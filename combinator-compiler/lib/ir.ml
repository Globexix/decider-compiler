open Error

type ty =
  | Int of int
  | Ptr
  | Array of int * ty
  | Struct of string
  | Void

type operand =
  | Const of { width : int; value : int }
  | Local of { ty : ty; id : int }
  | Param of { ty : ty; name : string }
  | Zero

type binop = Add | Sub | Mul | And | Or | Xor
type cmp = Eq | Ne | Slt | Sle | Sgt | Sge | Ult | Ule | Ugt | Uge
type cast = Zext | Sext | Trunc | Bitcast

type instr =
  | Alloca of { dest : int; ty : ty }
  | Load of { dest : int; ty : ty; ptr : operand }
  | Store of { ty : ty; value : operand; ptr : operand }
  | Bin of { dest : int; op : binop; width : int; a : operand; b : operand }
  | Cmp of { dest : int; pred : cmp; width : int; a : operand; b : operand }
  | Cast of { dest : int; op : cast; src : ty; value : operand; dst : ty }
  | Select of { dest : int; cond : operand; a : operand; b : operand }
  | Phi of { dest : int; ty : ty; incoming : (operand * int) list }
  | Gep of { dest : int; ty : ty; base : operand; indices : operand list }
  | Call of { dest : int option; ret : ty; callee : string; args : (ty * operand) list }

type term =
  | Ret of operand option
  | Br of int
  | Condbr of operand * int * int
  | Switch of { width : int; value : operand; cases : (int * int) list; default : int }

type block = { id : int; instrs : instr array; term : term }

type func = {
  name : string;
  params : (string * ty) list;
  ret : ty;
  body : block array Lazy.t;
}

type struct_def = { fields : ty list; tail_padding : int }

type program = {
  json : Yojson.Safe.t;
  structs : (string * struct_def) list;
  funcs : func list;
  has_globals : bool;
}

let rec ty_to_string = function
  | Int w -> "i" ^ string_of_int w
  | Ptr -> "ptr"
  | Void -> "void"
  | Struct name -> "%struct." ^ name
  | Array (n, t) -> Printf.sprintf "[%d x %s]" n (ty_to_string t)

let rec parse_ty s =
  let n = String.length s in
  match s with
  | "i1" -> Int 1 | "i8" -> Int 8 | "i16" -> Int 16 | "i32" -> Int 32 | "i64" -> Int 64
  | "ptr" -> Ptr
  | "void" -> Void
  | _ when n > 8 && String.sub s 0 8 = "%struct." -> Struct (String.sub s 8 (n - 8))
  | _ when n > 2 && s.[0] = '[' && s.[n - 1] = ']' ->
    (match String.index_opt s 'x' with
     | Some i when i > 1 && s.[i - 1] = ' ' && i + 1 < n && s.[i + 1] = ' ' ->
       let count = String.trim (String.sub s 1 (i - 2)) in
       (match int_of_string_opt count with
        | Some c when c >= 0 -> Array (c, parse_ty (String.sub s (i + 2) (n - i - 3)))
        | _ -> fail "unsupported type %S" s)
     | _ -> fail "unsupported type %S" s)
  | _ -> fail "unsupported type %S" s

let scalar_width = function Int w -> w | ty -> fail "expected an integer type, got %s" (ty_to_string ty)

module J = struct
  let str = function `String s -> s | _ -> fail "malformed IR: expected a string"
  let int = function `Int i -> i | `Intlit s -> fail "IR constant %s is out of range" s | _ -> fail "malformed IR: expected an integer"
  let list = function `List l -> l | _ -> fail "malformed IR: expected a list"
  let field name = function
    | `Assoc fields -> (try List.assoc name fields with Not_found -> fail "malformed IR: missing %S" name)
    | _ -> fail "malformed IR: expected an object"
  let field_opt name = function `Assoc fields -> List.assoc_opt name fields | _ -> None
end

let operand (v : Yojson.Safe.t) =
  match v with
  | `List [ `String "zero" ] -> Zero
  | `List [ `String "const"; ty; n ] -> Const { width = scalar_width (parse_ty (J.str ty)); value = J.int n }
  | `List [ `String "local"; ty; n ] -> Local { ty = parse_ty (J.str ty); id = J.int n }
  | `List [ `String "param"; ty; name ] -> Param { ty = parse_ty (J.str ty); name = J.str name }
  | `List (`String kind :: _) -> fail "unsupported value %s" kind
  | _ -> fail "malformed scalar value"

let binop = function
  | "add" -> Add | "sub" -> Sub | "mul" -> Mul | "and" -> And | "or" -> Or | "xor" -> Xor
  | op -> fail "unsupported binary operation %s" op

let cmp = function
  | "eq" -> Eq | "ne" -> Ne | "slt" -> Slt | "sle" -> Sle | "sgt" -> Sgt | "sge" -> Sge
  | "ult" -> Ult | "ule" -> Ule | "ugt" -> Ugt | "uge" -> Uge
  | p -> fail "unsupported comparison %s" p

let cast = function
  | "zext" -> Zext | "sext" -> Sext | "trunc" -> Trunc | "bitcast" -> Bitcast
  | c -> fail "unsupported cast %s" c

let instr (v : Yojson.Safe.t) =
  let ty x = parse_ty (J.str x) in
  match J.list v with
  | [ `String "alloca"; dest; t; _ ] -> Alloca { dest = J.int dest; ty = ty t }
  | [ `String "load"; dest; t; ptr; _ ] -> Load { dest = J.int dest; ty = ty t; ptr = operand ptr }
  | [ `String "store"; t; value; ptr; _ ] -> Store { ty = ty t; value = operand value; ptr = operand ptr }
  | [ `String "bin"; dest; op; t; a; b ] ->
    Bin { dest = J.int dest; op = binop (J.str op); width = scalar_width (ty t); a = operand a; b = operand b }
  | [ `String "cmp"; dest; p; t; a; b ] ->
    Cmp { dest = J.int dest; pred = cmp (J.str p); width = scalar_width (ty t); a = operand a; b = operand b }
  | [ `String "cast"; dest; op; src; value; dst ] ->
    Cast { dest = J.int dest; op = cast (J.str op); src = ty src; value = operand value; dst = ty dst }
  | [ `String "select"; dest; c; a; b ] -> Select { dest = J.int dest; cond = operand c; a = operand a; b = operand b }
  | [ `String "phi"; dest; t; incoming ] ->
    let edge e = match J.list e with [ v; pred ] -> (operand v, J.int pred) | _ -> fail "malformed phi" in
    Phi { dest = J.int dest; ty = ty t; incoming = List.map edge (J.list incoming) }
  | [ `String "gep"; dest; t; base; indices ] ->
    Gep { dest = J.int dest; ty = ty t; base = operand base; indices = List.map operand (J.list indices) }
  | [ `String "call"; dest; _; ret; callee; args ] ->
    let dest = match dest with `Null -> None | d -> Some (J.int d) in
    let arg a = match J.list a with [ t; _; v ] -> (ty t, operand v) | _ -> fail "malformed call argument" in
    Call { dest; ret = ty ret; callee = J.str callee; args = List.map arg (J.list args) }
  | `String op :: _ -> fail "unsupported instruction %s" op
  | _ -> fail "malformed instruction"

let term (v : Yojson.Safe.t) =
  match J.list v with
  | [ `String "ret" ] | [ `String "ret"; _ ] -> Ret None
  | [ `String "ret"; _; value ] -> Ret (Some (operand value))
  | [ `String "br"; target ] -> Br (J.int target)
  | [ `String "condbr"; c; t; f ] -> Condbr (operand c, J.int t, J.int f)
  | [ `String "switch"; t; value; cases; default ] ->
    let case c = match J.list c with [ k; target ] -> (J.int k, J.int target) | _ -> fail "malformed switch" in
    Switch { width = scalar_width (parse_ty (J.str t)); value = operand value;
             cases = List.map case (J.list cases); default = J.int default }
  | `String op :: _ -> fail "unsupported terminator %s" op
  | _ -> fail "malformed terminator"

let block v =
  { id = J.int (J.field "id" v);
    instrs = Array.of_list (List.map instr (J.list (J.field "instrs" v)));
    term = term (J.field "term" v) }

let func v =
  let name = J.str (J.field "name" v) in
  let params =
    List.map (fun p -> (J.str (J.field "name" p), parse_ty (J.str (J.field "ty" p)))) (J.list (J.field "params" v))
  in
  let body = lazy (locate (Func name) (fun () ->
      Array.of_list (List.map block (J.list (J.field "blocks" v))))) in
  { name; params; ret = parse_ty (J.str (J.field "ret" v)); body }

let of_json (json : Yojson.Safe.t) =
  check (J.field_opt "format" json = Some (`String "fas-ir-json") && J.field_opt "version" json = Some (`Int 2))
    "expected fas-ir-json version 2";
  let structs =
    match J.field_opt "structs" json with
    | None -> []
    | Some s ->
      List.map (fun s ->
          (J.str (J.field "name" s),
           { fields = List.map (fun f -> parse_ty (J.str f)) (J.list (J.field "fields" s));
             tail_padding = (match J.field_opt "tail_padding" s with Some n -> J.int n | None -> 0) }))
        (J.list s)
  in
  let has_globals = match J.field_opt "globals" json with
    | None | Some `Null | Some (`List []) | Some (`Assoc []) -> false
    | Some _ -> true
  in
  { json; structs; funcs = List.map func (J.list (J.field "funcs" json)); has_globals }

let find_func program name = List.find_opt (fun f -> f.name = name) program.funcs

let rec layout program ty =
  match ty with
  | Ptr -> (8, 8)
  | Int w -> let b = max 1 (w / 8) in (b, b)
  | Array (n, t) -> let size, align = layout program t in (n * size, align)
  | Struct name ->
    let def = match List.assoc_opt name program.structs with
      | Some d -> d | None -> fail "unsupported aggregate type %%struct.%s" name in
    let offset, align = List.fold_left (fun (offset, align) field ->
        let size, a = layout program field in
        ((offset + a - 1) / a * a + size, max align a)) (0, 1) def.fields in
    (offset + def.tail_padding, align)
  | Void -> fail "void has no layout"

let rec cells program ?(offset = 0) ty =
  match ty with
  | Ptr | Int _ -> [ (offset, ty) ]
  | Array (n, t) ->
    let size, _ = layout program t in
    List.concat (List.init n (fun i -> cells program ~offset:(offset + i * size) t))
  | Struct name ->
    let def = List.assoc name program.structs in
    let _, acc = List.fold_left (fun (pos, acc) field ->
        let size, align = layout program field in
        let pos = (pos + align - 1) / align * align in
        (pos + size, acc @ cells program ~offset:pos field)) (offset, []) def.fields in
    acc
  | Void -> []

let successors = function
  | Ret _ -> []
  | Br t -> [ t ]
  | Condbr (_, t, f) -> [ t; f ]
  | Switch { cases; default; _ } -> List.map snd cases @ [ default ]

let topological_order f =
  let blocks = Lazy.force f.body in
  check (Array.length blocks > 0) (f.name ^ ": external functions are unsupported");
  let index = Hashtbl.create (Array.length blocks) in
  Array.iteri (fun i b ->
      if Hashtbl.mem index b.id then fail "%s: duplicate block ID" f.name;
      Hashtbl.replace index b.id i) blocks;
  let state = Array.make (Array.length blocks) `New in
  let order = ref [] in
  let rec visit id =
    match Hashtbl.find_opt index id with
    | None -> fail "%s: missing branch target %d" f.name id
    | Some i ->
      match state.(i) with
      | `Done -> ()
      | `Active -> fail "%s: loops are unsupported; express repeated work as state updates" f.name
      | `New ->
        state.(i) <- `Active;
        List.iter visit (successors blocks.(i).term);
        state.(i) <- `Done;
        order := blocks.(i) :: !order
  in
  visit blocks.(0).id;
  Array.iter (fun b -> visit b.id) blocks;
  let reachable = Hashtbl.create 16 in
  let rec mark id =
    if not (Hashtbl.mem reachable id) then begin
      Hashtbl.replace reachable id ();
      List.iter mark (successors blocks.(Hashtbl.find index id).term)
    end in
  mark blocks.(0).id;
  List.filter (fun b -> Hashtbl.mem reachable b.id) !order
