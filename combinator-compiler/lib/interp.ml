open Error

type value =
  | Int of int
  | Ptr of { root : int; offset : int }

let normalize width n =
  if width >= 63 then n
  else
    let m = n land ((1 lsl width) - 1) in
    if m >= 1 lsl (width - 1) then m - (1 lsl width) else m

let unsigned width n = if width >= 63 then n else n land ((1 lsl width) - 1)

type memory = {
  cells : (int * int * Ir.ty, value option) Hashtbl.t;
  mutable roots : int;
}

let create_memory () = { cells = Hashtbl.create 64; roots = 0 }

let alloc program mem ty =
  let root = mem.roots in
  mem.roots <- root + 1;
  List.iter (fun (off, cty) -> Hashtbl.replace mem.cells (root, off, cty) None) (Ir.cells program ty);
  Ptr { root; offset = 0 }

let width_of = function Ir.Int w -> w | Ir.Ptr -> 64 | ty -> fail "unsupported type %s" (Ir.ty_to_string ty)

let compare (pred : Ir.cmp) w a b =
  let ua = unsigned w a and ub = unsigned w b in
  match pred with
  | Eq -> a = b | Ne -> a <> b
  | Slt -> a < b | Sle -> a <= b | Sgt -> a > b | Sge -> a >= b
  | Ult -> ua < ub | Ule -> ua <= ub | Ugt -> ua > ub | Uge -> ua >= ub

let binary (op : Ir.binop) w a b =
  normalize w (match op with
      | Add -> a + b | Sub -> a - b | Mul -> a * b
      | And -> a land b | Or -> a lor b | Xor -> a lxor b)

let budget = ref 0

let rec call program mem (f : Ir.func) (args : value list) ~depth : value option =
  if depth > 64 then fail "%s: call depth exceeded" f.name;
  let blocks = Lazy.force f.body in
  if Array.length blocks = 0 then fail "%s: external functions are unsupported" f.name;
  let find id = match Array.find_opt (fun (b : Ir.block) -> b.id = id) blocks with
    | Some b -> b | None -> fail "%s: missing branch target %d" f.name id in
  let params = List.combine (List.map fst f.params) args in
  let locals = Hashtbl.create 32 in
  let own = ref [] in
  let value (v : Ir.operand) =
    match v with
    | Const { width; value } -> Int (normalize width value)
    | Zero -> Int 0
    | Param { name; _ } -> List.assoc name params
    | Local { id; _ } -> (match Hashtbl.find_opt locals id with
        | Some v -> v | None -> fail "%s: undefined value %d" f.name id)
  in
  let int v = match value v with Int n -> n | Ptr _ -> fail "%s: pointer used as an integer" f.name in
  let cell ptr ty =
    match value ptr with
    | Ptr { root; offset } ->
      let key = (root, offset, ty) in
      if not (Hashtbl.mem mem.cells key) then
        fail "%s: out-of-bounds, uninitialized, or reinterpreted %s memory access" f.name (Ir.ty_to_string ty);
      key
    | Int _ -> fail "%s: memory access requires a fixed allocation" f.name
  in
  let rec exec (block : Ir.block) pred =
    incr budget;
    if !budget > 10_000_000 then fail "execution budget exceeded";
    let phis = Array.to_list block.instrs |> List.filter_map (function
        | Ir.Phi { dest; incoming; _ } ->
          (match List.find_opt (fun (_, p) -> Some p = pred) incoming with
           | Some (v, _) -> Some (dest, value v)
           | None -> fail "%s: invalid phi" f.name)
        | _ -> None) in
    List.iter (fun (d, v) -> Hashtbl.replace locals d v) phis;
    Array.iter (fun (ins : Ir.instr) ->
        let set d v = Hashtbl.replace locals d v in
        match ins with
        | Phi _ -> ()
        | Alloca { dest; ty } ->
          let p = alloc program mem ty in
          (match p with Ptr { root; _ } -> own := root :: !own | Int _ -> ());
          set dest p
        | Store { ty; value = v; ptr } -> Hashtbl.replace mem.cells (cell ptr ty) (Some (value v))
        | Load { dest; ty; ptr } ->
          (match Hashtbl.find mem.cells (cell ptr ty) with
           | Some v -> set dest v
           | None -> fail "%s: out-of-bounds, uninitialized, or reinterpreted %s memory access" f.name
                       (Ir.ty_to_string ty))
        | Bin { dest; op; width; a; b } -> set dest (Int (binary op width (int a) (int b)))
        | Cmp { dest; pred; width; a; b } ->
          set dest (Int (if compare pred width (int a) (int b) then -1 else 0))
        | Cast { dest; op; value = v; dst; src } ->
          (match value v, dst with
           | (Ptr _ as p), Ir.Ptr -> set dest p
           | Ptr _, _ -> fail "%s: pointer casts are unsupported" f.name
           | Int n, Ir.Int w ->
             let n = if op = Zext then unsigned (width_of src) n else n in
             set dest (Int (normalize w n))
           | Int _, _ -> fail "%s: unsupported cast" f.name)
        | Select { dest; cond; a; b } -> set dest (if int cond <> 0 then value a else value b)
        | Gep { dest; ty; base; indices } ->
          (match value base with
           | Ptr { root; offset } ->
             let _, offset, _ = List.fold_left (fun (ty, offset, i) index ->
                 let ty = if i = 0 then ty else match ty with
                     | Ir.Array (_, e) -> e
                     | _ -> fail "%s: unsupported GEP type %s" f.name (Ir.ty_to_string ty) in
                 let size, _ = Ir.layout program ty in
                 (ty, offset + int index * size, i + 1)) (ty, offset, 0) indices in
             set dest (Ptr { root; offset })
           | Int _ -> fail "%s: invalid GEP base" f.name)
        | Call { dest; callee; args; _ } ->
          let g = match Ir.find_func program callee with
            | Some g -> g | None -> fail "%s: external call %s unsupported" f.name callee in
          let r = call program mem g (List.map (fun (_, a) -> value a) args) ~depth:(depth + 1) in
          (match dest, r with
           | Some d, Some r -> set d r
           | Some _, None -> fail "%s: call to %s has no result" f.name callee
           | None, _ -> ()))
      block.instrs;
    match block.term with
    | Ret v -> Option.map value v
    | Br t -> exec (find t) (Some block.id)
    | Condbr (c, a, b) -> exec (find (if int c <> 0 then a else b)) (Some block.id)
    | Switch { value = v; cases; default; width } ->
      let x = normalize width (int v) in
      let target = match List.find_opt (fun (c, _) -> normalize width c = x) cases with
        | Some (_, t) -> t | None -> default in
      exec (find target) (Some block.id)
  in
  let result = exec blocks.(0) None in
  Hashtbl.filter_map_inplace (fun (root, _, _) v -> if List.mem root !own then None else Some v) mem.cells;
  result

let run program (f : Ir.func) args =
  budget := 0;
  call program (create_memory ()) f args ~depth:0
