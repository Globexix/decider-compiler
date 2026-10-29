open Error

type value =
  | Bits of Bitvec.t
  | Ptr of { root : int; offset : Bitvec.t }

module IM = Map.Make (Int)

type memory = value option IM.t

type cell = { root : int; offset : int; ty : Ir.ty }

type t = {
  program : Ir.program;
  valid : Bdd.t;
  cell_ids : (cell, int) Hashtbl.t;
  mutable cells : cell array;
  root_cells : (int, (int * Ir.ty * int) list) Hashtbl.t;
  root_names : (int, string) Hashtbl.t;
  memo : (string * Bitvec.t list * Bdd.t, Bitvec.t option) Hashtbl.t;
  mutable calls : int;
}

let create program ~valid =
  { program; valid; cell_ids = Hashtbl.create 64; cells = [||]; root_cells = Hashtbl.create 16;
    root_names = Hashtbl.create 16; memo = Hashtbl.create 16; calls = 0 }

let new_root t name =
  let id = Hashtbl.length t.root_names in
  Hashtbl.replace t.root_names id name;
  id

let cell t root offset ty =
  let key = { root; offset; ty } in
  match Hashtbl.find_opt t.cell_ids key with
  | Some id -> id
  | None ->
    let id = Hashtbl.length t.cell_ids in
    Hashtbl.replace t.cell_ids key id;
    if id >= Array.length t.cells then begin
      let cells = Array.make (max 16 (2 * id)) key in
      Array.blit t.cells 0 cells 0 (Array.length t.cells);
      t.cells <- cells
    end;
    t.cells.(id) <- key;
    let others = try Hashtbl.find t.root_cells root with Not_found -> [] in
    Hashtbl.replace t.root_cells root ((offset, ty, id) :: others);
    id

let cell_info t id = t.cells.(id)

let bits_of_cell_ty = function
  | Ir.Int w -> w
  | Ir.Ptr -> 64
  | ty -> fail "unsupported aggregate scalar type %s" (Ir.ty_to_string ty)

let value_equal a b =
  match a, b with
  | Bits x, Bits y -> Bitvec.equal x y
  | Ptr p, Ptr q -> p.root = q.root && Bitvec.equal p.offset q.offset
  | _ -> false

let select guard a b =
  if guard = Bdd.one then a
  else if guard = Bdd.zero then b
  else if value_equal a b then a
  else match a, b with
    | Bits x, Bits y -> Bits (Bitvec.select guard x y)
    | Ptr p, Ptr q when p.root = q.root -> Ptr { root = p.root; offset = Bitvec.select guard p.offset q.offset }
    | _ -> fail "conditional pointers must refer to the same fixed allocation"

let select_cell guard a b =
  match a, b with
  | Some x, Some y -> Some (select guard x y)
  | _ when guard = Bdd.one -> a
  | _ when guard = Bdd.zero -> b
  | _ -> None

let merge_memory = function
  | [] -> IM.empty
  | (_, first) :: rest ->
    List.fold_left (fun acc (guard, mem) ->
        if acc == mem then acc
        else IM.union (fun _ old fresh -> Some (if old == fresh then old else select_cell guard fresh old)) acc mem)
      first rest

let bits name = function
  | Bits b -> b
  | Ptr _ -> fail ~at:(Func name) "pointer used as an integer"

let rec run t (f : Ir.func) (args : value list) (mem : memory) ~guard ~stack : value option * memory =
  let name = f.name in
  t.calls <- t.calls + 1;
  if t.calls > 100_000 then fail "symbolic function execution budget exceeded";
  if List.mem name stack then fail ~at:(Func name) "recursive calls are unsupported";
  if List.length args <> List.length f.params then fail ~at:(Func name) "wrong argument count";
  let order = Ir.topological_order f in
  let params = List.combine (List.map fst f.params) args in
  let locals = Hashtbl.create 64 in
  let incoming : (int, (int option * Bdd.t * memory) list) Hashtbl.t = Hashtbl.create 16 in
  let send target pred g m =
    if g <> Bdd.zero then
      Hashtbl.replace incoming target ((pred, g, m) :: (try Hashtbl.find incoming target with Not_found -> []))
  in
  let exits = ref [] in
  let stack = name :: stack in
  Hashtbl.replace incoming (List.hd order).Ir.id [ (None, guard, mem) ];
  let root_prefix = String.concat "/" (List.rev stack) in
  List.iter (fun (block : Ir.block) ->
      let packets =
        List.filter (fun (_, g, _) -> Bdd.and_ t.valid g <> Bdd.zero)
          (List.rev (try Hashtbl.find incoming block.id with Not_found -> []))
      in
      if packets <> [] then begin
        let active = Bdd.disj (List.map (fun (_, g, _) -> g) packets) in
        let mem = ref (merge_memory (List.map (fun (_, g, m) -> (g, m)) packets)) in
        let value (v : Ir.operand) =
          match v with
          | Const { width; value } -> Bits (Bitvec.const ~width value)
          | Zero -> Bits (Bitvec.const ~width:64 0)
          | Param { name = p; _ } ->
            (match List.assoc_opt p params with Some v -> v | None -> fail ~at:(Func name) "unknown parameter %s" p)
          | Local { id; _ } ->
            (match Hashtbl.find_opt locals id with Some v -> v | None -> fail ~at:(Func name) "undefined value %d" id)
        in
        let set dest v = Hashtbl.replace locals dest v in
        let access ptr ty stored =
          match ptr with
          | Bits _ -> fail ~at:(Func name) "memory access requires a fixed allocation"
          | Ptr { root; offset } ->
            let candidates = List.filter_map (fun (off, cty, id) ->
                if cty <> ty then None
                else match IM.find_opt id !mem with
                  | None -> None
                  | Some None when stored = None -> None
                  | Some contents ->
                    let hit = Bitvec.eq offset (Bitvec.const ~width:64 off) in
                    if Bdd.and_ t.valid (Bdd.and_ active hit) = Bdd.zero then None
                    else Some (id, hit, contents))
                (try Hashtbl.find t.root_cells root with Not_found -> [])
            in
            let covered = Bdd.disj (List.map (fun (_, hit, _) -> hit) candidates) in
            if Bdd.and_ t.valid (Bdd.and_ active (Bdd.not_ covered)) <> Bdd.zero || candidates = [] then
              fail ~at:(Func name) "out-of-bounds, uninitialized, or reinterpreted %s memory access; guard runtime indices"
                 (Ir.ty_to_string ty);
            match stored with
            | Some v ->
              List.iter (fun (id, hit, old) -> mem := IM.add id (select_cell hit (Some v) old) !mem) candidates;
              None
            | None ->
              let contents = List.map (fun (_, hit, c) -> (hit, Option.get c)) candidates in
              let _, first = List.hd contents in
              Some (List.fold_left (fun acc (hit, v) -> select hit v acc) first (List.tl contents))
        in
        Array.iter (function
            | Ir.Phi { dest; incoming = edges; _ } ->
              let result = List.fold_left (fun acc (pred, g, _) ->
                  let options = List.filter (fun (_, p) -> Some p = pred) edges in
                  if List.length options <> 1 then fail ~at:(Func name) "invalid phi";
                  let v = value (fst (List.hd options)) in
                  match acc with None -> Some v | Some old -> Some (select g v old)) None packets in
              set dest (Option.get result)
            | _ -> ()) block.instrs;
        Array.iter (fun (ins : Ir.instr) ->
            match ins with
            | Phi _ -> ()
            | Alloca { dest; ty } ->
              let root = new_root t (Printf.sprintf "%s:%d" root_prefix dest) in
              set dest (Ptr { root; offset = Bitvec.const ~width:64 0 });
              List.iter (fun (off, cty) -> mem := IM.add (cell t root off cty) None !mem) (Ir.cells t.program ty)
            | Store { ty; value = v; ptr } ->
              let stored = value v in
              (match value ptr with
               | Ptr { root; offset } as p ->
                 (match Bitvec.to_const offset with
                  | Some off when (match Hashtbl.find_opt t.cell_ids { root; offset = off; ty } with
                      | Some id -> IM.mem id !mem | None -> false) ->
                    mem := IM.add (cell t root off ty) (Some stored) !mem
                  | _ -> ignore (access p ty (Some stored)))
               | Bits _ -> fail ~at:(Func name) "invalid store address")
            | Load { dest; ty; ptr } -> set dest (Option.get (access (value ptr) ty None))
            | Gep { dest; ty; base; indices } ->
              (match value base with
               | Ptr { root; offset } ->
                 let step (ty, offset) i index =
                   let ty = if i = 0 then ty else match ty with
                       | Ir.Array (_, elem) -> elem
                       | _ -> fail ~at:(Func name) "unsupported GEP type %s" (Ir.ty_to_string ty) in
                   let size, _ = Ir.layout t.program ty in
                   let n = Bitvec.resize ~signed:true 64 (bits name (value index)) in
                   (ty, Bitvec.add offset (Bitvec.mul n (Bitvec.const ~width:64 size)))
                 in
                 let _, offset = List.fold_left (fun (acc, i) index -> (step acc i index, i + 1)) ((ty, offset), 0) indices
                                 |> fst in
                 set dest (Ptr { root; offset })
               | Bits _ -> fail ~at:(Func name) "invalid GEP base")
            | Bin { dest; op; a; b; _ } -> set dest (Bits (Bitvec.binary op (bits name (value a)) (bits name (value b))))
            | Cmp { dest; pred; a; b; _ } ->
              (match value a, value b with
               | Bits x, Bits y -> set dest (Bits [| Bitvec.compare pred x y |])
               | _ -> fail ~at:(Func name) "pointer comparisons are unsupported")
            | Cast { dest; op; value = v; dst; _ } ->
              (match value v, dst with
               | (Ptr _ as p), Ir.Ptr when op = Bitcast -> set dest p
               | Ptr _, _ -> fail ~at:(Func name) "pointer casts are unsupported"
               | Bits x, Ir.Int w -> set dest (Bits (Bitvec.resize ~signed:(op = Sext) w x))
               | Bits _, _ -> fail ~at:(Func name) "unsupported cast")
            | Select { dest; cond; a; b } ->
              let c = bits name (value cond) in
              set dest (select c.(0) (value a) (value b))
            | Call { dest; callee; args = call_args; _ } ->
              let target = match Ir.find_func t.program callee with
                | Some g -> g | None -> fail ~at:(Func name) "external call %s unsupported" callee in
              let actuals = List.map (fun (_, a) -> value a) call_args in
              let result =
                if List.exists (function Ptr _ -> true | Bits _ -> false) actuals then begin
                  let result, changed = run t target actuals !mem ~guard:active ~stack in
                  mem := IM.filter (fun id _ -> IM.mem id !mem) changed;
                  result
                end else begin
                  let key = (callee, List.map (bits name) actuals, active) in
                  match Hashtbl.find_opt t.memo key with
                  | Some r -> Option.map (fun b -> Bits b) r
                  | None ->
                    let result, _ = run t target actuals IM.empty ~guard:active ~stack in
                    Hashtbl.replace t.memo key (Option.map (bits name) result);
                    result
                end
              in
              (match dest, result with
               | Some d, Some r -> set d r
               | Some _, None -> fail ~at:(Func name) "call to %s has no result" callee
               | None, _ -> ()))
          block.instrs;
        match block.term with
        | Ret v -> exits := (active, Option.map value v, !mem) :: !exits
        | Br target -> send target (Some block.id) active !mem
        | Condbr (c, a, b) ->
          let c = (bits name (value c)).(0) in
          send a (Some block.id) (Bdd.and_ active c) !mem;
          send b (Some block.id) (Bdd.and_ active (Bdd.not_ c)) !mem
        | Switch { width; value = v; cases; default } ->
          let x = bits name (value v) in
          let rest = List.fold_left (fun rest (case, target) ->
              let hit = Bitvec.eq x (Bitvec.const ~width case) in
              send target (Some block.id) (Bdd.and_ rest hit) !mem;
              Bdd.and_ rest (Bdd.not_ hit)) active cases in
          send default (Some block.id) rest !mem
      end) order;
  let exits = List.rev !exits in
  if exits = [] then fail ~at:(Func name) "no reachable return";
  let result = List.fold_left (fun acc (g, v, _) ->
      match acc, v with
      | None, v -> v
      | Some old, Some v -> Some (select g v old)
      | Some _, None -> fail ~at:(Func name) "inconsistent return values") None exits in
  (result, merge_memory (List.map (fun (g, _, m) -> (g, m)) exits))
