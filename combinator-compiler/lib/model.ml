open Error

type domain = {
  name : string;
  lo : int;
  size : int;
  bits : int list;
  input : bool;
}

type t = {
  spec : Spec.t;
  program : Ir.program;
  domains : domain list;
  values : (string, Bitvec.t) Hashtbl.t;
  valid : Bdd.t;
  next : (string, Bitvec.t) Hashtbl.t;
}

let domain t name = List.find (fun d -> d.name = name) t.domains
let value t name = Hashtbl.find t.values name
let next t name = Hashtbl.find t.next name
let values d = List.init d.size (fun i -> d.lo + i)

let bit_length n = let rec go k = if n lsr k = 0 then k else go (k + 1) in go 0

let assignment d v = List.mapi (fun i var -> (var, ((v - d.lo) lsr i) land 1)) d.bits

let is_value d v =
  Bdd.conj (List.map (fun (var, bit) -> if bit = 1 then Bdd.ithvar var else Bdd.not_ (Bdd.ithvar var)) (assignment d v))

let flag t state v = Bitvec.eq (next t state) (Bitvec.const v)

let owner state = match String.index_opt state '[' with Some i -> String.sub state 0 i | None -> state

let width_of = function Ir.Int w -> w | ty -> fail "unsupported parameter type %s" (Ir.ty_to_string ty)

let out_of_bounds t (s : Spec.state) func v ~within outside =
  let bits = match Bdd.any_sat outside with Some a -> a | None -> [] in
  let bit var = List.assoc_opt var bits = Some 1 in
  let decode d = d.lo + List.fold_left (fun acc var -> 2 * acc + if bit var then 1 else 0) 0 (List.rev d.bits) in
  let result = Array.fold_right (fun b acc -> 2 * acc + if Bdd.eval b bit then 1 else 0) v 0 in
  let result = if result >= 0x8000_0000 then result - 0x1_0000_0000 else result in
  let support = Bdd.support within in
  let shown = List.filter (fun d -> List.exists (fun var -> List.mem var support) d.bits) t.domains in
  let show d =
    let x = decode d in
    if d.input then Printf.sprintf "%s = %b" d.name (x = 1) else Printf.sprintf "%s = %d" d.name x in
  let when_ = match shown with
    | [] -> "it does so for every state and input"
    | _ -> "for example when " ^ String.concat ", " (List.map show shown) in
  fail ~at:(Func func)
    ~notes:[ (None, when_); (Some (Path [ "state"; s.name ]), Printf.sprintf "`%s` is declared as %d..%d here" s.name s.min s.max) ]
    ~help:[ "clamp the result, or widen the declared range" ]
    "%s" (if String.contains s.name '[' then
            Printf.sprintf "`%s` can set `%s` to %d, outside its range %d..%d" func s.name result s.min s.max
          else Printf.sprintf "`%s` can return %d for `%s`, outside its range %d..%d" func result s.name s.min s.max)

let create (spec : Spec.t) (program : Ir.program) =
  Bdd.reset ();
  let index = ref 0 in
  let make name lo size input =
    let n = bit_length (size - 1) in
    let bits = List.init n (fun i -> !index + i) in
    index := !index + n;
    { name; lo; size; bits; input } in
  let domains =
    List.map (fun (s : Spec.state) -> make s.name s.min (s.max - s.min + 1) false) spec.states
    @ List.map (fun (i : Spec.input) -> make i.input 0 2 true) spec.inputs in
  let values = Hashtbl.create 64 in
  List.iter (fun d ->
      let raw = Array.init 32 (fun i -> match List.nth_opt d.bits i with Some v -> Bdd.ithvar v | None -> Bdd.zero) in
      Hashtbl.replace values d.name (if d.lo = 0 then raw else Bitvec.add raw (Bitvec.const d.lo))) domains;
  let valid = Bdd.conj (List.map (fun d ->
      let raw = Bitvec.sub (Hashtbl.find values d.name) (Bitvec.const d.lo) in
      Bitvec.compare Ule raw (Bitvec.const (d.size - 1))) domains) in
  let t = { spec; program; domains; values; valid; next = Hashtbl.create 64 } in
  let exec = Symexec.create program ~valid in
  let boolean name = let d = domain t name in d.lo >= 0 && d.lo + d.size - 1 <= 1 in
  let roots = List.map (fun (g : Spec.group) ->
      let size, _ = Ir.layout program (Ir.Array (g.count, Ir.Struct g.struct_name)) in
      if size <> g.stride * g.count then fail ~at:(Path [ "arrays"; g.group ]) "array layout does not match struct `%s` in Fas IR" g.struct_name;
      (g.group, Symexec.new_root exec g.group)) spec.arrays in
  let addresses = Hashtbl.create 64 in
  let memory = List.fold_left (fun mem (g : Spec.group) ->
      let root = List.assoc g.group roots in
      let mem = ref mem in
      for i = 0 to g.count - 1 do
        List.iter (fun (f : Spec.field) ->
            let ty = match f.scalar with `I32 -> Ir.Int 32 | `Bool -> Ir.Int 8 in
            let flat = Printf.sprintf "%s[%d].%s" g.group i f.field in
            if not (Hashtbl.mem values flat) then fail ~at:(Path [ "arrays"; g.group ]) "array field `%s` has no state declaration" flat;
            let id = Symexec.cell exec root (i * g.stride + f.offset) ty in
            Hashtbl.replace addresses flat id;
            mem := Symexec.IM.add id (Some (Symexec.Bits (Bitvec.resize ~signed:false (width_of ty) (Hashtbl.find values flat)))) !mem)
          g.fields
      done;
      !mem) Symexec.IM.empty spec.arrays in
  let results = Hashtbl.create 16 in
  List.iter (fun (s : Spec.state) ->
      let u = List.find (fun (u : Spec.update) -> u.target = s.name) spec.updates in
      let f = match Ir.find_func program u.func with
        | Some f -> f | None -> fail ~at:(Path [ "updates"; s.name; "function" ]) ~help:(did_you_mean u.func (List.map (fun (f : Ir.func) -> f.name) program.funcs)) "no function `%s`" u.func in
      if List.length u.args <> List.length f.params then fail ~at:(Func u.func) ~notes:[ (Some (Path [ "updates"; s.name; "args" ]), Printf.sprintf "bound to %d arguments" (List.length u.args)) ] "`%s` takes %d parameters" u.func (List.length f.params);
      let args = List.map2 (fun arg (_, ty) ->
          match List.assoc_opt arg roots with
          | Some root ->
            if ty <> Ir.Ptr then fail ~at:(Func u.func) "parameter `%s` is bound to array `%s`, so its type must be `addr`" arg arg;
            Symexec.Ptr { root; offset = Bitvec.const ~width:64 0 }
          | None ->
            let w = width_of ty in
            if w = 1 && not (boolean arg) then fail ~at:(Func u.func) ~notes:[ (Some (Path [ "state"; arg ]), "declared here") ] "`%s` is a `bool` parameter, but `%s` is not a 0..1 state or an input" arg arg;
            Symexec.Bits (Bitvec.resize ~signed:false w (Hashtbl.find values arg))) u.args f.params in
      let key = (u.func, u.args) in
      let result, changed = match Hashtbl.find_opt results key with
        | Some r -> r
        | None ->
          let r = locate (Func u.func) (fun () -> Symexec.run exec f args memory ~guard:Bdd.one ~stack:[]) in
          Hashtbl.replace results key r; r in
      let array_state = Hashtbl.mem addresses s.name in
      let v = if array_state then begin
          if f.ret <> Ir.Void then fail ~at:(Func u.func) "`%s` updates an array, so it must return `void`" u.func;
          let mine = owner s.name in
          Symexec.IM.iter (fun id old ->
              let cell = Symexec.cell_info exec id in
              let group = Hashtbl.find exec.root_names cell.root in
              if group <> mine then
                match old, Symexec.IM.find_opt id changed with
                | Some (Symexec.Bits a), Some (Some (Symexec.Bits b)) ->
                  if Bdd.and_ valid (Bdd.not_ (Bitvec.eq a b)) <> Bdd.zero then
                    fail ~at:(Func u.func) "`%s` writes to array `%s`; an update may only modify its own array" u.func group
                | _ -> fail ~at:(Func u.func) "`%s` writes to array `%s`; an update may only modify its own array" u.func group) memory;
          match Symexec.IM.find_opt (Hashtbl.find addresses s.name) changed with
          | Some (Some (Symexec.Bits b)) -> b
          | _ -> fail ~at:(Func u.func) "`%s` can leave `%s` uninitialized" u.func s.name
        end else begin
          (match f.ret with Ir.Int (1 | 32) -> () | _ ->
             fail ~at:(Func u.func) "`%s` updates the scalar `%s`, so it must return `i32` or `bool`" u.func s.name);
          match result with
          | Some (Symexec.Bits b) -> b
          | _ -> fail ~at:(Func u.func) "`%s` does not always return a value" u.func
        end in
      let v = Bitvec.resize ~signed:false 32 v in
      let within = Bdd.and_ (Bitvec.compare Sge v (Bitvec.const s.min)) (Bitvec.compare Sle v (Bitvec.const s.max)) in
      let outside = Bdd.and_ valid (Bdd.not_ within) in
      if outside <> Bdd.zero then out_of_bounds t s u.func v ~within outside;
      Hashtbl.replace t.next s.name v) spec.states;
  t

let constant_assignment t constants =
  List.concat_map (fun (name, v) -> assignment (domain t name) v) constants

let array_constants t =
  let groups = List.map (fun (g : Spec.group) -> g.group) t.spec.arrays in
  let rec fix candidates =
    if candidates = [] then []
    else
      let bits = constant_assignment t candidates in
      let valid = Bdd.restrict t.valid bits in
      let survivors = List.filter (fun (name, v) ->
          Bdd.and_ valid (Bdd.restrict (Bdd.not_ (Bitvec.eq (next t name) (Bitvec.const v))) bits) = Bdd.zero) candidates in
      if List.length survivors = List.length candidates then candidates else fix survivors in
  fix (List.filter_map (fun (s : Spec.state) ->
      if List.mem (owner s.name) groups then Some (s.name, s.initial) else None) t.spec.states)
