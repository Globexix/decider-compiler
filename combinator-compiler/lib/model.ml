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
  latches : latch list;
}

(* A 0..1 state that holds last tick's value of a pure helper call. While [phase] is in [uses],
   none of the call's inputs changed on the last step, so the latch equals the call and updates
   read it instead of evaluating the call again. *)
and latch = {
  latch : string;
  callee : string;
  actuals : Symexec.value list;
  width : int;
  source : Bdd.t;
  phase : string;
  uses : int list;
  use : Bdd.t;
}

(* A call seen while evaluating the updates, with every place it runs: the update, the enclosing
   calls and the guard. *)
type call = {
  callee : string;
  actuals : Symexec.value list;
  mutable uses : use list;
}
and use = { site : string * string list; outer : call_key list; active : Bdd.t }
and call_key = string * (int * Bitvec.t) list

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

let call_key callee actuals : call_key =
  (callee, List.map (function Symexec.Bits b -> (-1, b) | Symexec.Ptr p -> (p.root, p.offset)) actuals)

(* A call can be latched only if it reads arrays through their roots, as the state left them. *)
let latchable (spec : Spec.t) memory (h : Symexec.hook) =
  let arrays = List.length spec.arrays in
  let pointers = List.filter_map (function Symexec.Ptr p -> Some p.root | Bits _ -> None) h.actuals in
  List.for_all (fun root -> root < arrays) pointers
  && (pointers = [] || Symexec.IM.for_all (fun id v ->
      match v, Symexec.IM.find_opt id h.mem with
      | Some a, Some (Some b) -> a == b || Symexec.value_equal a b
      | None, Some None -> true
      | _ -> false) memory)

(* [f] with every state variable replaced by its value after one step. *)
let after_step t f =
  let sub = Hashtbl.create 64 in
  List.iter (fun d ->
      if not d.input then begin
        let raw = Bitvec.sub (next t d.name) (Bitvec.const d.lo) in
        List.iteri (fun i var -> Hashtbl.replace sub var raw.(i)) d.bits
      end) t.domains;
  let memo = Hashtbl.create 64 in
  let rec go f =
    if f < 2 then f
    else match Hashtbl.find_opt memo f with
      | Some r -> r
      | None ->
        let v = Bdd.var f in
        let c = match Hashtbl.find_opt sub v with Some b -> b | None -> Bdd.ithvar v in
        let r = Bdd.ite c (go (Bdd.high f)) (go (Bdd.low f)) in
        Hashtbl.add memo f r; r in
  go f

(* States that step on their own, like a phase counter. *)
let clocks t =
  List.filter (fun d ->
      not d.input && d.size >= 2 && not (String.contains d.name '[')
      && Array.for_all (fun b -> List.for_all (fun v -> List.mem v d.bits) (Bdd.support b)) (next t d.name)) t.domains

(* Valid states, narrowed to the values each state can reach at each value of each clock. The set
   holds the initial state and is closed under a step, so it contains every reachable state. *)
let clock_box t =
  let initial = List.map (fun (s : Spec.state) -> (s.name, s.initial)) t.spec.states in
  let states = List.filter (fun d -> not d.input) t.domains in
  let equals = Hashtbl.create 64 in
  let next_is d v =
    match Hashtbl.find_opt equals (d.name, v) with
    | Some b -> b
    | None -> let b = Bitvec.eq (next t d.name) (Bitvec.const v) in Hashtbl.add equals (d.name, v) b; b in
  let tables = List.concat_map (fun c ->
      List.filter_map (fun d ->
          if d == c then None
          else Some (c, d, ref [ (List.assoc c.name initial, List.assoc d.name initial) ])) states) (clocks t) in
  let pairs (c, d, seen) = Bdd.disj (List.map (fun (p, v) -> Bdd.and_ (is_value c p) (is_value d v)) !seen) in
  let rec grow () =
    let box = Bdd.conj (t.valid :: List.map pairs tables) in
    let changed = ref false in
    List.iter (fun (c, d, seen) ->
        List.iter (fun p ->
            let into = Bdd.and_ box (next_is c p) in
            if into <> Bdd.zero then
              List.iter (fun v ->
                  if not (List.mem (p, v) !seen) && Bdd.and_ into (next_is d v) <> Bdd.zero then begin
                    seen := (p, v) :: !seen; changed := true
                  end) (values d)) (values c)) tables;
    if !changed then grow () else box in
  Bdd.stage := "finding the values each state can take at each phase";
  grow ()

let debug = Sys.getenv_opt "FAS_FACTORIO_LATCH_DEBUG" = Some "1"

(* Find the phase state whose latchable values, those only entered by steps that leave the call's
   result unchanged, cover the uses in the most updates; at least two. *)
let prove t ~reach exec memory (c : call) uses =
  match Ir.find_func t.program c.callee with
  | Some ({ ret = Ir.Int width; _ } as f) ->
    Bdd.stage := Printf.sprintf "looking for a phase to latch `%s`" c.callee;
    let result, changed = Symexec.run exec f c.actuals memory ~guard:Bdd.one ~stack:[] in
    let pure = Symexec.IM.for_all (fun id v ->
        match v, Symexec.IM.find_opt id changed with
        | Some a, Some (Some b) -> a == b || Symexec.value_equal a b
        | None, (Some None | None) -> true
        | _ -> false) memory in
    let inputs = List.concat_map (fun d -> if d.input then d.bits else []) t.domains in
    (match result with
     | Some (Symexec.Bits b) when pure && Array.for_all (( = ) Bdd.zero) (Array.sub b 1 (Array.length b - 1)) ->
       let source = b.(0) in
       if Bdd.is_const source || List.exists (fun v -> List.mem v inputs) (Bdd.support source) then
         (if debug then Printf.eprintf "latch %s: constant or reads an input\n%!" c.callee; None)
       else begin
         let reach = Lazy.force reach in
         let changes = Bdd.and_ reach (Bdd.xor source (after_step t source)) in
         let best = List.fold_left (fun best d ->
             if d.input || String.contains d.name '[' || d.size < 2 then best
             else
               let phases = List.filter (fun v -> Bdd.and_ changes (Bitvec.eq (next t d.name) (Bitvec.const v)) = Bdd.zero) (values d) in
               let use = Bdd.disj (List.map (is_value d) phases) in
               let sites = List.sort_uniq compare (List.filter_map (fun u ->
                   if Bdd.and_ reach (Bdd.and_ u.active (Bdd.not_ use)) = Bdd.zero then Some u.site else None) uses) in
               if debug then Printf.eprintf "latch %s: %s in {%s} covers %d of %d updates\n%!" c.callee d.name
                   (String.concat "," (List.map string_of_int phases)) (List.length sites) (List.length (List.sort_uniq compare (List.map (fun u -> u.site) uses)));
               match best with
               | Some (n, _) when n >= List.length sites -> best
               | _ -> Some (List.length sites, { latch = ""; callee = c.callee; actuals = c.actuals; width; source; phase = d.name; uses = phases; use }))
             None t.domains in
         match best with Some (n, l) when n >= 2 -> Some l | _ -> None
       end
     | _ -> if debug then Printf.eprintf "latch %s: not a pure bool\n%!" c.callee; None)
  | _ -> None

(* Outermost calls first; a call counts once per update that makes it outside an already chosen
   latch, and is worth a latch when at least two updates make it. *)
let choose_latches t exec memory calls =
  let depth (c : call) = List.fold_left (fun m u -> min m (List.length u.outer)) max_int c.uses in
  let free keys (c : call) = List.filter (fun u -> not (List.exists (fun k -> List.mem k keys) u.outer)) c.uses in
  let sites keys c = List.sort_uniq compare (List.map (fun u -> u.site) (free keys c)) in
  let order = List.sort (fun (_, a) (_, b) ->
      compare (depth a, - List.length (sites [] a)) (depth b, - List.length (sites [] b)))
      (Hashtbl.fold (fun k c acc -> (k, c) :: acc) calls []) in
  let taken = Hashtbl.create 16 and reach = lazy (clock_box t) in
  let name callee =
    let used n = List.exists (fun d -> d.name = n) t.domains || Hashtbl.mem taken n in
    let base = "latch_" ^ callee in
    let rec pick i = let n = if i = 1 then base else Printf.sprintf "%s%d" base i in if used n then pick (i + 1) else n in
    pick 1 in
  let chosen = List.fold_left (fun chosen (key, c) ->
      if List.length chosen >= 16 || List.length (sites (List.map fst chosen) c) < 2 then chosen
      else match prove t ~reach exec memory c (free (List.map fst chosen) c) with
        | Some l -> let n = name c.callee in Hashtbl.replace taken n (); (key, { l with latch = n }) :: chosen
        | None -> chosen) [] order in
  List.rev_map snd chosen


let evaluate t ~states ~hook ~site =
  let spec = t.spec and program = t.program and values = t.values in
  let exec = Symexec.create program ~valid:t.valid in
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
  exec.hook <- Option.map (fun h -> h memory) hook;
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
      Bdd.stage := Printf.sprintf "evaluating `%s`, the update for `%s`" u.func s.name;
      site := (u.func, u.args);
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
                  if Bdd.and_ t.valid (Bdd.not_ (Bitvec.eq a b)) <> Bdd.zero then
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
      Bdd.stage := Printf.sprintf "checking that `%s` keeps `%s` in range" u.func s.name;
      let within = Bdd.and_ (Bitvec.compare Sge v (Bitvec.const s.min)) (Bitvec.compare Sle v (Bitvec.const s.max)) in
      let outside = Bdd.and_ t.valid (Bdd.not_ within) in
      if outside <> Bdd.zero then out_of_bounds t s u.func v ~within outside;
      Hashtbl.replace t.next s.name v) states;
  (exec, memory)

(* Add the latch states, assume their invariant, and evaluate the updates again with latched calls
   reading the latch. *)
let with_latches t latches ~site =
  let index = ref (1 + List.fold_left (fun m d -> List.fold_left max m d.bits) (-1) t.domains) in
  let added = List.map (fun l -> let v = !index in incr index; ({ name = l.latch; lo = 0; size = 2; bits = [ v ]; input = false }, l)) latches in
  let values = Hashtbl.copy t.values in
  List.iter (fun (d, _) -> Hashtbl.replace values d.name (Bitvec.resize ~signed:false 32 [| Bdd.ithvar (List.hd d.bits) |])) added;
  let initial_bits = List.concat_map (fun (s : Spec.state) -> assignment (domain t s.name) s.initial) t.spec.states in
  let initial l = if Bdd.eval l.source (fun v -> List.assoc_opt v initial_bits = Some 1) then 1 else 0 in
  let held (d, l) = Bdd.imp l.use (Bdd.xnor (Bdd.ithvar (List.hd d.bits)) l.source) in
  let spec = { t.spec with states = t.spec.states @ List.map (fun (d, l) -> { Spec.name = d.name; min = 0; max = 1; initial = initial l }) added } in
  let latched = { t with spec; domains = t.domains @ List.map fst added; values; next = Hashtbl.create 64; latches;
                         valid = Bdd.conj (t.valid :: List.map held added) } in
  let intercept memory (h : Symexec.hook) =
    let key = call_key h.callee h.actuals in
    match List.find_opt (fun (_, (l : latch)) -> call_key l.callee l.actuals = key) added with
    | Some (d, l) when latchable t.spec memory h ->
      let value = Symexec.Bits (Bitvec.resize ~signed:false l.width (Hashtbl.find values d.name)) in
      if Bdd.and_ latched.valid (Bdd.and_ h.active (Bdd.not_ l.use)) = Bdd.zero then Some value
      else Option.map (fun r -> Symexec.select l.use value r) (h.real ())
    | _ -> h.real () in
  ignore (evaluate latched ~states:t.spec.states ~hook:(Some intercept) ~site);
  List.iter (fun (d, l) -> Hashtbl.replace latched.next d.name (Bitvec.resize ~signed:false 32 [| l.source |])) added;
  if Sys.getenv_opt "FAS_FACTORIO_CHECK" = Some "1" then
    List.iter (fun (s : Spec.state) ->
        if Bdd.and_ latched.valid (Bdd.not_ (Bitvec.eq (next t s.name) (next latched s.name))) <> Bdd.zero then
          failwith (Printf.sprintf "internal: latching changed the update for %s" s.name)) t.spec.states;
  (* The invariant only serves the range checks above: as part of the care set it slows planning
     several times over for a few percent fewer conditions. *)
  { latched with valid = t.valid }


let create ?(latch = false) (spec : Spec.t) (program : Ir.program) =
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
  let t = { spec; program; domains; values; valid; next = Hashtbl.create 64; latches = [] } in
  let calls = Hashtbl.create 64 and site = ref ("", []) and enclosing = ref [] in
  let record memory (h : Symexec.hook) =
    if not (latchable spec memory h) then h.real ()
    else begin
      let key = call_key h.callee h.actuals and outer = !enclosing in
      enclosing := key :: outer;
      let r = Fun.protect ~finally:(fun () -> enclosing := outer) h.real in
      let c = match Hashtbl.find_opt calls key with
        | Some c -> c
        | None -> let c = { callee = h.callee; actuals = h.actuals; uses = [] } in Hashtbl.add calls key c; c in
      c.uses <- { site = !site; outer; active = h.active } :: c.uses;
      r
    end in
  let exec, memory = evaluate t ~states:spec.states ~hook:(if latch then Some record else None) ~site in
  exec.hook <- None;
  match if latch then choose_latches t exec memory calls else [] with
  | [] -> t
  | latches -> with_latches t latches ~site

let constant_assignment t constants =
  List.concat_map (fun (name, v) -> assignment (domain t name) v) constants

let array_constants t =
  Bdd.stage := "looking for array fields that never change";
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
