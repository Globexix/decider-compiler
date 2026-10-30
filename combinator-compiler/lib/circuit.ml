open Error

type wires = Red | Green
type operand = Signal of string * wires | Each
type cond = { left : operand; cmp : string; right : int }

let i32 = Interp.normalize 32

type flag = {
  key : Display.key;
  inverted : bool;
  a : string;
  b : string;
  mutable pass_on : bool;
}

type layout = {
  start : string;
  names : string array;
  lanes : int;
  base : string -> int;
  flags : flag list;
  flag_of : Display.key -> flag;
}

let a_on f = if f.pass_on then 1 else -1
let b_on f = if f.pass_on then 2 else -2

let eq l signal wires raw = { left = Signal (signal, wires); cmp = "="; right = i32 (l.base signal + raw) }
let lane l signal raw = { left = Each; cmp = "="; right = i32 (l.base signal + raw) }

let stored l f ~phase ~on =
  if phase = 0 then eq l f.b Red (if on then b_on f else 0)
  else eq l f.a Red (if on then a_on f else - a_on f)

let visible l f =
  let on = not f.inverted in
  [ (f.a, i32 (l.base f.a + if on then a_on f else - a_on f)); (f.b, i32 (l.base f.b + if on then b_on f else 0)) ]

let allocate (spec : Spec.t) keys =
  let needed = 1 + 2 * List.length keys in
  let lanes = let rec up n = if n >= needed then n else up (2 * n) in up 1 in
  let inputs = List.map (fun (i : Spec.input) -> i.signal) spec.inputs in
  let pool = Array.to_list Signals.catalog |> List.filter (fun s ->
      (not (List.mem s inputs)) && s <> spec.start && (spec.quality = "auto" || Signals.quality s = spec.quality)) in
  if List.length pool < lanes - 1 then fail "signal pool exhausted";
  let names = Array.of_list (spec.start :: List.filteri (fun i _ -> i < lanes - 1) pool) in
  let band = (1 lsl 32) / lanes in
  let bases = Hashtbl.create (2 * lanes) in
  Array.iteri (fun i name -> Hashtbl.replace bases name (if i = 0 then 1 else i32 (i * band))) names;
  let flags = List.mapi (fun i (key, inverted) ->
      { key; inverted; a = names.(1 + 2 * i); b = names.(2 + 2 * i); pass_on = true }) keys in
  let by_key = Hashtbl.create 64 in
  List.iter (fun f -> Hashtbl.replace by_key f.key f) flags;
  { start = spec.start; names; lanes; base = Hashtbl.find bases; flags; flag_of = Hashtbl.find by_key }

type option_ = {
  mult : int;
  size : int;
  accepts : int list;
  build : int -> cond list list;
}

let literal_options l (spec : Spec.t) (lit : Cover.literal) =
  let d = lit.domain in
  if d.input then
    let signal = (List.find (fun (i : Spec.input) -> i.input = d.name) spec.inputs).signal in
    let on = lit.must = [ 1 ] in
    [ { mult = 1; size = 1; accepts = lit.must; build = (fun _ -> [ [ { left = Signal (signal, Red); cmp = (if on then "!=" else "="); right = 0 } ] ]) } ]
  else
    let flag v = try Some (l.flag_of (Display.State (d.name, v))) with Not_found -> None in
    let test phase v present =
      let f = Option.get (flag v) in
      stored l f ~phase ~on:(present <> f.inverted) in
    let has v = flag v <> None in
    let excluded = List.filter (fun v -> not (List.mem v lit.may)) (Model.values d) in
    (if List.for_all has lit.must then
       [ { mult = List.length lit.must; size = 1; accepts = lit.must; build = (fun phase -> List.map (fun v -> [ test phase v true ]) lit.must) } ]
     else [])
    @ (if List.for_all has excluded then
         [ { mult = 1; size = List.length excluded;
             accepts = List.filter (fun v -> not (List.mem v excluded)) (Model.values d); build = (fun phase -> [ List.map (fun v -> test phase v false) excluded ]) } ]
       else [])

let cost ?(extra = 0) options =
  List.fold_left (fun m o -> m * o.mult) 1 options * (1 + extra + List.fold_left (fun s o -> s + o.size) 0 options)

let spell l spec (cube : Cover.cube) =
  let choices = List.map (fun lit ->
      match literal_options l spec lit with
      | [] -> fail "internal: literal on %s has no flag spelling" lit.Cover.domain.name
      | options -> options) cube in
  let ambiguous = List.length (List.filter (fun o -> List.length o > 1) choices) in
  if ambiguous <= 10 then
    let rec best = function
      | [] -> [ [] ]
      | options :: rest -> let tails = best rest in List.concat_map (fun o -> List.map (fun t -> o :: t) tails) options in
    List.fold_left (fun acc c -> match acc with Some a when cost a <= cost c -> acc | _ -> Some c) None (best choices) |> Option.get
  else
    List.map (fun options -> List.fold_left (fun a o -> if cost [ o ] < cost [ a ] then o else a) (List.hd options) options) choices

let cube_cost ?extra l spec cube = cost ?extra (spell l spec cube)
let cover_cost ?extra l spec cubes = List.fold_left (fun s c -> s + cube_cost ?extra l spec c) 0 cubes

let named_first group = let named, each = List.partition (fun c -> c.left <> Each) group in named @ each

let groups l spec ~phase ~prefix cubes =
  List.concat_map (fun cube ->
      let alternatives = List.fold_left (fun acc o ->
          let alts = o.build phase in
          if List.length acc * List.length alts > 100_000 then fail ~notes:[ (None, Printf.sprintf "the compiler stopped while %s" !Bdd.stage) ]
              ~help:[ "narrow the ranges of the states this value depends on" ]
              "a single condition would expand into more than 100000 alternatives";
          List.concat_map (fun a -> List.map (fun b -> a @ b) alts) acc) [ [] ] (spell l spec cube) in
      List.map (fun alt -> named_first (prefix @ alt)) alternatives) cubes

type target = {
  flag : flag;
  next : Bdd.t;
  current : Bdd.t option;
}

type plan = { pass_on : bool; regular : Cover.cube list; held : Cover.cube list }

let plan_target ~optimize l spec (model : Model.t) ~care t =
  let preferred = match t.flag.key with Display.State (s, _) -> Some s | Derived _ -> None in
  let cover ~care f = Cover.cover ~optimize ~domains:model.domains ~preferred ~care ~cost:(cube_cost l spec) f in
  let candidates pass_on =
    let p = if pass_on then t.next else Bdd.not_ t.next in
    let plain = { pass_on; regular = cover ~care p; held = [] } in
    match t.current with
    | Some current when optimize ->
      let shows = if pass_on then current else Bdd.not_ current in
      let held = cover ~care:(Bdd.and_ care shows) p in
      let kept = Bdd.and_ p shows in
      let split = { pass_on; regular = cover ~care:(Bdd.and_ care (Bdd.not_ kept)) p; held } in
      [ plain; split ]
    | _ -> [ plain ] in
  let price p = cover_cost l spec p.regular + cover_cost ~extra:1 l spec p.held in
  let options = if optimize then candidates true @ candidates false else candidates true in
  List.fold_left (fun best p -> if price p < price best then p else best) (List.hd options) options

let compute_groups l spec (f : flag) plan =
  List.concat_map (fun phase ->
      let target, raw = if phase = 0 then (f.a, 0) else (f.b, if f.pass_on then 1 else -1) in
      let prefix = [ lane l target raw ] in
      groups l spec ~phase ~prefix plan.regular
      @ groups l spec ~phase ~prefix:(prefix @ [ stored l f ~phase ~on:f.pass_on ]) plan.held) [ 0; 1 ]

let fixed_groups l =
  let phase p = { left = Signal (l.start, Red); cmp = "="; right = l.base l.start + p } in
  let start = [ { left = Signal (l.start, Red); cmp = "<="; right = 1 };
                { left = Each; cmp = ">="; right = 1 }; { left = Each; cmp = "<="; right = 33 } ] in
  let resets = List.concat_map (fun f ->
      [ [ phase 1; lane l f.a (-1) ]; [ phase 0; lane l f.b (if f.pass_on then 0 else -2) ] ]) l.flags in
  let used = 1 + 2 * List.length l.flags in
  let padding =
    if used >= l.lanes then []
    else [ [ phase 0; { left = Each; cmp = ">="; right = l.base l.names.(used) };
             { left = Each; cmp = "<="; right = l.base l.names.(l.lanes - 1) } ] ] in
  (start :: padding) @ resets

let plan_meaning l spec (t : target) (p : plan) =
  let spelled cube =
    Bdd.conj (List.map2 (fun (lit : Cover.literal) (o : option_) -> Cover.domain_bdd lit.domain o.accepts)
                cube (spell l spec cube)) in
  let cubes cs = Bdd.disj (List.map spelled cs) in
  let pass = Bdd.or_ (cubes p.regular)
      (match t.current with
       | Some current -> Bdd.and_ (cubes p.held) (if p.pass_on then current else Bdd.not_ current)
       | None -> Bdd.zero) in
  if p.pass_on then pass else Bdd.not_ pass
