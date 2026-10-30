type literal = {
  domain : Model.domain;
  must : int list;
  may : int list;
}

type cube = literal list

let domain_bdd (d : Model.domain) values = Bdd.disj (List.map (Model.is_value d) values)

let cube_bdd ?(field = fun l -> l.may) (c : cube) = Bdd.conj (List.map (fun l -> domain_bdd l.domain (field l)) c)

type tree = Leaf of bool | Split of Model.domain * (int list * tree) list

exception Too_many_cofactors

(* Splits on the domain that settles most of the function first. That choice can visit exponentially
   many cofactors (e.g. splitting on grid cells before the position that indexes them), so past a
   budget it starts over splitting on the domain of the top BDD variable, which visits at most one
   cofactor per BDD node. *)
let mdd_cubes ~(domains : Model.domain list) ~preferred f =
  let owner = Bdd.Tbl.create 64 in
  List.iteri (fun i (d : Model.domain) ->
      let rank = if Some d.name = preferred then -1 else i in
      List.iter (fun v -> Bdd.Tbl.replace owner v (rank, d)) d.bits) domains;
  let budget = 2 * Bdd.dag_size [ f ] + 100 in
  (* Cofactors share most of their nodes, so one restrict memo per (domain, value) serves them all. *)
  let restrictors = Hashtbl.create 64 in
  let restrict node (d : Model.domain) v =
    let r = match Hashtbl.find_opt restrictors (d.name, v) with
      | Some r -> r
      | None -> let r = Bdd.restrictor (Model.assignment d v) in Hashtbl.replace restrictors (d.name, v) r; r in
    r node in
  let rec visit ~greedy memo node =
    if node = Bdd.zero then Leaf false
    else if node = Bdd.one then Leaf true
    else match Bdd.Tbl.find_opt memo node with
      | Some t -> t
      | None ->
        if greedy && Bdd.Tbl.length memo > budget then raise Too_many_cofactors;
        let candidates =
          if greedy then
            Bdd.support node |> List.filter_map (fun v -> Bdd.Tbl.find_opt owner v)
            |> List.sort_uniq (fun (a, _) (b, _) -> compare a b)
          else Option.to_list (Bdd.Tbl.find_opt owner (Bdd.var node)) in
        if candidates = [] then failwith "Cover: support outside the given domains";
        let best = ref None in
        List.iter (fun (rank, (d : Model.domain)) ->
            let grouped = Bdd.Tbl.create 8 and order = ref [] in
            List.iter (fun v ->
                let child = restrict node d v in
                match Bdd.Tbl.find_opt grouped child with
                | Some vs -> Bdd.Tbl.replace grouped child (v :: vs)
                | None -> Bdd.Tbl.replace grouped child [ v ]; order := child :: !order) (Model.values d);
            let terminals = Bdd.Tbl.fold (fun child vs n -> if child < 2 then n + List.length vs else n) grouped 0 in
            let score = (float_of_int terminals /. float_of_int d.size, - (List.length !order), - rank) in
            match !best with
            | Some (s, _, _, _) when s >= score -> ()
            | _ -> best := Some (score, d, grouped, List.rev !order)) candidates;
        let _, d, grouped, order = Option.get !best in
        (* Distinct children are distinct functions, so their trees never coincide. *)
        let branches = List.map (fun child -> (List.sort compare (Bdd.Tbl.find grouped child), visit ~greedy memo child)) order in
        let t = match branches with
          | [ (_, only) ] -> only
          | _ -> Split (d, List.filter (fun (_, r) -> r <> Leaf false) branches) in
        Bdd.Tbl.replace memo node t;
        t
  in
  let rec walk path = function
    | Leaf false -> []
    | Leaf true -> [ List.rev path ]
    | Split (d, branches) ->
      List.concat_map (fun (vs, child) -> walk ({ domain = d; must = vs; may = vs } :: path) child) branches in
  let root = try visit ~greedy:true (Bdd.Tbl.create 1024) f
    with Too_many_cofactors -> visit ~greedy:false (Bdd.Tbl.create 1024) f in
  walk [] root

let expand ~care f (c : cube) =
  let ok = Bdd.or_ f (Bdd.not_ care) in
  let fits (c : cube) = Bdd.implies (cube_bdd c) ok in
  let replace c (l : literal) l' = List.map (fun x -> if x == l then l' else x) c in
  let c = List.fold_left (fun c l ->
      let without = List.filter (fun x -> x != l) c in
      if fits without then without else c) c c in
  List.fold_left (fun c (l : literal) ->
      let grown = List.fold_left (fun (cur : literal) v ->
          if List.mem v cur.may then cur
          else
            let candidate = { cur with may = List.sort compare (v :: cur.may) } in
            if fits (replace c l candidate) then candidate else cur) l (Model.values l.domain) in
      replace c l grown) c c

(* Greedy removal in cost order. A segment tree over the cubes keeps unions of the ones still kept,
   so the union of all others costs O(log n) BDD operations instead of O(n). *)
let irredundant ~care ~cost cubes =
  let cubes = Array.of_list cubes in
  let n = Array.length cubes in
  let size = ref 1 in
  while !size < n do size := 2 * !size done;
  let tree = Array.make (2 * !size) Bdd.zero in
  Array.iteri (fun i c -> tree.(!size + i) <- cube_bdd ~field:(fun l -> l.must) c) cubes;
  for k = !size - 1 downto 1 do tree.(k) <- Bdd.or_ tree.(2 * k) tree.(2 * k + 1) done;
  let others i =
    let rec up k acc = if k = 1 then acc else up (k / 2) (Bdd.or_ acc tree.(k lxor 1)) in
    up (!size + i) Bdd.zero in
  let drop i =
    let k = ref (!size + i) in
    tree.(!k) <- Bdd.zero;
    while !k > 1 do k := !k / 2; tree.(!k) <- Bdd.or_ tree.(2 * !k) tree.(2 * !k + 1) done in
  let kept = Array.make n true in
  let by_cost = List.sort (fun i j -> compare (cost cubes.(j), j) (cost cubes.(i), i)) (List.init n Fun.id) in
  List.iter (fun i ->
      if Bdd.implies (Bdd.and_ care tree.(!size + i)) (others i) then (kept.(i) <- false; drop i)) by_cost;
  List.filteri (fun i _ -> kept.(i)) (Array.to_list cubes)

let cover ?(optimize = true) ~domains ~preferred ~care ~cost f =
  let f = Bdd.and_ f care in
  if f = Bdd.zero then []
  else if Bdd.implies care f then [ [] ]
  else
    let cubes = mdd_cubes ~domains ~preferred f in
    if not optimize then cubes
    else
      let expanded = List.map (expand ~care f) cubes in
      irredundant ~care ~cost (List.sort_uniq compare expanded)
