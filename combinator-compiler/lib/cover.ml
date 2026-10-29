type literal = {
  domain : Model.domain;
  must : int list;
  may : int list;
}

type cube = literal list

let domain_bdd (d : Model.domain) values = Bdd.disj (List.map (Model.is_value d) values)

let cube_bdd ?(field = fun l -> l.may) (c : cube) = Bdd.conj (List.map (fun l -> domain_bdd l.domain (field l)) c)

type tree = Leaf of bool | Split of Model.domain * (int list * tree) list

let mdd_cubes ~(domains : Model.domain list) ~preferred f =
  let owner = Hashtbl.create 64 in
  List.iteri (fun i (d : Model.domain) ->
      let rank = if Some d.name = preferred then -1 else i in
      List.iter (fun v -> Hashtbl.replace owner v (rank, d)) d.bits) domains;
  let memo = Hashtbl.create 1024 in
  let rec visit node =
    if node = Bdd.zero then Leaf false
    else if node = Bdd.one then Leaf true
    else match Hashtbl.find_opt memo node with
      | Some t -> t
      | None ->
        let candidates =
          Bdd.support node |> List.filter_map (fun v -> Hashtbl.find_opt owner v)
          |> List.sort_uniq (fun (a, _) (b, _) -> compare a b) in
        if candidates = [] then failwith "Cover: support outside the given domains";
        let best = ref None in
        List.iter (fun (rank, (d : Model.domain)) ->
            let grouped = Hashtbl.create 8 and order = ref [] in
            List.iter (fun v ->
                let child = Bdd.restrict node (Model.assignment d v) in
                match Hashtbl.find_opt grouped child with
                | Some vs -> Hashtbl.replace grouped child (v :: vs)
                | None -> Hashtbl.replace grouped child [ v ]; order := child :: !order) (Model.values d);
            let terminals = Hashtbl.fold (fun child vs n -> if child < 2 then n + List.length vs else n) grouped 0 in
            let score = (float_of_int terminals /. float_of_int d.size, - (List.length !order), - rank) in
            match !best with
            | Some (s, _, _, _) when s >= score -> ()
            | _ -> best := Some (score, d, grouped, List.rev !order)) candidates;
        let _, d, grouped, order = Option.get !best in
        let merged = Hashtbl.create 8 and merged_order = ref [] in
        List.iter (fun child ->
            let r = visit child in
            let vs = Hashtbl.find grouped child in
            match Hashtbl.find_opt merged r with
            | Some old -> Hashtbl.replace merged r (old @ vs)
            | None -> Hashtbl.replace merged r vs; merged_order := r :: !merged_order) order;
        let t = match !merged_order with
          | [ only ] -> only
          | _ -> Split (d, List.rev_map (fun r -> (List.sort compare (Hashtbl.find merged r), r)) !merged_order
                           |> List.filter (fun (_, r) -> r <> Leaf false)) in
        Hashtbl.replace memo node t;
        t
  in
  let rec walk path = function
    | Leaf false -> []
    | Leaf true -> [ List.rev path ]
    | Split (d, branches) ->
      List.concat_map (fun (vs, child) -> walk ({ domain = d; must = vs; may = vs } :: path) child) branches in
  walk [] (visit f)

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

let irredundant ~care ~cost cubes =
  let indexed = List.mapi (fun i c -> (i, c, cube_bdd ~field:(fun l -> l.must) c)) cubes in
  let by_cost = List.sort (fun (i, a, _) (j, b, _) -> compare (cost b, j) (cost a, i)) indexed in
  let kept = ref (List.map (fun (i, _, _) -> i) indexed) in
  List.iter (fun (i, _, bdd) ->
      let others = Bdd.disj (List.filter_map (fun (j, _, b) -> if j <> i && List.mem j !kept then Some b else None) indexed) in
      if Bdd.implies (Bdd.and_ care bdd) others then kept := List.filter (( <> ) i) !kept) by_cost;
  List.filter_map (fun (i, c, _) -> if List.mem i !kept then Some c else None) indexed

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
