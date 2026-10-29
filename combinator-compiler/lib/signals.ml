let virtual_signals =
  List.init 26 (fun i -> Printf.sprintf "signal-%c" (Char.chr (65 + i)))
  @ List.init 10 (fun i -> Printf.sprintf "signal-%d" i)
  @ List.map (( ^ ) "signal-")
    [ "red"; "green"; "blue"; "yellow"; "pink"; "cyan"; "white"; "grey"; "black"; "check"; "info"; "dot" ]

let catalog = Catalog_data.identities

let known =
  let table = Hashtbl.create (Array.length catalog) in
  Array.iter (fun s -> Hashtbl.replace table s ()) catalog;
  Hashtbl.mem table

let base_game =
  let table = Hashtbl.create 512 in
  Array.iter (fun s -> Hashtbl.replace table s ()) Catalog_data.base_game;
  Hashtbl.mem table

let rec uses_space_age : Yojson.Safe.t -> bool = function
  | `Assoc fields ->
    (match List.assoc_opt "type" fields, List.assoc_opt "name" fields, List.assoc_opt "quality" fields with
     | Some (`String kind), Some (`String name), quality ->
       quality <> None && quality <> Some (`String "normal")
       || not (List.mem name [ "signal-each"; "signal-anything"; "signal-everything" ]
                || base_game (if kind = "virtual" || kind = "item" then name else Printf.sprintf "%s:%s@normal" kind name))
     | _ -> List.exists (fun (_, v) -> uses_space_age v) fields)
  | `List items -> List.exists uses_space_age items
  | _ -> false

let prototype_type =
  let table = Hashtbl.create 4096 in
  Array.iter (fun (name, kind) -> if not (Hashtbl.mem table name) then Hashtbl.replace table name kind)
    Catalog_data.prototype_types;
  Hashtbl.find_opt table

type t = { kind : string; name : string; quality : string option }

let parse identity =
  match String.index_opt identity ':' with
  | Some i ->
    let rest = String.sub identity (i + 1) (String.length identity - i - 1) in
    let at = String.rindex rest '@' in
    { kind = String.sub identity 0 i; name = String.sub rest 0 at;
      quality = Some (String.sub rest (at + 1) (String.length rest - at - 1)) }
  | None ->
    let kind = match prototype_type identity with
      | Some k -> k
      | None -> if String.starts_with ~prefix:"signal-" identity then "virtual" else "item" in
    { kind; name = identity; quality = None }

let quality identity = Option.value (parse identity).quality ~default:"normal"

let to_json identity : Yojson.Safe.t =
  let s = parse identity in
  `Assoc ([ ("type", `String s.kind); ("name", `String s.name) ]
          @ match s.quality with Some q -> [ ("quality", `String q) ] | None -> [])

let qualities = Array.to_list Catalog_data.qualities

let limits : Yojson.Safe.t =
  `Assoc [ ("display_records", `Int Catalog_data.display_records); ("conditions", `Int 1_000_000);
           ("outputs", `Int 1_000_000);
           ("note", `String "Decider budgets are successfully probed lower bounds, not claimed engine maxima");
           ("factorio", `String Catalog_data.factorio) ]
