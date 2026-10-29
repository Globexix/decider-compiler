open Yojson.Safe.Util

let special = [ "signal-each"; "signal-anything"; "signal-everything" ]

let type_rank = function
  | "virtual" -> 0 | "fluid" -> 1 | "item" -> 2 | "entity" -> 3 | "recipe" -> 4
  | "asteroid-chunk" -> 5 | "quality" -> 6 | "space-location" -> 7
  | kind -> failwith ("unknown signal type " ^ kind)

let identity kind name quality =
  if quality = "normal" && (kind = "virtual" || kind = "item") then name
  else Printf.sprintf "%s:%s@%s" kind name quality

let () =
  let capabilities = Yojson.Safe.from_file Sys.argv.(1) in
  let symbols = Yojson.Safe.from_file Sys.argv.(2) in
  let qualities = symbols |> member "qualities" |> to_list |> List.map (fun q -> q |> member "name" |> to_string) in
  let quality_rank q =
    let rec find i = function [] -> failwith q | x :: rest -> if x = q then i else find (i + 1) rest in
    find 0 qualities
  in
  let signals =
    symbols |> member "signals" |> to_list
    |> List.map (fun s -> (s |> member "type" |> to_string, s |> member "name" |> to_string,
                           s |> member "quality" |> to_string))
    |> List.filter (fun (_, name, _) -> not (List.mem name special))
    |> List.map (fun (kind, name, quality) -> ((quality_rank quality, type_rank kind, name), identity kind name quality))
    |> List.stable_sort (fun (a, _) (b, _) -> compare a b)
    |> List.map snd
  in
  let types =
    capabilities |> member "signals" |> to_list
    |> List.map (fun s -> (s |> member "name" |> to_string, s |> member "type" |> to_string))
  in
  Printf.printf "let factorio = %S\n" (capabilities |> member "version" |> to_string);
  Printf.printf "let display_records = %d\n"
    (capabilities |> member "limits" |> member "display_records" |> to_int);
  Printf.printf "let qualities = [|%s|]\n" (String.concat ";" (List.map (Printf.sprintf "%S") qualities));
  Printf.printf "let identities = [|\n";
  List.iter (Printf.printf "%S;\n") signals;
  Printf.printf "|]\nlet prototype_types = [|\n";
  List.iter (fun (n, t) -> Printf.printf "(%S,%S);\n" n t) types;
  Printf.printf "|]\n"
