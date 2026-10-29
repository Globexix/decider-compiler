open Error

type context = {
  input : string;
  source : string option;
  bindings : string option;
  origins : (string list * span) list;
}

let lines text = Array.of_list (String.split_on_char '\n' text)

let origin ctx path =
  let rec go p =
    match List.assoc_opt p ctx.origins with
    | Some s -> Some s
    | None -> if p = [] then None else go (List.filteri (fun i _ -> i < List.length p - 1) p) in
  go path

let function_span ctx name =
  match ctx.source with
  | None -> None
  | Some text ->
    let re = Str.regexp ("\\bfn[ \t]+\\(" ^ Str.quote name ^ "\\)\\b") in
    Array.to_list (lines text) |> List.mapi (fun i l -> (i, l)) |> List.find_map (fun (i, l) ->
        match Str.search_forward re l 0 with
        | _ -> Some { line = i + 1; col = Str.group_beginning 1 + 1; len = String.length name }
        | exception Not_found -> None)

type resolved = At of string * span | Within of string * string | Nowhere

let resolve ctx = function
  | None -> Nowhere
  | Some (Span s) -> At (ctx.input, s)
  | Some (Path p) ->
    (match origin ctx p with
     | Some s -> At (ctx.input, s)
     | None -> Within (Option.value ctx.bindings ~default:ctx.input, String.concat "." p))
  | Some (Func f) ->
    (match function_span ctx f with Some s -> At (ctx.input, s) | None -> Within (ctx.input, "fn " ^ f))

let excerpt ctx (s : span) =
  match ctx.source with
  | None -> ""
  | Some text ->
    let all = lines text in
    if s.line < 1 || s.line > Array.length all then ""
    else
      let line = all.(s.line - 1) in
      let pad = String.init (max 0 (min (s.col - 1) (String.length line))) (fun i -> if line.[i] = '\t' then '\t' else ' ') in
      let width = max 1 (min s.len (String.length line - s.col + 1)) in
      Printf.sprintf "      %s\n      %s^%s\n" line pad (String.make (width - 1) '~')

let header ctx kind at message =
  match resolve ctx at with
  | At (file, s) -> Printf.sprintf "%s:%d:%d: %s: %s\n%s" file s.line s.col kind message (excerpt ctx s)
  | Within (file, where) -> Printf.sprintf "%s: %s: %s: %s\n" file kind where message
  | Nowhere -> Printf.sprintf "%s: %s: %s\n" ctx.input kind message

let render ctx (e : t) =
  let notes = List.map (fun (at, m) ->
      match at with
      | None -> Printf.sprintf "note: %s\n" m
      | Some _ -> header ctx "note" at m) e.notes in
  String.concat "" ((header ctx "error" e.at e.message :: notes) @ List.map (Printf.sprintf "help: %s\n") e.help)
