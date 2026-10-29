type span = { line : int; col : int; len : int }

type location =
  | Span of span
  | Path of string list
  | Func of string

type t = {
  message : string;
  at : location option;
  notes : (location option * string) list;
  help : string list;
}

exception Compile_error of t

let make ?at ?(notes = []) ?(help = []) message = { message; at; notes; help }

let fail ?at ?notes ?help fmt =
  Printf.ksprintf (fun message -> raise (Compile_error (make ?at ?notes ?help message))) fmt

let check ?at cond message = if not cond then raise (Compile_error (make ?at message))

let locate at f = try f () with Compile_error e when e.at = None -> raise (Compile_error { e with at = Some at })

let context prefix f =
  try f () with Compile_error e -> raise (Compile_error { e with message = prefix ^ e.message })

let edit_distance a b =
  let m = String.length a and n = String.length b in
  let d = Array.init (m + 1) (fun i -> Array.init (n + 1) (fun j -> if i = 0 then j else if j = 0 then i else 0)) in
  for i = 1 to m do
    for j = 1 to n do
      let cost = if a.[i - 1] = b.[j - 1] then 0 else 1 in
      d.(i).(j) <- min (min (d.(i - 1).(j) + 1) (d.(i).(j - 1) + 1)) (d.(i - 1).(j - 1) + cost)
    done
  done;
  d.(m).(n)

let closest name candidates =
  let scored = List.filter_map (fun c ->
      let d = edit_distance (String.lowercase_ascii name) (String.lowercase_ascii c) in
      if c <> name && d <= max 1 (String.length name / 3) then Some (d, c) else None) candidates in
  match List.sort compare scored with (_, c) :: _ -> Some c | [] -> None

let did_you_mean name candidates =
  match closest name candidates with Some c -> [ Printf.sprintf "did you mean `%s`?" c ] | None -> []

let quoted names = String.concat ", " (List.map (Printf.sprintf "`%s`") names)
