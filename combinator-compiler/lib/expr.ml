open Error

type t =
  | Int of int
  | Ref of string
  | Neg of t
  | Bin of [ `Add | `Sub | `Mul ] * t * t

let is_ident c = c = '_' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')

let parse ~names text =
  let n = String.length text in
  let pos = ref 0 in
  let found () = if !pos >= n then "end of expression" else Printf.sprintf "`%s`" (String.sub text !pos (n - !pos)) in
  let invalid () =
    fail ~help:[ "display expressions use integers, states, `+`, `-`, `*` and parentheses" ]
      "malformed expression `%s`: unexpected %s" text (found ()) in
  let rec skip () = if !pos < n && (text.[!pos] = ' ' || text.[!pos] = '\t') then (incr pos; skip ()) in
  let peek () = skip (); if !pos < n then Some text.[!pos] else None in
  let ident () =
    let start = !pos in
    while !pos < n && is_ident text.[!pos] do incr pos done;
    String.sub text start (!pos - start) in
  let rec expr () =
    let left = ref (term ()) in
    let rec loop () = match peek () with
      | Some ('+' | '-' as c) -> incr pos; left := Bin ((if c = '+' then `Add else `Sub), !left, term ()); loop ()
      | _ -> () in
    loop (); !left
  and term () =
    let left = ref (unary ()) in
    let rec loop () = match peek () with
      | Some '*' when not (!pos + 1 < n && text.[!pos + 1] = '*') -> incr pos; left := Bin (`Mul, !left, unary ()); loop ()
      | _ -> () in
    loop (); !left
  and unary () = match peek () with
    | Some '-' -> incr pos; Neg (unary ())
    | Some '+' -> incr pos; unary ()
    | _ -> atom ()
  and atom () = match peek () with
    | Some '(' -> incr pos; let e = expr () in if peek () <> Some ')' then invalid (); incr pos; e
    | Some c when c >= '0' && c <= '9' ->
      let s = ident () in
      (match int_of_string_opt (String.concat "" (String.split_on_char '_' s)) with Some v -> Int v | None -> invalid ())
    | Some c when is_ident c ->
      let name = Buffer.create 16 in
      Buffer.add_string name (ident ());
      let rec suffix () = match peek () with
        | Some '.' -> incr pos; skip (); let f = ident () in if f = "" then invalid (); Buffer.add_char name '.'; Buffer.add_string name f; suffix ()
        | Some '[' ->
          let depth = ref 0 and start = !pos in
          while (if !pos >= n then invalid () else true) && (text.[!pos] <> ']' || !depth > 1) do
            if text.[!pos] = '[' then incr depth else if text.[!pos] = ']' then decr depth;
            incr pos done;
          incr pos;
          let inner = String.sub text start (!pos - start) in
          Buffer.add_string name (String.concat "" (String.split_on_char ' ' inner)); suffix ()
        | _ -> () in
      suffix ();
      (match Buffer.contents name with
       | "true" | "True" -> Int 1
       | "false" | "False" -> Int 0
       | r ->
         if not (List.mem r names) then
           fail ~help:(did_you_mean r names) "`%s` is not a declared state" r;
         Ref r)
    | _ -> invalid ()
  in
  let e = expr () in
  if peek () <> None then invalid ();
  e

let rec refs = function
  | Int _ -> []
  | Ref r -> [ r ]
  | Neg e -> refs e
  | Bin (_, a, b) -> List.sort_uniq compare (refs a @ refs b)

let i32 n = Interp.normalize 32 n

let rec eval env = function
  | Int n -> i32 n
  | Ref r -> env r
  | Neg e -> i32 (- (eval env e))
  | Bin (op, a, b) ->
    let a = eval env a and b = eval env b in
    i32 (match op with `Add -> a + b | `Sub -> a - b | `Mul -> a * b)

let rec symbolic env = function
  | Int n -> Bitvec.const n
  | Ref r -> env r
  | Neg e -> Bitvec.neg (symbolic env e)
  | Bin (op, a, b) ->
    let a = symbolic env a and b = symbolic env b in
    (match op with `Add -> Bitvec.add a b | `Sub -> Bitvec.sub a b | `Mul -> Bitvec.mul a b)

let constant e = if refs e = [] then Some (eval (fun _ -> 0) e) else None
