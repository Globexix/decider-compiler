type t = Yojson.Safe.t

let escape buf s =
  Buffer.add_char buf '"';
  let n = String.length s in
  let i = ref 0 in
  let u code = Buffer.add_string buf (Printf.sprintf "\\u%04x" code) in
  while !i < n do
    let c = Char.code s.[!i] in
    (match s.[!i] with
     | '"' -> Buffer.add_string buf "\\\""
     | '\\' -> Buffer.add_string buf "\\\\"
     | '\n' -> Buffer.add_string buf "\\n"
     | '\r' -> Buffer.add_string buf "\\r"
     | '\t' -> Buffer.add_string buf "\\t"
     | '\b' -> Buffer.add_string buf "\\b"
     | '\012' -> Buffer.add_string buf "\\f"
     | _ when c >= 0x20 && c < 0x7f -> Buffer.add_char buf s.[!i]
     | _ when c < 0x80 -> u c
     | _ ->
       let d = String.get_utf_8_uchar s !i in
       let code = Uchar.to_int (Uchar.utf_decode_uchar d) in
       i := !i + Uchar.utf_decode_length d - 1;
       if code < 0x10000 then u code
       else begin
         let v = code - 0x10000 in
         u (0xD800 lor (v lsr 10));
         u (0xDC00 lor (v land 0x3FF))
       end);
    incr i
  done;
  Buffer.add_char buf '"'

let float_repr f =
  if Float.is_integer f && Float.abs f < 1e16 then Printf.sprintf "%.1f" f
  else
    let rec go p =
      let s = Printf.sprintf "%.*g" p f in
      if p >= 17 || float_of_string s = f then s else go (p + 1)
    in
    go 1

let rec write ~indent buf depth (v : t) =
  let newline d =
    match indent with
    | None -> ()
    | Some n -> Buffer.add_char buf '\n'; Buffer.add_string buf (String.make (n * d) ' ')
  in
  let item_sep = match indent with None -> "," | Some _ -> "," in
  let key_sep = match indent with None -> ":" | Some _ -> ": " in
  match v with
  | `Null -> Buffer.add_string buf "null"
  | `Bool b -> Buffer.add_string buf (if b then "true" else "false")
  | `Int i -> Buffer.add_string buf (string_of_int i)
  | `Intlit s -> Buffer.add_string buf s
  | `Float f -> Buffer.add_string buf (float_repr f)
  | `String s -> escape buf s
  | `List [] -> Buffer.add_string buf "[]"
  | `Assoc [] -> Buffer.add_string buf "{}"
  | `List items ->
    Buffer.add_char buf '[';
    List.iteri (fun i x ->
        if i > 0 then Buffer.add_string buf item_sep;
        newline (depth + 1);
        write ~indent buf (depth + 1) x) items;
    newline depth;
    Buffer.add_char buf ']'
  | `Assoc fields ->
    Buffer.add_char buf '{';
    List.iteri (fun i (k, x) ->
        if i > 0 then Buffer.add_string buf item_sep;
        newline (depth + 1);
        escape buf k;
        Buffer.add_string buf key_sep;
        write ~indent buf (depth + 1) x) fields;
    newline depth;
    Buffer.add_char buf '}'

let pretty v =
  let buf = Buffer.create 65536 in
  write ~indent:(Some 2) buf 0 v;
  Buffer.contents buf

let compact v =
  let buf = Buffer.create 65536 in
  write ~indent:None buf 0 v;
  Buffer.contents buf
