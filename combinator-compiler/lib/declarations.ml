open Error

let fail ?at ?notes ?help fmt = Error.fail ?at:(Option.map (fun s -> Span s) at) ?notes ?help fmt

type origins = (string list * span) list

let code source =
  let b = Bytes.of_string source and n = String.length source in
  let blank i = if i < n && Bytes.get b i <> '\n' then Bytes.set b i ' ' in
  let rec go i =
    if i + 1 < n && source.[i] = '/' && source.[i + 1] = '/' then begin
      let j = ref i in
      while !j < n && source.[!j] <> '\n' do blank !j; incr j done;
      go !j
    end else if i + 1 < n && source.[i] = '/' && source.[i + 1] = '*' then begin
      let j = ref i in
      while !j < n && not (!j > i + 1 && source.[!j - 1] = '*' && source.[!j] = '/') do blank !j; incr j done;
      blank !j;
      go (!j + 1)
    end else if i < n then go (i + 1) in
  go 0;
  Bytes.to_string b

let span_of source offset len =
  let line = ref 1 and start = ref 0 in
  for i = 0 to min offset (String.length source) - 1 do
    if source.[i] = '\n' then (incr line; start := i + 1)
  done;
  { line = !line; col = offset - !start + 1; len = max 1 len }

type cursor = { text : string; line : int; base : int; mutable pos : int; syntax : string }

let is_space c = c = ' ' || c = '\t'
let is_word c = match c with 'A' .. 'Z' | 'a' .. 'z' | '0' .. '9' | '_' -> true | _ -> false

let skip c = while c.pos < String.length c.text && is_space c.text.[c.pos] do c.pos <- c.pos + 1 done
let at_end c = skip c; c.pos >= String.length c.text
let span c pos len = { line = c.line; col = c.base + pos; len = max 1 len }
let write_as c = "write it as `" ^ c.syntax ^ "`"

let syntax_error c what =
  skip c;
  let j = ref c.pos in
  while !j < String.length c.text && not (is_space c.text.[!j]) do incr j done;
  let token = String.sub c.text c.pos (!j - c.pos) in
  let got = if token = "" then "end of line" else Printf.sprintf "`%s`" token in
  fail ~at:(span c c.pos (String.length token)) ~help:[ write_as c ] "expected %s, found %s" what got

let take c pred =
  skip c;
  let start = c.pos in
  while c.pos < String.length c.text && pred c.text.[c.pos] do c.pos <- c.pos + 1 done;
  (String.sub c.text start (c.pos - start), span c start (c.pos - start))

let name c what =
  skip c;
  if at_end c || not (is_word c.text.[c.pos]) || (c.text.[c.pos] >= '0' && c.text.[c.pos] <= '9') then syntax_error c what;
  take c is_word

let integer c what =
  skip c;
  let start = c.pos in
  if c.pos < String.length c.text && c.text.[c.pos] = '-' then c.pos <- c.pos + 1;
  let digits, _ = take c (fun ch -> ch >= '0' && ch <= '9') in
  if digits = "" then (c.pos <- start; syntax_error c what);
  let text = String.sub c.text start (c.pos - start) in
  let at = span c start (c.pos - start) in
  match int_of_string_opt text with
  | Some n when n >= -0x8000_0000 && n <= 0x7fff_ffff -> (n, at)
  | _ -> fail ~at "%s does not fit a 32-bit signal" text

let expect c token =
  skip c;
  let n = String.length token in
  if c.pos + n <= String.length c.text && String.sub c.text c.pos n = token then c.pos <- c.pos + n
  else syntax_error c (Printf.sprintf "`%s`" token)

let finish c = if not (at_end c) then syntax_error c "end of declaration"

let words c =
  let out = ref [] in
  while not (at_end c) do
    let start = c.pos and buf = Buffer.create 16 and quote = ref None in
    while c.pos < String.length c.text && (!quote <> None || not (is_space c.text.[c.pos])) do
      let ch = c.text.[c.pos] in
      (match !quote with
       | Some q when ch = q -> quote := None
       | Some _ -> Buffer.add_char buf ch
       | None when ch = '\'' || ch = '"' -> quote := Some ch
       | None -> Buffer.add_char buf ch);
      c.pos <- c.pos + 1
    done;
    if !quote <> None then fail ~at:(span c start (c.pos - start)) "unterminated quote";
    out := (Buffer.contents buf, span c start (c.pos - start)) :: !out
  done;
  List.rev !out

let options c ~allowed words =
  List.fold_left (fun acc (w, (sp : span)) ->
      match String.index_opt w '=' with
      | Some i when i > 0 ->
        let key = String.sub w 0 i and value = String.sub w (i + 1) (String.length w - i - 1) in
        let key_span = { sp with len = i } in
        if not (List.mem key allowed) then
          fail ~at:key_span ~help:(did_you_mean key allowed @ [ write_as c ])
            "unknown option `%s`; expected %s" key (quoted allowed);
        if List.mem_assoc key acc then fail ~at:key_span "option `%s` is given twice" key;
        acc @ [ (key, (value, { sp with col = sp.col + i + 1; len = max 1 (String.length value) })) ]
      | _ -> fail ~at:sp ~help:[ write_as c ] "expected `key=value`, found `%s`" w) [] words

type decl = { kind : string; kind_span : span; whole : span; cursor : cursor }

let syntaxes = [
  ("state", "// @state NAME: MIN..MAX = INITIAL");
  ("input", "// @input NAME = SIGNAL");
  ("array", "// @array NAME: STRUCT[COUNT]");
  ("field", "// @field ARRAY.FIELD: MIN..MAX = INITIAL[, INITIAL...]");
  ("screen", "// @screen WIDTHxHEIGHT");
  ("rect", "// @rect [NAME] x=EXPR y=EXPR width=EXPR height=EXPR [enabled=EXPR] [icon=SIGNAL]");
  ("bar", "// @bar STATE x=COLUMN size=LENGTH [icon=SIGNAL]");
  ("digits", "// @digits STATE at=X,Y [icon=SIGNAL]");
  ("number", "// @number STATE at=X,Y");
  ("point", "// @point XSTATE,YSTATE [icon=SIGNAL]");
]

let declaration_re = Str.regexp "^\\([ \t]*//[ \t]*\\)@\\([A-Za-z_]+\\)"

let declarations source =
  let strip_cr line =
    let n = String.length line in
    if n > 0 && line.[n - 1] = '\r' then String.sub line 0 (n - 1) else line in
  List.mapi (fun i line -> (i + 1, strip_cr line)) (String.split_on_char '\n' source)
  |> List.filter_map (fun (number, line) ->
      if not (Str.string_match declaration_re line 0) then None
      else
        let at = Str.match_end () in
        let col = String.length (Str.matched_group 1 line) + 1 and kind = Str.matched_group 2 line in
        let kind_span = { line = number; col; len = String.length kind + 1 } in
        let rest = String.sub line (col - 1) (String.length line - col + 1) in
        let whole = { line = number; col; len = String.length (String.trim rest) } in
        let syntax = match List.assoc_opt kind syntaxes with
          | Some s -> s
          | None ->
            fail ~at:kind_span
              ~help:(did_you_mean ("@" ^ kind) (List.map (fun (k, _) -> "@" ^ k) syntaxes)
                     @ [ "declarations are " ^ quoted (List.map (fun (k, _) -> "@" ^ k) syntaxes) ])
              "unknown declaration `@%s`" kind in
        Some { kind; kind_span; whole;
               cursor = { text = String.sub line at (String.length line - at); line = number; base = at + 1; pos = 0; syntax } })

type struct_field = { fname : string; ftype : string; fspan : span }
type struct_source = { sname : string; sspan : span; sfields : struct_field list }

let ident = "[A-Za-z_][A-Za-z0-9_]*"

let structs source code =
  let re = Str.regexp ("\\bstruct[ \t\n]+\\(" ^ ident ^ "\\)[ \t\n]*{\\([^}]*\\)}") in
  let field_re = Str.regexp ("\\(" ^ ident ^ "\\)[ \t\n]+\\([^,\n]*[^,\n \t]\\)") in
  let rec scan pos acc =
    match Str.search_forward re code pos with
    | exception Not_found -> List.rev acc
    | _ ->
      let sname = Str.matched_group 1 code and body = Str.matched_group 2 code in
      let name_at = Str.group_beginning 1 and body_at = Str.group_beginning 2 and next = Str.match_end () in
      let rec fields p acc =
        match Str.search_forward field_re body p with
        | exception Not_found -> List.rev acc
        | _ ->
          let f = { fname = Str.matched_group 1 body; ftype = Str.matched_group 2 body;
                    fspan = span_of source (body_at + Str.group_beginning 1) (Str.match_end () - Str.group_beginning 1) } in
          fields (Str.match_end ()) (f :: acc) in
      scan next ({ sname; sspan = span_of source name_at (String.length sname); sfields = fields 0 [] } :: acc) in
  scan 0 []

let parameters source code name =
  let re = Str.regexp ("\\bfn[ \t\n]+" ^ Str.quote name ^ "[ \t\n]*(\\([^)]*\\))") in
  match Str.search_forward re code 0 with
  | exception Not_found -> None
  | _ ->
    let body = Str.matched_group 1 code and at = Str.group_beginning 1 in
    let re = Str.regexp ("\\(" ^ ident ^ "\\)[ \t\n]+[^,]+") in
    let rec go p acc =
      match Str.search_forward re body p with
      | exception Not_found -> List.rev acc
      | _ ->
        let n = Str.matched_group 1 body in
        go (Str.match_end ()) ((n, span_of source (at + Str.group_beginning 1) (String.length n)) :: acc) in
    Some (go 0 [])

type array_decl = { aname : string; aspan : span; struct_ : string; struct_span : span; count : int; adecl : span }

type field_decl = {
  array : string; field : string; lo : int; hi : int; initials : int list;
  fdecl : span;
  fref : span;
}

let parse_range c =
  let lo, lo_span = integer c "the minimum value" in
  expect c "..";
  let hi, hi_span = integer c "the maximum value" in
  let at = { lo_span with len = hi_span.col + hi_span.len - lo_span.col } in
  if lo > hi then fail ~at "empty range %d..%d" lo hi;
  (lo, hi, at)

let check_initial ~at lo hi v = if v < lo || v > hi then fail ~at "initial value %d is outside %d..%d" v lo hi

let parse_array d =
  let c = d.cursor in
  let aname, aspan = name c "an array name" in
  expect c ":";
  let struct_, struct_span = name c "a struct name" in
  expect c "[";
  let count, count_span = integer c "the array capacity" in
  expect c "]";
  finish c;
  if count < 1 || count > 32 then fail ~at:count_span "array capacity %d is outside 1..32" count;
  { aname; aspan; struct_; struct_span; count; adecl = d.whole }

let parse_field d =
  let c = d.cursor in
  let array, a_span = name c "an array name" in
  expect c ".";
  let field, f_span = name c "a field name" in
  expect c ":";
  let lo, hi, _ = parse_range c in
  expect c "=";
  let rec initials acc =
    let v, at = integer c "an initial value" in
    check_initial ~at lo hi v;
    skip c;
    if c.pos < String.length c.text && c.text.[c.pos] = ',' then (c.pos <- c.pos + 1; initials (v :: acc))
    else List.rev (v :: acc) in
  let initials = initials [] in
  finish c;
  { array; field; lo; hi; initials; fdecl = d.whole; fref = { a_span with len = f_span.col + f_span.len - a_span.col } }

let field_syntax a (sf : struct_field) =
  Printf.sprintf "// @field %s.%s: %s = %s" a sf.fname (if sf.ftype = "bool" then "0..1" else "MIN..MAX") "INITIAL"

let resolve_arrays source code (ir : Ir.program) arrays fields =
  let defs = structs source code in
  List.iter (fun (f : field_decl) ->
      if not (List.exists (fun a -> a.aname = f.array) arrays) then
        fail ~at:{ f.fref with len = String.length f.array }
          ~help:(match did_you_mean f.array (List.map (fun a -> a.aname) arrays) with
              | [] -> [ Printf.sprintf "declare the array: `// @array %s: STRUCT[COUNT]`" f.array ]
              | h -> h)
          "no `@array %s` for this field" f.array) fields;
  List.map (fun a ->
      let def = match List.find_opt (fun s -> s.sname = a.struct_) defs with
        | Some s -> s
        | None ->
          fail ~at:a.struct_span ~help:(did_you_mean a.struct_ (List.map (fun s -> s.sname) defs))
            "struct `%s` is not defined in this file" a.struct_ in
      if def.sfields = [] then fail ~at:def.sspan "struct `%s` has no fields" def.sname;
      let names = List.map (fun f -> f.fname) def.sfields in
      let struct_note = (Some (Span def.sspan), Printf.sprintf "struct `%s` has fields %s" def.sname (quoted names)) in
      List.iter (fun sf ->
          match List.find_opt (fun g -> g.fname = sf.fname && g != sf) def.sfields with
          | Some _ -> fail ~at:sf.fspan "struct `%s` has two fields named `%s`" def.sname sf.fname
          | None ->
            if not (List.mem sf.ftype [ "i32"; "bool" ]) then
              fail ~at:sf.fspan ~notes:[ (Some (Span a.struct_span), Printf.sprintf "`@array %s` stores this struct" a.aname) ]
                "field `%s` has type `%s`; array struct fields must be `i32` or `bool`" sf.fname sf.ftype) def.sfields;
      let declared = List.filter (fun f -> f.array = a.aname) fields in
      List.iter (fun (f : field_decl) ->
          if not (List.mem f.field names) then
            let missing = List.filter (fun n -> not (List.exists (fun (g : field_decl) -> g.field = n) declared)) names in
            fail ~at:f.fref ~notes:[ struct_note ]
              ~help:(match did_you_mean f.field missing, missing with
                  | [], [ only ] -> [ Printf.sprintf "did you mean `%s`? it is the only field without an `@field`" only ]
                  | [], _ -> did_you_mean f.field names
                  | h, _ -> h)
              "struct `%s` has no field `%s`" def.sname f.field) declared;
      let typed = List.map (fun sf ->
          match List.filter (fun (f : field_decl) -> f.field = sf.fname) declared with
          | [ f ] -> (sf, f)
          | [] ->
            let missing = List.filter (fun g -> not (List.exists (fun (f : field_decl) -> f.field = g.fname) declared)) def.sfields in
            fail ~at:a.adecl
              ~notes:(List.map (fun g -> (Some (Span g.fspan), Printf.sprintf "field `%s` is declared here" g.fname)) missing)
              ~help:(List.map (fun g -> "add `" ^ field_syntax a.aname g ^ "`") missing
                     @ [ "every field of an array's struct needs bounds and initial values" ])
              "array `%s` is missing `@field` for %s %s" a.aname
              (if List.length missing = 1 then "field" else "fields") (quoted (List.map (fun g -> g.fname) missing))
          | first :: second :: _ ->
            fail ~at:second.fdecl ~notes:[ (Some (Span first.fdecl), "first declared here") ]
              "`@field %s.%s` is declared twice" a.aname sf.fname) def.sfields in
      List.iter (fun (sf, (f : field_decl)) ->
          let n = List.length f.initials in
          if n <> 1 && n <> a.count then
            fail ~at:f.fdecl ~notes:[ (Some (Span a.adecl), Printf.sprintf "`%s` has %d elements" a.aname a.count) ]
              ~help:[ "give one initial value per element, or a single value for all of them" ]
              "%d initial values for %d elements" n a.count;
          if sf.ftype = "bool" && (f.lo, f.hi) <> (0, 1) then
            fail ~at:f.fdecl ~notes:[ (Some (Span sf.fspan), "declared `bool` here") ] "`%s.%s` is a bool; its bounds must be 0..1" a.aname f.field) typed;
      let expected = List.map (fun (sf, _) -> if sf.ftype = "i32" then Ir.Int 32 else Ir.Int 8) typed in
      let layout = match List.assoc_opt a.struct_ ir.structs with
        | Some (d : Ir.struct_def) when d.fields = expected -> d
        | _ -> fail ~at:def.sspan "struct `%s` does not match its Fas IR layout (this is a combinator-compiler bug)" a.struct_ in
      let offset = ref 0 in
      let fields_json = List.map (fun (sf, f) ->
          let size = if sf.ftype = "i32" then 4 else 1 in
          offset := (!offset + size - 1) / size * size;
          let json = `Assoc [ ("name", `String f.field); ("type", `String sf.ftype); ("offset", `Int !offset);
                              ("min", `Int f.lo); ("max", `Int f.hi);
                              ("initials", `List (List.map (fun n -> `Int n) f.initials)) ] in
          offset := !offset + size;
          json) typed in
      (a, List.map snd typed,
       `Assoc [ ("type", `String a.struct_); ("count", `Int a.count); ("fields", `List fields_json);
                ("stride", `Int (!offset + layout.tail_padding)) ])) arrays

let bindings_with_origins source (ir : Ir.program) : Yojson.Safe.t * origins =
  let code = code source in
  let decls = declarations source in
  let origins = ref [] in
  let origin path sp = origins := (path, sp) :: !origins in
  let names = Hashtbl.create 16 in
  let claim name sp what =
    match Hashtbl.find_opt names name with
    | Some (first, kind) ->
      fail ~at:sp ~notes:[ (Some (Span first), Printf.sprintf "first declared here as %s" kind) ] "`%s` is declared twice" name
    | None -> Hashtbl.replace names name (sp, what) in
  let arrays = List.filter_map (fun d -> if d.kind = "array" then Some (parse_array d) else None) decls in
  List.iter (fun a -> claim a.aname a.aspan "an array") arrays;
  let fields = List.filter_map (fun d -> if d.kind = "field" then Some (parse_field d) else None) decls in
  let groups = resolve_arrays source code ir arrays fields in
  let states = ref [] and inputs = ref [] and layers = ref [] and screen = ref None and refs = ref [] in
  let layer_path () = [ "outputs"; "0"; "layers"; string_of_int (List.length !layers) ] in
  let need_screen d =
    if !screen = None then
      fail ~at:d.kind_span ~help:[ "add `// @screen WIDTHxHEIGHT` before the first display layer" ]
        "`@%s` needs a `@screen` declared before it" d.kind in
  List.iter (fun d ->
      let c = d.cursor in
      match d.kind with
      | "array" | "field" -> ()
      | "state" ->
        let n, sp = name c "a state name" in
        expect c ":";
        let lo, hi, _ = parse_range c in
        expect c "=";
        let initial, at = integer c "the initial value" in
        finish c;
        check_initial ~at lo hi initial;
        claim n sp "a state";
        origin [ "state"; n ] d.whole;
        states := !states @ [ (n, `Assoc [ ("min", `Int lo); ("max", `Int hi); ("initial", `Int initial) ]) ]
      | "input" ->
        let n, sp = name c "an input name" in
        expect c "=";
        let signal, ssp = take c (fun ch -> not (is_space ch)) in
        if signal = "" then syntax_error c "a signal name";
        finish c;
        claim n sp "an input";
        origin [ "inputs"; n ] d.whole;
        origin [ "inputs"; n; "signal" ] ssp;
        inputs := !inputs @ [ (n, `Assoc [ ("signal", `String signal); ("type", `String "bool") ]) ]
      | "screen" ->
        Option.iter (fun (_, _, first) ->
            fail ~at:d.whole ~notes:[ (Some (Span first), "first declared here") ] "only one `@screen` is supported") !screen;
        let w, wsp = integer c "the screen width" in
        expect c "x";
        let h, hsp = integer c "the screen height" in
        finish c;
        List.iter (fun (v, at) -> if v < 1 then fail ~at "screen size must be positive, found %d" v) [ (w, wsp); (h, hsp) ];
        origin [ "outputs"; "0" ] d.whole;
        screen := Some (w, h, d.whole)
      | "rect" ->
        need_screen d;
        let ws = words c in
        let label, ws = match ws with
          | (t, _) :: rest when not (String.contains t '=') -> (t, rest)
          | _ -> (Printf.sprintf "rect_%d" d.whole.line, ws) in
        let opts = options c ~allowed:[ "x"; "y"; "width"; "height"; "enabled"; "icon" ] ws in
        List.iter (fun k ->
            if not (List.mem_assoc k opts) then fail ~at:d.whole ~help:[ write_as c ] "`@rect` is missing `%s=`" k)
          [ "x"; "y"; "width"; "height" ];
        let mentions g v = Str.string_match (Str.regexp (".*\\b" ^ Str.quote g ^ "\\.")) v 0 in
        let used = List.filter (fun (a, _, _) -> List.exists (fun (k, (v, _)) -> k <> "icon" && mentions a.aname v) opts) groups in
        (match used with
         | (a, _, _) :: (b, _, _) :: _ ->
           fail ~at:d.whole ~help:[ Printf.sprintf "index the other array explicitly, e.g. `%s[0].FIELD`" b.aname ]
             "one `@rect` repeats over one array, but this one uses both `%s` and `%s`" a.aname b.aname
         | _ -> ());
        let count, rename = match used with
          | [ (a, _, _) ] ->
            (a.count, fun index v ->
                Str.global_replace (Str.regexp ("\\b" ^ Str.quote a.aname ^ "\\.")) (Printf.sprintf "%s[%d]." a.aname index) v)
          | _ -> (1, fun _ v -> v) in
        for index = 0 to count - 1 do
          let path = layer_path () in
          origin path d.whole;
          List.iter (fun (k, (_, sp)) -> origin (path @ [ k ]) sp) opts;
          let lname = if used <> [] then Printf.sprintf "%s[%d]" label index else label in
          layers := !layers @ [ `Assoc (("kind", `String "rect") :: ("name", `String lname)
                                        :: List.map (fun (k, (v, _)) -> (k, `String (if k = "icon" then v else rename index v))) opts) ]
        done
      | ("bar" | "digits" | "point" | "number") as kind ->
        need_screen d;
        let (first, first_span), rest = match words c with
          | w :: rest when not (String.contains (fst w) '=') -> (w, rest)
          | _ -> syntax_error c (if kind = "point" then "`XSTATE,YSTATE`" else "a state name") in
        let allowed = match kind with
          | "bar" -> [ "x"; "size"; "icon" ] | "digits" -> [ "at"; "icon" ] | "number" -> [ "at" ] | _ -> [ "icon" ] in
        let opts = try options c ~allowed rest
          with Compile_error e when kind = "number" && List.exists (fun (w, _) -> String.starts_with ~prefix:"icon=" w) rest ->
            raise (Compile_error { e with help = [ "`@number` picks its icons from the value; use `@digits` for colored pixel digits" ] }) in
        List.iter (fun k ->
            if k <> "icon" && not (List.mem_assoc k opts) then
              fail ~at:d.whole ~help:[ write_as c ] "`@%s` is missing `%s=`" kind k) allowed;
        let int_opt k =
          let v, at = List.assoc k opts in
          match int_of_string_opt v with Some n -> `Int n | None -> fail ~at "`%s=` must be an integer, found `%s`" k v in
        let pair k =
          let v, at = List.assoc k opts in
          match List.map (fun s -> int_of_string_opt (String.trim s)) (String.split_on_char ',' v) with
          | [ Some x; Some y ] -> `List [ `Int x; `Int y ]
          | _ -> fail ~at "`%s=` must be two integers `X,Y`, found `%s`" k v in
        let path = layer_path () in
        origin path d.whole;
        List.iter (fun (k, (_, sp)) -> origin (path @ [ k ]) sp) opts;
        let body = match kind with
          | "bar" -> [ ("state", `String first); ("x", int_opt "x"); ("size", int_opt "size") ]
          | "digits" | "number" -> [ ("state", `String first); ("at", pair "at") ]
          | _ ->
            (match String.index_opt first ',' with
             | Some i ->
               let x = String.sub first 0 i and y = String.sub first (i + 1) (String.length first - i - 1) in
               refs := (y, { first_span with col = first_span.col + i + 1; len = String.length y }, kind)
                       :: (x, { first_span with len = i }, kind) :: !refs;
               [ ("x", `String x); ("y", `String y) ]
             | None -> fail ~at:first_span ~help:[ write_as c ] "expected `XSTATE,YSTATE`, found `%s`" first) in
        if kind <> "point" then (origin (path @ [ "state" ]) first_span; refs := (first, first_span, kind) :: !refs);
        let icon = match List.assoc_opt "icon" opts with Some (i, _) -> [ ("icon", `String i) ] | None -> [] in
        layers := !layers @ [ `Assoc ((("kind", `String kind) :: body) @ icon) ]
      | _ -> assert false) decls;
  let flat = List.concat_map (fun (a, fields, _) ->
      List.concat (List.init a.count (fun index ->
          List.map (fun (f : field_decl) ->
              let n = Printf.sprintf "%s[%d].%s" a.aname index f.field in
              origin [ "state"; n ] f.fdecl;
              let initial = List.nth f.initials (if List.length f.initials = 1 then 0 else index) in
              (n, `Assoc [ ("min", `Int f.lo); ("max", `Int f.hi); ("initial", `Int initial) ])) fields))) groups in
  let states = !states @ flat in
  if states = [] then
    fail ~help:[ "declare state in comments, e.g. `// @state score: 0..9 = 0`, or pass --bindings FILE" ]
      "no `@state` or `@array` declarations";
  let state_names = List.map fst states in
  List.iter (fun (n, at, kind) ->
      if not (List.mem n state_names) then
        fail ~at ~help:(match did_you_mean n state_names with
            | [] -> [ Printf.sprintf "declare it with `// @state %s: MIN..MAX = INITIAL` and define `fn update_%s(...)`" n n ]
            | h -> h)
          "`@%s` shows `%s`, which is not a declared state" kind n) (List.rev !refs);
  let input_names = List.map fst !inputs and array_names = List.map (fun (a, _, _) -> a.aname) groups in
  let fn_names = List.map (fun (f : Ir.func) -> f.name) ir.funcs in
  let updates = List.map (fun (state, _) ->
      let owner = match String.index_opt state '[' with Some i -> String.sub state 0 i | None -> state in
      let fname = "update_" ^ owner in
      let f = match Ir.find_func ir fname with
        | Some f -> f
        | None ->
          fail ~at:(List.assoc [ "state"; state ] !origins)
            ~help:(did_you_mean fname fn_names
                   @ [ Printf.sprintf "every state is updated once per tick by `fn %s(...)`" fname ])
            "no update function `%s` for `%s`" fname owner in
      let params = match parameters source code fname with
        | Some p -> p
        | None -> Error.fail ~at:(Func fname) "cannot read the parameter names of `%s`" fname in
      if List.length params <> List.length f.params then
        Error.fail ~at:(Func fname) "`%s` has %d parameters in the source but %d in Fas IR (this is a combinator-compiler bug)"
          fname (List.length params) (List.length f.params);
      List.iter (fun (p, at) ->
          if not (List.mem p state_names || List.mem p input_names || List.mem p array_names) then
            fail ~at ~help:(did_you_mean p (state_names @ input_names @ array_names)
                            @ [ "parameters are bound by name to `@state`, `@array` and `@input` declarations" ])
              "parameter `%s` of `%s` matches no declaration" p fname) params;
      (state, `Assoc [ ("function", `String fname); ("args", `List (List.map (fun (p, _) -> `String p) params)) ])) states in
  let outputs = match !screen with
    | None -> []
    | Some (w, h, _) -> [ `Assoc [ ("kind", `String "canvas"); ("width", `Int w); ("height", `Int h); ("layers", `List !layers) ] ] in
  List.iter (fun (a, fields, _) ->
      origin [ "arrays"; a.aname ] a.adecl;
      List.iter (fun (f : field_decl) -> origin [ "arrays"; a.aname; "fields"; f.field ] f.fdecl) fields) groups;
  (`Assoc ([ ("version", `Int 1); ("backend", `String "symbolic"); ("state", `Assoc states); ("inputs", `Assoc !inputs);
             ("updates", `Assoc updates); ("outputs", `List outputs) ]
           @ if groups = [] then [] else [ ("arrays", `Assoc (List.map (fun (a, _, j) -> (a.aname, j)) groups)) ]),
   !origins)

let bindings source ir = fst (bindings_with_origins source ir)
