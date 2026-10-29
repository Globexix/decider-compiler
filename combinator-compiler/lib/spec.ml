open Error

type layer =
  | Rect of { name : string; x : string; y : string; width : string; height : string; enabled : string;
              icon : string option }
  | Point of { x : string; y : string; icon : string option }
  | Bar of { state : string; x : int; size : int; icon : string option }
  | Digits of { state : string; at : int * int; icon : string option }
  | Number of { state : string; at : int * int }
  | Mask of { state : string; at : int * int; width : int; height : int; values : int list; icon : string option }

type output =
  | Number_panel of { state : string; at : int * int }
  | Pixel_panel of { state : string; at : int * int }
  | Bar_panel of { state : string; at : int * int; length : int; size : int }
  | Port of { state : string }
  | Canvas of { width : int; height : int; layers : layer list }

type state = { name : string; min : int; max : int; initial : int }
type input = { input : string; signal : string }
type update = { target : string; func : string; args : string list }

type field = { field : string; scalar : [ `I32 | `Bool ]; offset : int; lo : int; hi : int }
type group = { group : string; struct_name : string; count : int; stride : int; fields : field list }

type t = {
  states : state list;
  inputs : input list;
  updates : update list;
  outputs : output list;
  start : string;
  symbolic : bool;
  quality : string;
  arrays : group list;
  raw : Yojson.Safe.t;
}

let state_of t name = List.find (fun s -> s.name = name) t.states
let domain s = List.init (s.max - s.min + 1) (fun i -> s.min + i)

let fail_at at = fail ~at:(Path at)

let fields at = function
  | `Assoc l -> l
  | _ -> fail_at at "expected an object"

let only at allowed json =
  let l = fields at json in
  List.iter (fun (k, _) ->
      if not (List.mem k allowed) then
        fail ~at:(Path (at @ [ k ])) ~help:(did_you_mean k allowed) "unknown field `%s`; expected %s" k (quoted allowed)) l;
  l

let int at = function `Int n -> n | _ -> fail_at at "expected an integer"
let str at = function `String s -> s | _ -> fail_at at "expected a string"
let list at = function `List l -> l | _ -> fail_at at "expected a list"

let get at key l = match List.assoc_opt key l with Some v -> v | None -> fail_at at "missing `%s`" key
let opt key l = List.assoc_opt key l

let pair at = function
  | `List [ `Int x; `Int y ] -> (x, y)
  | _ -> fail_at at "expected `[x, y]`"

let expr at = function
  | `Int n -> string_of_int n
  | `Bool b -> if b then "1" else "0"
  | `String s -> s
  | _ -> fail_at at "expected an integer or expression"

let signal at name =
  if not (Signals.known name) then
    fail ~at:(Path at) ~help:(did_you_mean name (Array.to_list Signals.catalog) @ [ "signals are Factorio identities such as `signal-A`, `iron-plate` or `signal-red`" ])
      "unknown signal `%s`" name;
  name

let icon at l = Option.map (fun v -> signal (at @ [ "icon" ]) (str (at @ [ "icon" ]) v)) (opt "icon" l)

let layer at index json =
  let at = at @ [ string_of_int index ] in
  let l = fields at json in
  let kind = str (at @ [ "kind" ]) (get at "kind" l) in
  let name = match opt "name" l with Some (`String n) -> n | _ -> kind in
  let kinds = [ "rect"; "point"; "bar"; "digits"; "number"; "mask" ] in
  let allowed = match kind with
    | "rect" -> [ "kind"; "name"; "x"; "y"; "width"; "height"; "enabled"; "icon" ]
    | "point" -> [ "kind"; "x"; "y"; "icon" ]
    | "bar" -> [ "kind"; "state"; "x"; "size"; "icon" ]
    | "digits" -> [ "kind"; "state"; "at"; "icon" ]
    | "number" -> [ "kind"; "state"; "at" ]
    | "mask" -> [ "kind"; "state"; "at"; "width"; "height"; "values"; "icon" ]
    | k -> fail ~at:(Path (at @ [ "kind" ])) ~help:(did_you_mean k kinds) "unknown layer kind `%s`; expected %s" k (quoted kinds)
  in
  let l = only at allowed json in
  let field key = at @ [ key ] in
  let e key = expr (field key) (get at key l) in
  let state () = str (field "state") (get at "state" l) in
  let at_ () = pair (field "at") (get at "at" l) in
  match kind with
  | "rect" ->
    Rect { name; x = e "x"; y = e "y"; width = e "width"; height = e "height";
           enabled = (match opt "enabled" l with Some v -> expr (field "enabled") v | None -> "1"); icon = icon at l }
  | "point" -> Point { x = e "x"; y = e "y"; icon = icon at l }
  | "bar" ->
    Bar { state = state (); x = int (field "x") (get at "x" l);
          size = (match opt "size" l with Some v -> int (field "size") v | None -> 1); icon = icon at l }
  | "digits" -> Digits { state = state (); at = at_ (); icon = icon at l }
  | "number" -> Number { state = state (); at = at_ () }
  | _ ->
    Mask { state = state (); at = at_ (); width = int (field "width") (get at "width" l);
           height = int (field "height") (get at "height" l);
           values = List.map (int (field "values")) (list (field "values") (get at "values" l)); icon = icon at l }

let output index json =
  let at = [ "outputs"; string_of_int index ] in
  let l = only at [ "kind"; "state"; "at"; "length"; "size"; "layers"; "width"; "height" ] json in
  let field key = at @ [ key ] in
  let state () = str (field "state") (get at "state" l) in
  let at_ () = pair (field "at") (get at "at" l) in
  let kinds = [ "number"; "pixel"; "bar"; "port"; "canvas" ] in
  match str (field "kind") (get at "kind" l) with
  | "number" -> Number_panel { state = state (); at = at_ () }
  | "pixel" -> Pixel_panel { state = state (); at = at_ () }
  | "bar" ->
    Bar_panel { state = state (); at = at_ (); length = int (field "length") (get at "length" l);
                size = (match opt "size" l with Some v -> int (field "size") v | None -> 1) }
  | "port" -> Port { state = state () }
  | "canvas" ->
    let w = int (field "width") (get at "width" l) and h = int (field "height") (get at "height" l) in
    if not (1 <= w && w <= 32 && 1 <= h && h <= 32) then
      fail_at at "canvas is %dx%d; a canvas holds at most 32x32 display panels" w h;
    if opt "at" l <> None then fail_at (field "at") "a canvas always begins at [0, 0]";
    Canvas { width = w; height = h; layers = List.mapi (layer (field "layers")) (list (field "layers") (get at "layers" l)) }
  | k -> fail ~at:(Path (field "kind")) ~help:(did_you_mean k kinds) "unknown output kind `%s`; expected %s" k (quoted kinds)

let group name json =
  let at = [ "arrays"; name ] in
  let l = fields at json in
  let field index f =
    let at = at @ [ "fields"; string_of_int index ] in
    let fl = fields at f in
    let fname = str (at @ [ "name" ]) (get at "name" fl) in
    let at = [ "arrays"; name; "fields"; fname ] in
    { field = fname;
      scalar = (match get at "type" fl with `String "i32" -> `I32 | `String "bool" -> `Bool
                                            | _ -> fail_at at "array struct fields must be `i32` or `bool`");
      offset = int at (get at "offset" fl);
      lo = int at (get at "min" fl); hi = int at (get at "max" fl) } in
  let count = int (at @ [ "count" ]) (get at "count" l) in
  if count < 1 || count > 32 then fail_at at "array capacity %d is outside 1..32" count;
  { group = name; struct_name = str (at @ [ "type" ]) (get at "type" l); count;
    stride = int (at @ [ "stride" ]) (get at "stride" l);
    fields = List.mapi field (list (at @ [ "fields" ]) (get at "fields" l)) }

let of_json (raw : Yojson.Safe.t) =
  let l = only [] [ "version"; "state"; "inputs"; "updates"; "outputs"; "start_signal"; "backend";
                    "register_quality"; "arrays" ] raw in
  if opt "version" l <> Some (`Int 1) then fail_at [ "version" ] "bindings must have `\"version\": 1`";
  let backend = match opt "backend" l with
    | None | Some (`String "table") -> false
    | Some (`String "symbolic") -> true
    | _ -> fail_at [ "backend" ] "expected `\"table\"` or `\"symbolic\"`" in
  let section key = match opt key l with Some v -> fields [ key ] v | None -> [] in
  let required key = match opt key l with Some v -> fields [ key ] v | None -> fail_at [] "missing `%s`" key in
  let states = List.map (fun (name, spec) ->
      let at = [ "state"; name ] in
      let s = only at [ "min"; "max"; "initial" ] spec in
      let n key = int (at @ [ key ]) (get at key s) in
      let lo = n "min" and hi = n "max" in
      let initial = if opt "initial" s = None then lo else n "initial" in
      if not (-(1 lsl 31) <= lo && hi < 1 lsl 31) then fail_at at "bounds %d..%d do not fit a 32-bit signal" lo hi;
      if lo > hi then fail_at at "empty range %d..%d" lo hi;
      if initial < lo || initial > hi then fail_at at "initial value %d is outside %d..%d" initial lo hi;
      if hi - lo >= 32 then
        fail ~at:(Path at) ~help:[ "each value of a state is one register pair; split wide values into several states" ]
          "`%s` has %d values (%d..%d); at most 32 are supported" name (hi - lo + 1) lo hi;
      { name; min = lo; max = hi; initial }) (required "state") in
  let inputs = List.map (fun (name, spec) ->
      let at = [ "inputs"; name ] in
      let s = only at [ "signal"; "type" ] spec in
      (match opt "type" s with
       | None | Some (`String "bool") -> ()
       | _ -> fail_at (at @ [ "type" ]) "only Boolean inputs are supported; any nonzero count is true");
      { input = name; signal = signal (at @ [ "signal" ]) (str (at @ [ "signal" ]) (get at "signal" s)) }) (section "inputs") in
  let updates = List.map (fun (target, spec) ->
      let at = [ "updates"; target ] in
      let s = only at [ "function"; "args" ] spec in
      { target; func = str (at @ [ "function" ]) (get at "function" s);
        args = List.map (str (at @ [ "args" ])) (list (at @ [ "args" ]) (get at "args" s)) }) (required "updates") in
  let arrays = List.map (fun (name, g) -> group name g) (section "arrays") in
  let start = match opt "start_signal" l with Some v -> str [ "start_signal" ] v | None -> "signal-Z" in
  let quality = match opt "register_quality" l with Some v -> str [ "register_quality" ] v | None -> "auto" in
  let outputs = match opt "outputs" l with Some v -> List.mapi output (list [ "outputs" ] v) | None -> [] in
  if (not backend) && arrays <> [] then fail_at [ "arrays" ] "arrays require `\"backend\": \"symbolic\"`";
  let state_names = List.map (fun s -> s.name) states in
  let input_names = List.map (fun i -> i.input) inputs in
  if states = [] then fail_at [ "state" ] "no states are declared";
  List.iter (fun s ->
      if not (List.exists (fun u -> u.target = s.name) updates) then fail_at [ "state"; s.name ] "`%s` has no update function" s.name)
    states;
  List.iter (fun u ->
      if not (List.mem u.target state_names) then
        fail ~at:(Path [ "updates"; u.target ]) ~help:(did_you_mean u.target state_names) "update for `%s`, which is not a declared state" u.target)
    updates;
  List.iter (fun i -> if List.mem i.input state_names then fail_at [ "inputs"; i.input ] "`%s` is both a state and an input" i.input) inputs;
  let max_states = if backend then 128 else 8 in
  if List.length states > max_states then
    fail_at [ "state" ] "%d states declared; at most %d are supported%s" (List.length states) max_states
      (if backend then "" else " by the table backend");
  if List.length inputs > 8 then fail_at [ "inputs" ] "%d inputs declared; at most 8 are supported" (List.length inputs);
  if not (List.mem start Signals.virtual_signals) then
    fail_at [ "start_signal" ] "start signal `%s` must be a standard virtual signal" start;
  ignore (List.fold_left (fun seen i ->
      (match List.assoc_opt i.signal seen with
       | Some other ->
         fail ~at:(Path [ "inputs"; i.input; "signal" ]) ~notes:[ (Some (Path [ "inputs"; other ]), "also used by `" ^ other ^ "`") ]
           "inputs `%s` and `%s` both use `%s`" other i.input i.signal
       | None -> ());
      if i.signal = start then
        fail_at [ "inputs"; i.input; "signal" ] "`%s` is the start signal; pick another signal for `%s`" start i.input;
      (i.signal, i.input) :: seen) [] inputs);
  if quality <> "auto" && not (List.mem quality Signals.qualities) then
    fail ~at:(Path [ "register_quality" ]) ~help:(did_you_mean quality Signals.qualities) "unknown quality `%s`" quality;
  let group_names = List.map (fun g -> g.group) arrays in
  List.iter (fun u ->
      List.iter (fun a ->
          if not (List.mem a state_names || List.mem a input_names || List.mem a group_names) then
            fail ~at:(Path [ "updates"; u.target; "args" ]) ~help:(did_you_mean a (state_names @ input_names @ group_names))
              "argument `%s` of `%s` is not a state, input or array" a u.func) u.args) updates;
  { states; inputs; updates; outputs; start; symbolic = backend; quality; arrays; raw }

let raw_field t key = match t.raw with `Assoc l -> List.assoc_opt key l | _ -> None
