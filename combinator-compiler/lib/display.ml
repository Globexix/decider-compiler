open Error

type key = State of string * int | Derived of string
type test = Visible of key | Always
type record = { test : test; icon : string option }

type derived = { name : string; initial : bool; current : Bdd.t; next : Bdd.t; alias : (string * int) option }

let digits = [|
  [| "111"; "101"; "101"; "101"; "111" |]; [| "010"; "110"; "010"; "010"; "111" |];
  [| "111"; "001"; "111"; "100"; "111" |]; [| "111"; "001"; "111"; "001"; "111" |];
  [| "101"; "101"; "111"; "001"; "001" |]; [| "111"; "100"; "111"; "001"; "111" |];
  [| "111"; "100"; "111"; "101"; "111" |]; [| "111"; "001"; "010"; "010"; "010" |];
  [| "111"; "101"; "111"; "101"; "111" |]; [| "111"; "101"; "111"; "001"; "111" |] |]

let glyph_pixel value ~dx ~dy = digits.(value).(dy).[dx] = '1'

let white = "signal-white"
let state_names (spec : Spec.t) = List.map (fun (s : Spec.state) -> s.name) spec.states

let lower_canvas (spec : Spec.t) (output : Spec.output) =
  match output with
  | Canvas { width = w; height = h; layers }
    when List.exists (function Spec.Rect _ -> true | _ -> false) layers ->
    let icon_of = function
      | Spec.Rect r -> r.icon | Point p -> p.icon | Bar b -> b.icon | Digits d -> d.icon | Mask m -> m.icon | Number _ -> None in
    let icons = List.sort_uniq compare (List.map (fun l -> Option.value (icon_of l) ~default:white) layers) in
    if List.length icons <> 1 then output
    else begin
      let names = state_names spec in
      let state name = List.find_opt (fun (s : Spec.state) -> s.name = name) spec.states in
      let points = ref 0 in
      let exception Keep in
      try
        let lowered = List.filter_map (function
            | Spec.Rect r ->
              let e text = Expr.parse ~names text in
              let ex = e r.x and ey = e r.y and ew = e r.width and eh = e r.height and en = e r.enabled in
              let c = Expr.constant in
              let enabled_on = match c en with Some v -> v <> 0 | None -> false in
              (match c ex, c ey, c ew, c eh, state r.x, state r.y with
               | _, _, Some 1, Some 1, Some sx, Some sy when enabled_on ->
                 incr points;
                 if !points > 1 || not (0 <= sx.min && sx.max < w && 0 <= sy.min && sy.max < h) then raise Keep;
                 Some (Spec.Point { x = r.x; y = r.y; icon = r.icon })
               | Some x, _, Some 1, _, _, Some sy when enabled_on && (match c eh with Some n -> n > 0 | None -> false) ->
                 let size = Option.get (c eh) in
                 if not (0 <= x && x < w && 0 <= sy.min && sy.max + size <= h) then raise Keep;
                 Some (Spec.Bar { state = r.y; x; size; icon = r.icon })
               | Some x, Some y, Some width, Some height, _, _ when List.length (Expr.refs en) = 1 ->
                 if not (0 <= x && 0 <= y && 1 <= width && width <= w && 1 <= height && height <= h
                         && x + width <= w && y + height <= h) then raise Keep;
                 let sname = List.hd (Expr.refs en) in
                 let s = Option.get (state sname) in
                 let values = List.filter (fun v -> Expr.eval (fun _ -> v) en <> 0) (Spec.domain s) in
                 if values = [] then None
                 else if List.length values = s.max - s.min + 1 then raise Keep
                 else Some (Spec.Mask { state = sname; at = (x, y); width; height; values; icon = r.icon })
               | _ -> raise Keep)
            | _ -> raise Keep) layers in
        Canvas { width = w; height = h; layers = lowered }
      with Keep -> output
    end
  | _ -> output

let canvas (spec : Spec.t) ~output ~width:w ~height:h (layers : Spec.layer list) =
  let layer_path index = Path [ "outputs"; string_of_int output; "layers"; string_of_int index ] in
  let names = state_names spec in
  let domain name = Spec.domain (Spec.state_of spec name) in
  let points = List.filter_map (function Spec.Point { x; y; icon } -> Some (x, y, icon) | _ -> None) layers in
  if List.length points > 1 then
    fail ~at:(Path [ "outputs"; string_of_int output ]) "a canvas without rectangles supports at most one moving point";
  List.iteri (fun index layer ->
      let check field name =
        if not (List.mem name names) then
          fail ~at:(Path [ "outputs"; string_of_int output; "layers"; string_of_int index; field ]) ~help:(did_you_mean name names)
            "`%s` is not a declared state" name in
      match layer with
      | Spec.Point p -> check "x" p.x; check "y" p.y
      | Bar b -> check "state" b.state
      | Digits d -> check "state" d.state
      | Number n -> check "state" n.state
      | Mask m -> check "state" m.state
      | Rect _ -> fail ~at:(layer_path index) "unsupported layer kind `rect`") layers;
  let visible state v icon = { test = Visible (State (state, v)); icon } in
  let pixels = ref [] in
  for x = 0 to w - 1 do
    for y = 0 to h - 1 do
      let records = List.concat (List.mapi (fun index layer -> locate (layer_path index) @@ fun () ->
          let values, state, icon = match layer with
            | Spec.Point _ | Rect _ -> ([], "", fun _ -> None)
            | Bar b ->
              if not (0 <= b.x && b.x < w) then fail "bar column %d is outside the %d-wide canvas" b.x w;
              if not (1 <= b.size && b.size <= h) then fail "bar size %d is outside 1..%d" b.size h;
              let d = domain b.state in
              if List.hd d < 0 || List.nth d (List.length d - 1) + b.size > h then
                fail "at `%s` = %d the bar extends past the bottom of the %d-high canvas" b.state (List.nth d (List.length d - 1)) h;
              ((if x = b.x then List.filter (fun v -> v <= y && y < v + b.size) d else []), b.state,
               fun _ -> Some (Option.value b.icon ~default:white))
            | Mask m ->
              let dx, dy = m.at in
              if not (0 <= dx && 0 <= dy && 1 <= m.width && m.width <= w && 1 <= m.height && m.height <= h
                      && dx + m.width <= w && dy + m.height <= h) then fail "mask does not fit inside the %dx%d canvas" w h;
              if not (List.for_all (fun v -> List.mem v (domain m.state)) m.values) then fail "mask values must be values of `%s`" m.state;
              ((if dx <= x && x < dx + m.width && dy <= y && y < dy + m.height then m.values else []), m.state,
               fun _ -> Some (Option.value m.icon ~default:white))
            | Number n ->
              let dx, dy = n.at in
              if not (0 <= dx && dx < w && 0 <= dy && dy < h) then fail "number at %d,%d is outside the %dx%d canvas" dx dy w h;
              if not (List.for_all (fun v -> 0 <= v && v <= 9) (domain n.state)) then fail "`@number` shows one digit, but `%s` is not within 0..9" n.state;
              ((if (x, y) = (dx, dy) then domain n.state else []), n.state, fun v -> Some (Printf.sprintf "signal-%d" v))
            | Digits d ->
              let dx, dy = d.at in
              if not (0 <= dx && dx + 3 <= w && 0 <= dy && dy + 5 <= h) then fail "3x5 digits at %d,%d do not fit the %dx%d canvas" dx dy w h;
              if not (List.for_all (fun v -> 0 <= v && v <= 9) (domain d.state)) then fail "`@digits` shows one digit, but `%s` is not within 0..9" d.state;
              ((if dx <= x && x < dx + 3 && dy <= y && y < dy + 5 then
                  List.filter (fun v -> glyph_pixel v ~dx:(x - dx) ~dy:(y - dy)) (domain d.state) else []),
               d.state, fun _ -> Some (Option.value d.icon ~default:white)) in
          List.map (fun v -> visible state v (icon v)) values) layers) in
      let point = match points with
        | [] -> []
        | (px, py, picon) :: _ ->
          let dx = domain px and dy = domain py in
          if List.hd dx < 0 || List.nth dx (List.length dx - 1) >= w || List.hd dy < 0 || List.nth dy (List.length dy - 1) >= h then
            fail ~at:(Path [ "outputs"; string_of_int output ]) "point `%s,%s` can leave the %dx%d canvas" px py w h;
          List.filter_map (fun v -> if v <> x then Some (visible px v None) else None) dx
          @ (if List.mem y dy then [ visible py y (Some (Option.value picon ~default:white)) ] else []) in
      pixels := ((x, y), records @ point) :: !pixels
    done
  done;
  List.rev !pixels

let adapter (spec : Spec.t) (output : Spec.output) =
  let cells state cells =
    let s = Spec.state_of spec state in
    List.map (fun (x, y, icon_for) ->
        let records = List.filter_map (fun v ->
            if v = s.initial then None else Some { test = Visible (State (state, v)); icon = icon_for v }) (Spec.domain s) in
        ((x, y), records @ [ { test = Always; icon = icon_for s.initial } ])) cells in
  let known state = if not (List.mem state (state_names spec)) then fail "output refers to unknown state %s" state in
  let at (x, y) = if x < 0 || y < 0 then fail "output positions must be nonnegative integer cells" in
  match output with
  | Spec.Port { state } -> known state; []
  | Number_panel { state; at = (x, y) } ->
    known state; at (x, y);
    if not (List.for_all (fun v -> 0 <= v && v <= 9) (Spec.domain (Spec.state_of spec state))) then
      fail "number adapter requires a 0..9 domain";
    cells state [ (x, y, fun v -> Some (Printf.sprintf "signal-%d" v)) ]
  | Pixel_panel { state; at = (x, y) } ->
    known state; at (x, y);
    if not (List.for_all (fun v -> v = 0 || v = 1) (Spec.domain (Spec.state_of spec state))) then
      fail "pixel adapter requires Boolean state";
    cells state [ (x, y, fun v -> if v <> 0 then Some white else None) ]
  | Bar_panel { state; at = (x, y); length; size } ->
    known state; at (x, y);
    if not (1 <= size && size <= length && length <= 32) then fail "invalid bar length/size";
    let s = Spec.state_of spec state in
    if s.min < 0 || s.max + size > length then fail "bar position is outside its declared length";
    cells state (List.init length (fun row -> (x, y + row, fun v -> if v <= row && row < v + size then Some white else None)))
  | Canvas _ -> assert false

type geometry = { x : Bitvec.t; y : Bitvec.t; width : Bitvec.t; height : Bitvec.t; enabled : Bitvec.t }
type exprs = { ex : Expr.t; ey : Expr.t; ew : Expr.t; eh : Expr.t; en : Expr.t }

type prepared =
  | Shape of { icon : string; exprs : exprs; cur : geometry; nxt : geometry }
  | Glyph of { number : bool; state : string; at : int * int; icon : string }

let rec until_always = function
  | ({ test = Always; _ } as r) :: _ -> [ r ]
  | r :: rest -> r :: until_always rest
  | [] -> []

let cmp pred a n = Bitvec.compare pred a (Bitvec.const n)

let factor_geometry (model : Model.t) prepared constants height =
  let constant name = List.assoc_opt name constants in
  let not_constant = List.filter (fun r -> constant r = None) in
  let eval e driver value = Expr.eval (fun r -> if r = driver then value else Option.get (constant r)) e in
  let domain name = Model.values (Model.domain model name) in
  let groups = Hashtbl.create 8 and group_order = ref [] and candidates = Hashtbl.create 8 and horizontal = Hashtbl.create 8 in
  List.iteri (fun index p ->
      match p with
      | Glyph _ -> ()
      | Shape { exprs = e; cur; nxt; _ } ->
        match not_constant (List.sort_uniq compare (Expr.refs e.ey @ Expr.refs e.eh)) with
        | [ driver ] when not (List.mem driver (Expr.refs e.ex @ Expr.refs e.ew @ Expr.refs e.en)) ->
          let rows = Array.make height [] in
          List.iter (fun v ->
              let top = eval e.ey driver v in
              let bottom = Expr.i32 (top + eval e.eh driver v) in
              for y = 0 to height - 1 do if top <= y && y < bottom then rows.(y) <- rows.(y) @ [ v ] done) (domain driver);
          let key = (driver, [ cur.x; cur.width; cur.enabled; nxt.x; nxt.width; nxt.enabled ]) in
          if not (Hashtbl.mem groups key) then group_order := key :: !group_order;
          Hashtbl.replace groups key ((try Hashtbl.find groups key with Not_found -> []) @ [ (index, rows) ]);
          Hashtbl.replace candidates index (driver, rows);
          (match not_constant (List.sort_uniq compare (Expr.refs e.ex @ Expr.refs e.ew)) with
           | [ hdriver ] ->
             let columns = List.map (fun v ->
                 let left = eval e.ex hdriver v in
                 (v, left, Expr.i32 (left + eval e.ew hdriver v))) (domain hdriver) in
             Hashtbl.replace horizontal index (hdriver, columns)
           | _ -> ())
        | _ -> ()) prepared;
  let result = Hashtbl.create 8 in
  List.iter (fun ((driver, _) as key) ->
      let entries = Hashtbl.find groups key in
      let patterns = List.sort_uniq compare (List.concat_map (fun (_, rows) -> List.filter (( <> ) []) (Array.to_list rows)) entries) in
      if List.length patterns > List.length (domain driver) + 1 then
        List.iter (fun (index, _) -> Hashtbl.replace result index (Hashtbl.find candidates index)) entries)
    (List.rev !group_order);
  let row_costs = Array.make height 0 and equality_costs = Array.make height 0 in
  List.iteri (fun index p ->
      match Hashtbl.find_opt result index, p with
      | Some (driver, rows), _ ->
        let size = List.length (domain driver) in
        let multiplicity = match Hashtbl.find_opt horizontal index with
          | None -> 1
          | Some (_, columns) ->
            List.fold_left max 0 (List.init 32 (fun x ->
                List.length (List.filter (fun (_, l, r) -> l <= x && x < r) columns))) in
        Array.iteri (fun y row ->
            let cost = 2 * (if List.length row = size then 1 else List.length row) in
            row_costs.(y) <- row_costs.(y) + cost;
            equality_costs.(y) <- equality_costs.(y) + cost * multiplicity) rows
      | None, Glyph { state; _ } ->
        let cost = 2 * List.length (domain state) in
        for y = 0 to height - 1 do row_costs.(y) <- row_costs.(y) + cost; equality_costs.(y) <- equality_costs.(y) + cost done
      | None, Shape _ ->
        for y = 0 to height - 1 do row_costs.(y) <- row_costs.(y) + 2; equality_costs.(y) <- equality_costs.(y) + 2 done)
    prepared;
  let max_of a = Array.fold_left max 0 a in
  if max_of row_costs > 100 then Hashtbl.create 0
  else begin
    let out = Hashtbl.create 8 in
    Hashtbl.iter (fun index (driver, rows) ->
        let columns = if max_of equality_costs <= 100 then Hashtbl.find_opt horizontal index else None in
        Hashtbl.replace out index (driver, rows, columns)) result;
    out
  end

let plan (model : Model.t) ~output ~constants ~factor ~width:w ~height:h (layers : Spec.layer list) =
  let prefix = string_of_int output in
  let spec = model.spec in
  let names = state_names spec in
  let constant_bits = Model.constant_assignment model constants in
  let fix b = if constants = [] then b else Bdd.restrict b constant_bits in
  let domain name = Model.values (Model.domain model name) in
  let prepared = List.mapi (fun index layer ->
      let kind, label = match layer with
        | Spec.Rect r -> ("rect", r.name) | Point _ -> ("point", "point") | Bar _ -> ("bar", "bar")
        | Digits _ -> ("digits", "digits") | Number _ -> ("number", "number") | Mask _ -> ("mask", "mask") in
      ignore label;
      let at = [ "outputs"; string_of_int output; "layers"; string_of_int index ] in
      locate (Path at) (fun () ->
          let shape icon x y width height enabled =
            let p key text = locate (Path (at @ [ key ])) (fun () -> Expr.parse ~names text) in
            let exprs = { ex = p "x" x; ey = p "y" y; ew = p "width" width; eh = p "height" height; en = p "enabled" enabled } in
            let vector env =
              let s e = Expr.symbolic env e in
              { x = s exprs.ex; y = s exprs.ey; width = s exprs.ew; height = s exprs.eh; enabled = s exprs.en } in
            let cur = vector (Model.value model) and nxt = vector (Model.next model) in
            List.iter (fun (axis, v) ->
                let ok = Bdd.and_ (cmp Sge v 0) (cmp Sle v 32) in
                if Bdd.and_ model.valid (Bdd.not_ ok) <> Bdd.zero then
                  fail ~at:(Path (at @ [ axis ])) "%s must stay within 0..32 for every reachable state" axis) [ ("width", cur.width); ("height", cur.height) ];
            let restrict g = { x = Array.map fix g.x; y = Array.map fix g.y; width = Array.map fix g.width;
                               height = Array.map fix g.height; enabled = Array.map fix g.enabled } in
            Shape { icon = Option.value icon ~default:white; exprs; cur = restrict cur; nxt = restrict nxt } in
          let glyph number state (x, y) icon =
            if not (List.mem state names) then
              fail ~at:(Path (at @ [ "state" ])) ~help:(did_you_mean state names) "`%s` is not a declared state" state;
            if not (List.for_all (fun v -> 0 <= v && v <= 9) (domain state)) then
              fail ~at:(Path (at @ [ "state" ])) "`@%s` shows one digit, but `%s` is not within 0..9" kind state;
            let gw, gh = if number then (1, 1) else (3, 5) in
            if not (0 <= x && x <= w - gw && 0 <= y && y <= h - gh) then
              fail ~at:(Path (at @ [ "at" ])) "%dx%d %s at %d,%d does not fit the %dx%d canvas" gw gh kind x y w h;
            Glyph { number; state; at = (x, y); icon = Option.value icon ~default:white } in
          match layer with
          | Spec.Rect r -> shape r.icon r.x r.y r.width r.height r.enabled
          | Point p -> shape p.icon p.x p.y "1" "1" "1"
          | Bar b -> shape b.icon (string_of_int b.x) b.state "1" (string_of_int b.size) "1"
          | Digits d -> glyph false d.state d.at d.icon
          | Number n -> glyph true n.state n.at None
          | Mask _ -> fail "`%s` layers need a canvas without rectangles" kind)) layers in
  let prepared_a = Array.of_list prepared in
  let factored = if factor then factor_geometry model prepared constants h else Hashtbl.create 0 in
  let eq_value vec v = fix (Bitvec.eq vec (Bitvec.const v)) in
  let pair_of name v = (eq_value (Model.value model name) v, eq_value (Model.next model name) v) in
  let horizontal = Hashtbl.create 64 and choices = Hashtbl.create 64 in
  Hashtbl.iter (fun index (driver, _, columns) ->
      match prepared_a.(index) with
      | Glyph _ -> ()
      | Shape { cur; nxt; _ } ->
        let enabled g = Bdd.not_ (cmp Eq g.enabled 0) in
        for x = 0 to w - 1 do
          let roots = match columns with
            | Some (hdriver, columns) ->
              List.filter_map (fun (v, left, right) ->
                  if left <= x && x < right then
                    let c, n = pair_of hdriver v in
                    Some (Bdd.and_ (enabled cur) c, Bdd.and_ (enabled nxt) n)
                  else None) columns
            | None ->
              let cover g = Bdd.conj [ enabled g; cmp Sle g.x x; cmp Sgt (Bitvec.add g.x g.width) x ] in
              [ (cover cur, cover nxt) ] in
          Hashtbl.replace horizontal (index, x) roots
        done;
        List.iter (fun v -> Hashtbl.replace choices (driver, v) (pair_of driver v)) (domain driver)) factored;
  let initial = List.concat_map (fun (s : Spec.state) -> Model.assignment (Model.domain model s.name) s.initial) spec.states in
  let aliases = Hashtbl.create 64 in
  if factor then
    List.iter (fun (s : Spec.state) ->
        if not (List.mem_assoc s.name constants) then
          List.iter (fun v ->
              let key = pair_of s.name v in
              if not (Hashtbl.mem aliases key) then Hashtbl.replace aliases key (s.name, v)) (domain s.name)) spec.states;
  let flags = ref [] and by_root = Hashtbl.create 64 in
  let predicate (current, next) =
    if current = Bdd.zero then None
    else if current = Bdd.one then Some Always
    else match Hashtbl.find_opt by_root (current, next) with
      | Some name -> Some (Visible (Derived name))
      | None ->
        let name = Printf.sprintf "$display%s_%d" prefix (List.length !flags) in
        let init = Bdd.restrict current initial in
        if not (Bdd.is_const init) then fail "display predicate unexpectedly depends on external inputs";
        flags := { name; initial = init = Bdd.one; current; next; alias = Hashtbl.find_opt aliases (current, next) } :: !flags;
        Hashtbl.replace by_root (current, next) name;
        Some (Visible (Derived name)) in
  let pixels = ref [] in
  for x = 0 to w - 1 do
    for y = 0 to h - 1 do
      let records = ref [] in
      let add roots icon = match predicate roots with Some test -> records := { test; icon = Some icon } :: !records | None -> () in
      for index = Array.length prepared_a - 1 downto 0 do
        match prepared_a.(index), Hashtbl.find_opt factored index with
        | Shape { icon; _ }, Some (driver, rows, _) ->
          let allowed = rows.(y) in
          List.iter (fun (c, n) ->
              if List.length allowed = List.length (domain driver) then add (c, n) icon
              else List.iter (fun v ->
                  let cc, cn = Hashtbl.find choices (driver, v) in
                  add (Bdd.and_ c cc, Bdd.and_ n cn) icon) allowed) (Hashtbl.find horizontal (index, x))
        | Shape { icon; cur; nxt; _ }, None ->
          let cover g = Bdd.conj [ Bdd.not_ (cmp Eq g.enabled 0); cmp Sle g.x x; cmp Sgt (Bitvec.add g.x g.width) x;
                                   cmp Sle g.y y; cmp Sgt (Bitvec.add g.y g.height) y ] in
          add (cover cur, cover nxt) icon
        | Glyph { number; state; at = (dx, dy); icon }, _ ->
          let inside = if number then (x, y) = (dx, dy) else dx <= x && x < dx + 3 && dy <= y && y < dy + 5 in
          if inside then
            List.iter (fun v ->
                if number || glyph_pixel v ~dx:(x - dx) ~dy:(y - dy) then
                  add (pair_of state v) (if number then Printf.sprintf "signal-%d" v else icon)) (domain state)
      done;
      pixels := ((x, y), until_always (List.rev !records)) :: !pixels
    done
  done;
  (List.rev !flags, List.rev !pixels)
