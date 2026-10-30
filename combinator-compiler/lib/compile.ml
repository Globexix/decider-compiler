open Error
open Circuit

type result = {
  project : Yojson.Safe.t;
  manifest : Yojson.Safe.t;
  rows : Yojson.Safe.t;
  blueprint : Yojson.Safe.t;
  lanes : int;
  conditions : int;
  ms_per_tick : float;
  row_count : int;
  latches : Model.latch list;
}

let big_product factors =
  let mul digits k =
    let carry = ref 0 in
    let out = List.map (fun d -> let v = d * k + !carry in carry := v / 10; v mod 10) digits in
    let rec rest c = if c = 0 then [] else (c mod 10) :: rest (c / 10) in
    out @ rest !carry in
  let digits = List.fold_left mul [ 1 ] factors in
  String.concat "" (List.rev_map string_of_int digits)

let fits_int s = String.length s < 18

let rec product = function
  | [] -> [ [] ]
  | (name, values) :: rest ->
    let tails = product rest in
    List.concat_map (fun v -> List.map (fun t -> (name, v) :: t) tails) values

let reachable_box (model : Model.t) ~care ~constants =
  let states = List.filter (fun (s : Spec.state) -> not (List.mem_assoc s.name constants)) model.spec.states in
  let sets = Hashtbl.create 64 in
  List.iter (fun (s : Spec.state) -> Hashtbl.replace sets s.name [ s.initial ]) states;
  let box () =
    Bdd.conj (care :: List.map (fun (s : Spec.state) ->
        Cover.domain_bdd (Model.domain model s.name) (Hashtbl.find sets s.name)) states) in
  let bits = Model.constant_assignment model constants in
  Bdd.stage := "finding the reachable range of every state";
  let rec grow () =
    let b = box () in
    let changed = ref false in
    List.iter (fun (s : Spec.state) ->
        let next = Model.next model s.name in
        List.iter (fun v ->
            let known = Hashtbl.find sets s.name in
            if not (List.mem v known) then
              let hit = Bdd.and_ b (Bdd.restrict (Bitvec.eq next (Bitvec.const v)) bits) in
              if hit <> Bdd.zero then (Hashtbl.replace sets s.name (v :: known); changed := true))
          (Spec.domain s)) states;
    if !changed then grow () else b in
  grow ()

let display_cells (spec : Spec.t) model ~optimize ~constants outputs =
  let derived = ref [] and cells = ref [] in
  let owner = Hashtbl.create 64 in
  let place ~index (cell, records) =
    let x, y = cell in
    let at = Path [ "outputs"; string_of_int index ] in
    (match Hashtbl.find_opt owner cell with
     | Some other -> fail ~at ~notes:[ (Some (Path [ "outputs"; string_of_int other ]), "the other output") ] "outputs overlap at panel %d,%d" x y
     | None -> Hashtbl.replace owner cell index);
    if x >= 32 || y >= 32 then fail ~at "panel %d,%d is outside the 32x32 display area" x y;
    cells := !cells @ [ (cell, records) ] in
  List.iteri (fun index (output : Spec.output) ->
      match output with
      | Canvas { width; height; layers } ->
        if List.exists (function Spec.Rect _ -> true | _ -> false) layers && spec.symbolic then begin
          Bdd.stage := "working out which panel cells each `@rect` can light";
          let flags, pixels = Display.plan model ~output:index ~constants ~factor:optimize ~width ~height layers in
          derived := !derived @ flags;
          List.iter (place ~index) pixels
        end else begin
          if not spec.symbolic then fail ~at:(Path [ "backend" ]) "canvas outputs require `\"backend\": \"symbolic\"`";
          List.iter (place ~index) (Display.canvas spec ~output:index ~width ~height layers)
        end
      | _ -> List.iter (place ~index) (locate (Path [ "outputs"; string_of_int index ]) (fun () -> Display.adapter spec output))) outputs;
  (!derived, !cells)

let drawn_states outputs =
  List.fold_left (fun (canvas, direct) (o : Spec.output) ->
      match o with
      | Canvas { layers; _ } when not (List.exists (function Spec.Rect _ -> true | _ -> false) layers) ->
        (List.concat_map (function
             | Spec.Point p -> [ p.x; p.y ]
             | Bar { state; _ } | Digits { state; _ } | Number { state; _ } | Mask { state; _ } -> [ state ]
             | Rect _ -> []) layers @ canvas, direct)
      | Canvas _ -> (canvas, direct)
      | Number_panel { state; _ } | Pixel_panel { state; _ } | Bar_panel { state; _ } | Port { state } -> (canvas, state :: direct))
    ([], []) outputs

let display_parameters l (derived : Display.derived list) records =
  let flag_for = function
    | Display.Derived name as key ->
      (match (List.find (fun (d : Display.derived) -> d.name = name) derived).alias with
       | Some (s, v) -> l.flag_of (Display.State (s, v))
       | None -> l.flag_of key)
    | key -> l.flag_of key in
  let with_icon condition icon =
    `Assoc ([ ("condition", condition) ] @ match icon with Some i -> [ ("icon", Emit.signal i) ] | None -> []) in
  let condition signal cmp constant =
    `Assoc [ ("first_signal", Emit.signal signal); ("comparator", `String cmp); ("constant", `Int constant) ] in
  List.concat_map (fun (r : Display.record) ->
      match r.test with
      | Always -> [ with_icon (condition l.start ">=" 0) r.icon ]
      | Visible key -> List.map (fun (s, v) -> with_icon (condition s "=" v) r.icon) (visible l (flag_for key))) records

let compile ?(optimize = true) ?(name = "program") ?(min_ups = 20.) (program : Ir.program) (config : Yojson.Safe.t) =
  if program.has_globals then
    fail ~help:[ "pass state to update functions as parameters, bound by `@state` declarations" ] "global variables are not supported";
  let spec = Spec.of_json config in
  let symbolic = spec.symbolic in
  let sizes = List.map (fun (s : Spec.state) -> s.max - s.min + 1) spec.states @ List.map (fun _ -> 2) spec.inputs in
  let cases = big_product sizes in
  if (not symbolic) && (not (fits_int cases) || int_of_string cases > 4096) then
    fail ~at:(Path [ "backend" ]) ~help:[ "use `\"backend\": \"symbolic\"`" ] "the transition table would have %s rows; the table backend allows 4096" cases;
  let latch = symbolic && optimize && Sys.getenv_opt "FAS_FACTORIO_NO_LATCH" <> Some "1" in
  let model = Model.create ~latch spec program in
  let spec = model.spec in
  let constants = if symbolic && optimize && spec.arrays <> [] then Model.array_constants model else [] in
  let bits = Model.constant_assignment model constants in
  let fix b = if bits = [] then b else Bdd.restrict b bits in
  let outputs = if optimize then List.map (Display.lower_canvas spec) spec.outputs else spec.outputs in
  let derived, cells = display_cells spec model ~optimize ~constants outputs in
  let canvas_states, direct_states = drawn_states outputs in
  let aliases = List.filter_map (fun (d : Display.derived) -> d.alias) derived in
  let keys =
    List.concat_map (fun (s : Spec.state) ->
        if List.mem_assoc s.name constants && not (List.mem s.name canvas_states || List.mem s.name direct_states) then []
        else
          List.filter_map (fun v ->
              if List.mem s.name canvas_states || List.mem (s.name, v) aliases || v <> s.initial then
                Some (Display.State (s.name, v), v = s.initial)
              else None) (Spec.domain s)) spec.states
    @ List.filter_map (fun (d : Display.derived) ->
        if d.alias = None then Some (Display.Derived d.name, d.initial) else None) derived in
  let needed = 1 + 2 * List.length keys in
  let budget = if symbolic then if derived <> [] then 8192 else 1024 else 64 in
  let lanes = let rec up n = if n >= needed then n else up (2 * n) in up 1 in
  if lanes > budget then
    fail ~help:[ "narrow state ranges or remove states; every value of every state needs a register pair" ]
      "the machine needs %d register lanes; the budget is %d" lanes budget;
  let l = allocate spec keys in
  if Array.length l.names + 1 > 1_000_000 then fail "generated output count exceeds verified game budget";
  let care = fix model.valid in
  let care = if optimize then reachable_box model ~care ~constants else care in
  let targets = List.map (fun f ->
      let next, current = match f.key with
        | Display.State (s, v) -> (fix (Model.flag model s v), None)
        | Derived name ->
          let d = List.find (fun (d : Display.derived) -> d.name = name) derived in
          (d.next, Some d.current) in
      let flip b = if f.inverted then Bdd.not_ b else b in
      { flag = f; next = flip next; current = Option.map flip current }) l.flags in
  (* Planning leaves most of its nodes dead; collect them whenever the live count has doubled. *)
  let roots () =
    let vectors table = Hashtbl.fold (fun _ v acc -> Array.to_list v @ acc) table [] in
    (model.valid :: care :: vectors model.values) @ vectors model.next
    @ List.concat_map (fun t -> t.next :: Option.to_list t.current) targets
    @ List.concat_map (fun (d : Display.derived) -> [ d.current; d.next ]) derived in
  let kept = ref (Bdd.size ()) in
  let plans = List.map (fun t ->
      if Bdd.size () > 2 * !kept + 1_000_000 then (Bdd.collect (roots ()); kept := Bdd.size ());
      Bdd.stage := (match t.flag.key with
          | Display.State (s, v) -> Printf.sprintf "building the conditions for `%s` = %d" s v
          | Derived n -> Printf.sprintf "building the conditions for display cell `%s`" n);
      (t.flag, plan_target ~optimize l spec model ~care t)) targets in
  List.iter (fun ((f : flag), (p : plan)) -> f.pass_on <- p.pass_on) plans;
  if Sys.getenv_opt "FAS_FACTORIO_CHECK" = Some "1" then
    List.iter2 (fun t (_, p) ->
        let wrong = Bdd.and_ care (Bdd.xor (plan_meaning l spec t p) t.next) in
        if wrong <> Bdd.zero then
          failwith (Printf.sprintf "internal: plan for %s differs from its target"
                      (match t.flag.key with State (s, v) -> Printf.sprintf "%s=%d" s v | Derived n -> n))) targets plans;
  let limit = if symbolic then 1_000_000 else 100_000 in
  let count = ref 0 and seen = Hashtbl.create 4096 and groups = ref [] in
  let emit group =
    if not (Hashtbl.mem seen group) then begin
      Hashtbl.replace seen group ();
      count := !count + List.length group;
      if !count > limit then
        fail ~notes:[ (None, Printf.sprintf "the compiler stopped while %s" !Bdd.stage) ]
          ~help:[ "narrow state ranges, or make updates depend on fewer states" ]
          "the decider would need more than %d conditions" limit;
      groups := group :: !groups
    end in
  List.iter emit (fixed_groups l);
  List.iter (fun ((f : flag), p) ->
      Bdd.stage := (match f.key with
          | Display.State (s, v) -> Printf.sprintf "emitting the conditions for `%s` = %d" s v
          | Derived n -> Printf.sprintf "emitting the conditions for display cell `%s`" n);
      List.iter emit (compute_groups l spec f p)) plans;
  let conditions = Emit.flatten (List.rev !groups) in
  let seeds = List.map (fun n -> { Emit.signal = n; copy_red = false; value = l.base n }) (List.tl (Array.to_list l.names)) in
  let outs delta = { Emit.signal = "each"; copy_red = true; value = 1 } :: { signal = "each"; copy_red = false; value = delta } :: seeds in
  let ms_per_tick = Cost.estimate l spec conditions (outs 1) (outs (-1)) in
  if Cost.ups ms_per_tick < min_ups then
    fail ~notes:[ (None, Printf.sprintf "%d lanes and %d conditions; the estimate is %.1f ms of circuit work per tick, %.0f UPS"
                     l.lanes (List.length conditions) ms_per_tick (Cost.ups ms_per_tick)) ]
      ~help:[ "narrow state ranges or remove states: every tick each condition is checked against every lane";
              "pass `--min-ups 0` to build it anyway" ]
      "the game would run below %g UPS" min_ups;
  let p = Emit.project () in
  Emit.add_node p "machine" "decider"
    (`Assoc [ ("conditions", `List (List.map Emit.condition_json conditions));
              ("outputs", `List (List.map Emit.output_json (outs 1)));
              ("elseOutputs", `List (List.map Emit.output_json (outs (-1)))) ]);
  Emit.wire p "machine" "machine" "red";
  Emit.wire p "machine" "machine" "green";
  let sensor id s = Emit.add_node p id "sensor_wall" (`Assoc [ ("signal", `String s); ("simActive", `Bool false) ]) in
  sensor "start" spec.start;
  Emit.wire p ~src_port:"circuit" "start" "machine" "green";
  List.iteri (fun i (input : Spec.input) ->
      sensor ("control_" ^ input.input) input.signal;
      sensor ("wake_" ^ input.input) spec.start;
      let previous kind = if i = 0 then "machine" else kind ^ (List.nth spec.inputs (i - 1)).input in
      let dst_port = if i = 0 then "input" else "circuit" in
      Emit.wire p ~src_port:"circuit" ~dst_port ("wake_" ^ input.input) (previous "wake_") "green";
      Emit.wire p ~src_port:"circuit" ~dst_port ("control_" ^ input.input) (previous "control_") "red") spec.inputs;
  let pixels = List.map (fun (cell, records) -> (cell, display_parameters l derived records)) cells in
  if List.exists (fun (_, ps) -> List.length ps > Catalog_data.display_records) pixels then
    fail "a display panel needs more than %d records, the game's limit" Catalog_data.display_records;
  if pixels <> [] then begin
    let w = 1 + List.fold_left (fun m ((x, _), _) -> max m x) 0 pixels
    and h = 1 + List.fold_left (fun m ((_, y), _) -> max m y) 0 pixels in
    for x = 0 to w - 1 do
      for y = 0 to h - 1 do
        let node = Printf.sprintf "pixel_%d_%d" x y in
        let parameters = Option.value (List.assoc_opt (x, y) pixels) ~default:[] in
        Emit.add_node p node "display" (`Assoc [ ("parameters", `List parameters) ]);
        let parent = if y > 0 then Printf.sprintf "pixel_%d_%d" x (y - 1) else if x > 0 then Printf.sprintf "pixel_%d_0" (x - 1) else "machine" in
        Emit.wire p ~src_port:(if parent = "machine" then "output" else "circuit") ~dst_port:"circuit" parent node "green"
      done
    done
  end;
  let condition_count = List.length conditions in
  let decider = Emit.decider_json conditions (outs 1) (outs (-1)) in
  let blueprint = Emit.blueprint p ~label:("One combinator " ^ name) ~decider ~inputs:spec.inputs in
  let rows =
    if symbolic then []
    else
      let states = List.map (fun (s : Spec.state) -> (s.name, Spec.domain s)) spec.states in
      let inputs = List.map (fun (i : Spec.input) -> (i.input, [ 0; 1 ])) spec.inputs in
      List.concat_map (fun old ->
          List.map (fun external_ ->
              let next = Oracle.step spec program (old @ external_) in
              let obj l = `Assoc (List.map (fun (k, v) -> (k, `Int v)) l) in
              `Assoc [ ("state", obj old); ("inputs", obj external_); ("next", obj next) ]) (product inputs)) (product states) in
  let raw key default = Option.value (Spec.raw_field spec key) ~default in
  let register f extra =
    extra @ [ ("a", `String f.a); ("b", `String f.b); ("a_on", `Int (a_on f)); ("b_on", `Int (b_on f)) ] in
  let state_flags = List.filter_map (fun f ->
      match f.key with
      | Display.State (s, v) ->
        Some (`Assoc (register f [ ("state", `String s); ("value", `Int v) ] @ if f.inverted then [ ("inverted", `Bool true) ] else []))
      | Derived _ -> None) l.flags in
  let manifest =
    `Assoc ([ ("format", `String "combinator-compiler"); ("version", `Int 2);
              ("state", raw "state" (`Assoc [])); ("inputs", raw "inputs" (`Assoc [])); ("updates", raw "updates" (`Assoc []));
              ("clock", `String spec.start); ("start_signal", `String spec.start);
              ("bases", `Assoc (Array.to_list (Array.map (fun n -> (n, `Int (l.base n))) l.names)));
              ("flags", `List state_flags);
              ("registers", `String
                 "value = base + raw (int32). Clock raw = phase. Phase 0: B holds the state (on = b_on, off = 0); \
                  phase 1: A holds it (on = a_on, off = -a_on). Inverted flags store the complement of state == value.");
              ("lanes", `Int l.lanes); ("conditions", `Int condition_count);
              ("transition_rows", if symbolic then `Int 0 else `Intlit cases); ("potential_transitions", `Intlit cases);
              ("backend", `String (if symbolic then "symbolic-mdd" else if optimize then "table-mdd" else "table"));
              ("register_quality", `String spec.quality); ("game_limits", Signals.limits);
              ("timing", `String "one synchronous update per powered circuit tick after initialization");
              ("input_port", `String "red input pole; bool = any nonzero signal count");
              ("output_port", `String "green output pole; encoded one-hot state, not raw scalar counts");
              ("outputs", raw "outputs" (`List [])) ]
            @ (if derived = [] then []
               else
                 [ ("display_flags", `List (List.filter_map (fun (d : Display.derived) ->
                       if d.alias <> None then None
                       else Some (`Assoc (register (l.flag_of (Display.Derived d.name)) [ ("name", `String d.name) ]
                                         @ [ ("initial", `Bool d.initial) ]))) derived));
                   ("display_aliases", `Assoc (List.filter_map (fun (d : Display.derived) ->
                       Option.map (fun (s, v) -> (d.name, `List [ `String s; `Int v ])) d.alias) derived)) ])
            @ (match Spec.raw_field spec "arrays" with Some a when spec.arrays <> [] -> [ ("arrays", a) ] | _ -> [])
            @ if constants = [] then [] else [ ("constant_array_fields", `Assoc (List.map (fun (n, v) -> (n, `Int v)) constants)) ]) in
  { project = Emit.project_json p; manifest; rows = `List rows; blueprint; lanes = l.lanes; conditions = condition_count; ms_per_tick;
    row_count = List.length rows; latches = model.latches }
