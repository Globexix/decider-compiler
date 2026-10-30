(* Estimated game time per tick, ported from fas_factorio/cost_workload.py and cost_features.py.
   The decider is run from its initial encoding for a few ticks; each tick's evaluated work is
   priced with the calibrated coefficients in Cost_data and the predictions are averaged. *)

open Circuit

let output_knots = [| 32; 40; 48; 56; 64; 72; 76; 80; 88; 92; 96; 104; 108; 112; 120; 128; 136; 144; 152; 160; 176; 192;
                      208; 224; 240; 256; 272; 288; 304; 320; 352; 384; 416; 448; 496; 512; 528; 544; 560; 576; 608; 640;
                      672; 704; 736; 768; 832; 864; 896; 960; 1023; 1024 |]
let lookup_knots = [| 32; 40; 56; 64; 72; 80; 88; 96; 104; 112; 128; 144; 160; 192; 224; 256; 288; 320; 384; 448; 512;
                      576; 640; 704; 768; 896; 960; 1024 |]

let coefficient =
  let table = Hashtbl.create 128 in
  List.iter (fun (k, v) -> Hashtbl.replace table k v) Cost_data.coefficients;
  fun k -> Option.value (Hashtbl.find_opt table k) ~default:0.

(* Linear interpolation weights between knots, as interpolation_features. *)
let interpolate add n amount knots name ~scale_below =
  let last = Array.length knots - 1 in
  if n <= knots.(0) then add (name 0) (amount *. if scale_below then n /. knots.(0) else 1.)
  else if n >= knots.(last) then add (name last) (amount *. if scale_below then n /. knots.(last) else 1.)
  else begin
    let i = ref 1 in
    while knots.(!i) < n do incr i done;
    let w = (n -. knots.(!i - 1)) /. (knots.(!i) -. knots.(!i - 1)) in
    add (name (!i - 1)) ((1. -. w) *. amount);
    add (name !i) (w *. amount)
  end

type work = {
  mutable signals : int;
  mutable each_checks : int;
  mutable mixed_each_checks : float;
  mutable group_visits : int;
  mutable named_scalar_checks : int;
  mutable unique_groups : int;
  mutable fixed_outputs : int;
  mutable wrapped_outputs : int;
  mutable zero_outputs : int;
  mutable each_constant_writes : int;
  mutable each_copy_writes : int;
  mutable unique_conditions : int;
  mutable named_diversity : int;
  configured_conditions : int;
}

let milliseconds w =
  let total = ref 0. in
  let add k v = total := !total +. coefficient k *. v in
  let f = float_of_int in
  let n = f w.signals and e = f w.each_checks and g = f w.group_visits and u = f w.unique_conditions in
  let scalar = f w.named_scalar_checks and diversity = f (max 1 w.named_diversity) in
  let log2 x = log x /. log 2. in
  add "each_checks" e;
  add "mixed_each_checks" w.mixed_each_checks;
  add "group_visits" g;
  add "unique_groups" (f w.unique_groups);
  add "configured_conditions" (f w.configured_conditions);
  add "fixed_outputs" (f w.fixed_outputs);
  add "zero_outputs" (f w.zero_outputs);
  add "wrapped_outputs" (f w.wrapped_outputs);
  add "unique_conditions_large" (u *. Float.log1p (u /. 8192.));
  add "group_length_work" (g *. log2 (Float.max 1. (e /. Float.max g 1.)));
  add "named_log_signals" (scalar *. log2 (Float.max n 2.));
  add "named_spread" (scalar *. log2 diversity);
  let writes = f (w.each_constant_writes + w.each_copy_writes) in
  let knots k = Array.map float_of_int k in
  interpolate add n (writes /. Float.max n 1.) (knots output_knots)
    (fun i -> Printf.sprintf "output_curve_%d" output_knots.(i)) ~scale_below:true;
  let share = scalar *. Float.min 1. (log2 diversity /. log2 (Float.max n 2.)) in
  interpolate add n share (knots lookup_knots) (fun i -> Printf.sprintf "named_curve_%d" lookup_knots.(i)) ~scale_below:false;
  interpolate add n (f w.each_copy_writes) (knots lookup_knots)
    (fun i -> Printf.sprintf "copy_curve_%d" lookup_knots.(i)) ~scale_below:false;
  !total

type operand = Lane | Named of int * wires

(* One decider evaluation on (red, green), indexed by signal; returns the work and the output. *)
let evaluate groups ~configured (outputs : Emit.output list) (else_outputs : Emit.output list) index red green =
  let size = Array.length red in
  let keys = List.filter (fun i -> green.(i) <> 0) (List.init size Fun.id) |> Array.of_list in
  let n = Array.length keys in
  let w = { signals = n; each_checks = 0; mixed_each_checks = 0.; group_visits = 0; named_scalar_checks = 0;
            unique_groups = 0; fixed_outputs = 0; wrapped_outputs = 0; zero_outputs = 0; each_constant_writes = 0;
            each_copy_writes = 0; unique_conditions = 0; named_diversity = 1; configured_conditions = configured } in
  let accepted = Array.make n false and remaining = ref n in
  let visited = Hashtbl.create 1024 and named = Hashtbl.create 64 in
  let visit id (c : operand) = Hashtbl.replace visited id (); match c with Named (s, _) -> Hashtbl.replace named s () | Lane -> () in
  let scalar s wires = match wires with Red -> red.(s) | Green -> green.(s) in
  let holds cmp a b = match cmp with
    | "=" -> a = b | "!=" -> a <> b | "<" -> a < b | ">" -> a > b | "<=" -> a <= b | ">=" -> a >= b
    | c -> failwith ("internal: comparator " ^ c) in
  let active = Array.make n 0 in
  (try
     Array.iter (fun group ->
         if !remaining = 0 then raise Exit;
         w.unique_groups <- w.unique_groups + 1;
         let len = Array.length group in
         let start = ref 0 and failed = ref false in
         while not !failed && !start < len && (match group.(!start) with (_, Named _, _, _) -> true | _ -> false) do
           let id, op, cmp, right = group.(!start) in
           w.named_scalar_checks <- w.named_scalar_checks + 1;
           visit id op;
           (match op with Named (s, wires) -> if not (holds cmp (scalar s wires) right) then failed := true | Lane -> ());
           incr start
         done;
         if not !failed then
           if !start = len then begin Array.fill accepted 0 n true; remaining := 0; raise Exit end
           else begin
             let count = ref 0 in
             Array.iteri (fun i ok -> if not ok then (active.(!count) <- i; incr count)) accepted;
             w.group_visits <- w.group_visits + !count;
             let i = ref !start in
             while !i < len && !count > 0 do
               let id, op, cmp, right = group.(!i) in
               visit id op;
               let before = !count in
               (match op with
                | Lane ->
                  w.each_checks <- w.each_checks + before;
                  let kept = ref 0 in
                  for j = 0 to before - 1 do
                    let k = active.(j) in
                    if holds cmp green.(keys.(k)) right then (active.(!kept) <- k; incr kept)
                  done;
                  count := !kept;
                  w.mixed_each_checks <- w.mixed_each_checks
                                         +. 4. *. float_of_int (!kept * (before - !kept)) /. float_of_int before
                | Named (s, wires) ->
                  w.named_scalar_checks <- w.named_scalar_checks + 1;
                  if not (holds cmp (scalar s wires) right) then count := 0);
               incr i
             done;
             for j = 0 to !count - 1 do accepted.(active.(j)) <- true done;
             remaining := !remaining - !count
           end) groups
   with Exit -> ());
  w.unique_conditions <- Hashtbl.length visited;
  w.named_diversity <- max 1 (Hashtbl.length named);
  let out = Array.make size 0 in
  let branch (records : Emit.output list) mine =
    let count = Array.fold_left (fun c a -> if a = mine then c + 1 else c) 0 accepted in
    if count > 0 then
      List.iter (fun (o : Emit.output) ->
          if o.signal = "each" then begin
            if o.copy_red then w.each_copy_writes <- w.each_copy_writes + count
            else w.each_constant_writes <- w.each_constant_writes + count;
            Array.iteri (fun k a ->
                if a = mine then
                  let s = keys.(k) in
                  out.(s) <- i32 (out.(s) + if o.copy_red then red.(s) else o.value)) accepted
          end else if o.value = 0 then w.zero_outputs <- w.zero_outputs + 1
          else begin
            let total = i32 (o.value * count) in
            if total = 0 then w.wrapped_outputs <- w.wrapped_outputs + 1 else w.fixed_outputs <- w.fixed_outputs + 1;
            let s = index o.signal in
            out.(s) <- i32 (out.(s) + total)
          end) records in
  branch outputs true;
  branch else_outputs false;
  (w, out)

(* Average estimated milliseconds per tick over [ticks] ticks from the initial encoding, with the
   inputs switching on and off in a fixed pattern. *)
let estimate ?(ticks = 16) (l : layout) (spec : Spec.t) conditions outputs else_outputs =
  let inputs = List.map (fun (i : Spec.input) -> i.signal) spec.inputs in
  let names = Array.append l.names (Array.of_list inputs) in
  let positions = Hashtbl.create (2 * Array.length names) in
  Array.iteri (fun i n -> Hashtbl.replace positions n i) names;
  let index = Hashtbl.find positions in
  let groups = ref [] and current = ref [] in
  List.iteri (fun id ((c : cond), join) ->
      if join = Some "or" then (groups := Array.of_list (List.rev !current) :: !groups; current := []);
      let op = match c.left with Each -> Lane | Signal (s, w) -> Named (index s, w) in
      current := (id, op, c.cmp, c.right) :: !current) conditions;
  if !current <> [] then groups := Array.of_list (List.rev !current) :: !groups;
  let groups = Array.of_list (List.rev !groups) in
  let configured = List.length conditions in
  (* Initial encoding, phase 0: every flag is stored as off (initial values are inverted flags). *)
  let out = Array.make (Array.length names) 0 in
  Array.iteri (fun i n -> out.(i) <- l.base n) l.names;
  let total = ref 0. in
  for t = 0 to ticks - 1 do
    let red = Array.copy out and green = Array.copy out in
    List.iteri (fun k s -> if (t / 4 + k) mod 2 = 1 then red.(index s) <- i32 (red.(index s) + 1)) inputs;
    let w, next = evaluate groups ~configured outputs else_outputs index red green in
    total := !total +. milliseconds w;
    Array.blit next 0 out 0 (Array.length out)
  done;
  !total /. float_of_int ticks

let ups ms = if ms <= 0. then 60. else Float.min 60. (1000. /. ms)
