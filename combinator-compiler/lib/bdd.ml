type t = int

let zero = 0
let one = 1
let terminal_var = max_int

let vars = ref [||]
let lows = ref [||]
let highs = ref [||]
let count = ref 0
let limit = ref 20_000_000

let table = ref [||]
let table_mask = ref 0

let cache_bits = 20
let cache_size = 1 lsl cache_bits
let ite_cache = Array.make (4 * cache_size) (-1)
let not_cache = Array.make (2 * cache_size) (-1)

let reset () =
  vars := Array.make 1024 terminal_var;
  lows := Array.make 1024 0;
  highs := Array.make 1024 0;
  !lows.(1) <- 1; !highs.(1) <- 1;
  count := 2;
  table := Array.make 2048 0;
  table_mask := 2047;
  Array.fill ite_cache 0 (Array.length ite_cache) (-1);
  Array.fill not_cache 0 (Array.length not_cache) (-1)

let () = reset ()

let size () = !count
let var n = Array.unsafe_get !vars n
let low n = Array.unsafe_get !lows n
let high n = Array.unsafe_get !highs n
let is_const n = n < 2

let[@inline] hash3 a b c =
  let h = (a * 0x9E3779B1) lxor (b * 0x85EBCA77) lxor (c * 0xC2B2AE3D) in
  h lxor (h lsr 29)

let grow_nodes () =
  let n = Array.length !vars in
  let extend a fill = let b = Array.make (2 * n) fill in Array.blit a 0 b 0 n; b in
  vars := extend !vars terminal_var;
  lows := extend !lows 0;
  highs := extend !highs 0

let rehash () =
  let size = 2 * Array.length !table in
  let t = Array.make size 0 in
  let mask = size - 1 in
  for n = 2 to !count - 1 do
    let i = ref (hash3 (var n) (low n) (high n) land mask) in
    while t.(!i) <> 0 do i := (!i + 1) land mask done;
    t.(!i) <- n
  done;
  table := t;
  table_mask := mask

let mk v l h =
  if l = h then l
  else begin
    let t = !table and mask = !table_mask in
    let i = ref (hash3 v l h land mask) in
    let found = ref (-1) in
    while !found < 0 do
      let n = Array.unsafe_get t !i in
      if n = 0 then found := 0
      else if var n = v && low n = l && high n = h then found := n
      else i := (!i + 1) land mask
    done;
    if !found > 0 then !found
    else begin
      if !count >= !limit then Error.fail "symbolic BDD node budget exceeded";
      if !count >= Array.length !vars then grow_nodes ();
      let n = !count in
      incr count;
      !vars.(n) <- v; !lows.(n) <- l; !highs.(n) <- h;
      t.(!i) <- n;
      if 2 * !count > Array.length t then rehash ();
      n
    end
  end

let ithvar v = mk v 0 1

let rec not_ f =
  if f < 2 then 1 - f
  else begin
    let slot = 2 * (f land (cache_size - 1)) in
    if Array.unsafe_get not_cache slot = f then Array.unsafe_get not_cache (slot + 1)
    else begin
      let r = mk (var f) (not_ (low f)) (not_ (high f)) in
      not_cache.(slot) <- f; not_cache.(slot + 1) <- r;
      let back = 2 * (r land (cache_size - 1)) in
      not_cache.(back) <- r; not_cache.(back + 1) <- f;
      r
    end
  end

let rec ite f g h =
  if f = 1 then g
  else if f = 0 then h
  else if g = h then g
  else if g = 1 && h = 0 then f
  else if g = 0 && h = 1 then not_ f
  else begin
    let g = if g = f then 1 else g and h = if h = f then 0 else h in
    if g = h then g
    else if g = 1 && h = 0 then f
    else begin
      let slot = 4 * (hash3 f g h land (cache_size - 1)) in
      if Array.unsafe_get ite_cache slot = f && Array.unsafe_get ite_cache (slot + 1) = g
         && Array.unsafe_get ite_cache (slot + 2) = h
      then Array.unsafe_get ite_cache (slot + 3)
      else begin
        let vf = var f and vg = var g and vh = var h in
        let v = min vf (min vg vh) in
        let f0, f1 = if vf = v then (low f, high f) else (f, f) in
        let g0, g1 = if vg = v then (low g, high g) else (g, g) in
        let h0, h1 = if vh = v then (low h, high h) else (h, h) in
        let r = mk v (ite f0 g0 h0) (ite f1 g1 h1) in
        ite_cache.(slot) <- f; ite_cache.(slot + 1) <- g; ite_cache.(slot + 2) <- h;
        ite_cache.(slot + 3) <- r;
        r
      end
    end
  end

let and_ a b = if a = 0 || b = 0 then 0 else if a = 1 then b else if b = 1 then a else ite a b 0
let or_ a b = if a = 1 || b = 1 then 1 else if a = 0 then b else if b = 0 then a else ite a 1 b
let xor a b = if a = 0 then b else if b = 0 then a else ite a (not_ b) b
let xnor a b = not_ (xor a b)
let imp a b = ite a b 1
let conj l = List.fold_left and_ 1 l
let disj l = List.fold_left or_ 0 l

let implies a b = and_ a (not_ b) = 0

let restrict_with ~value ~last f =
  let memo = Hashtbl.create 64 in
  let rec go f =
    if f < 2 || var f > last then f
    else match Hashtbl.find_opt memo f with
      | Some r -> r
      | None ->
        let r = match value (var f) with
          | 0 -> go (low f)
          | 1 -> go (high f)
          | _ -> mk (var f) (go (low f)) (go (high f))
        in
        Hashtbl.add memo f r; r
  in
  go f

let restrict f assignment =
  match assignment with
  | [] -> f
  | _ ->
    let table = Hashtbl.create 16 in
    let last = List.fold_left (fun m (v, b) -> Hashtbl.replace table v b; max m v) (-1) assignment in
    restrict_with ~value:(fun v -> match Hashtbl.find_opt table v with Some b -> b | None -> -1) ~last f

let eval f value =
  let rec go f = if f < 2 then f = 1 else go (if value (var f) then high f else low f) in
  go f

let any_sat f =
  let rec go f acc =
    if f = 0 then None
    else if f = 1 then Some (List.rev acc)
    else if low f <> 0 then go (low f) ((var f, 0) :: acc)
    else go (high f) ((var f, 1) :: acc) in
  go f []

let support f =
  let seen = Hashtbl.create 64 and vs = Hashtbl.create 16 in
  let rec go f =
    if f >= 2 && not (Hashtbl.mem seen f) then begin
      Hashtbl.add seen f ();
      Hashtbl.replace vs (var f) ();
      go (low f); go (high f)
    end in
  go f;
  List.sort compare (Hashtbl.fold (fun v () acc -> v :: acc) vs [])

let exists vars f =
  match vars with
  | [] -> f
  | _ ->
    let set = Hashtbl.create 16 in
    List.iter (fun v -> Hashtbl.replace set v ()) vars;
    let last = List.fold_left max (-1) vars in
    let memo = Hashtbl.create 64 in
    let rec go f =
      if f < 2 || var f > last then f
      else match Hashtbl.find_opt memo f with
        | Some r -> r
        | None ->
          let l = go (low f) and h = go (high f) in
          let r = if Hashtbl.mem set (var f) then or_ l h else mk (var f) l h in
          Hashtbl.add memo f r; r
    in
    go f

let dag_size roots =
  let seen = Hashtbl.create 64 in
  let rec go f = if f >= 2 && not (Hashtbl.mem seen f) then (Hashtbl.add seen f (); go (low f); go (high f)) in
  List.iter go roots;
  Hashtbl.length seen
