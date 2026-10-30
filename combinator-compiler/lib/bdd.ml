open Bigarray

type t = int

(* Tables keyed by nodes or variables; the generic Hashtbl (and Int.hash) hash through a C call. *)
module Tbl = Hashtbl.Make (struct type t = int let equal = Int.equal let hash x = x land max_int end)

let zero = 0
let one = 1
let terminal_var = max_int

(* Nodes and the unique table live off-heap as int32: 12 bytes per node plus
   4 per table slot, and the GC never scans them. *)
type store = (int32, int32_elt, c_layout) Array1.t

let make_store n fill = let a = Array1.create int32 c_layout n in Array1.fill a (Int32.of_int fill); a

let nodes : store ref = ref (make_store 0 0)
let count = ref 0
(* Nodes freed by [collect] form a list threaded through their low fields. *)
let free_head = ref 0
let free_count = ref 0
let limit = ref 20_000_000
let stage = ref "building the model"

let table : store ref = ref (make_store 0 0)
let table_mask = ref 0

let cache_bits = 20
let cache_size = 1 lsl cache_bits
let ite_cache = Array.make (4 * cache_size) (-1)
let not_cache = Array.make (2 * cache_size) (-1)

let reset () =
  nodes := make_store (3 * 1024) 0;
  !nodes.{1} <- 1l; !nodes.{2} <- 1l;
  count := 2;
  free_head := 0;
  free_count := 0;
  table := make_store 2048 0;
  table_mask := 2047;
  stage := "building the model";
  Array.fill ite_cache 0 (Array.length ite_cache) (-1);
  Array.fill not_cache 0 (Array.length not_cache) (-1)

let () = reset ()

let size () = !count - !free_count
let[@inline] field n k = Int32.to_int (Array1.unsafe_get !nodes (3 * n + k))
let var n = if n < 2 then terminal_var else field n 0
let low n = field n 1
let high n = field n 2
let is_const n = n < 2

let[@inline] hash3 a b c =
  let h = (a * 0x9E3779B1) lxor (b * 0x85EBCA77) lxor (c * 0xC2B2AE3D) in
  h lxor (h lsr 29)

let grow_nodes () =
  let n = Array1.dim !nodes / 3 in
  let b = make_store (3 * min (2 * n) (!limit + 1)) 0 in
  Array1.blit !nodes (Array1.sub b 0 (3 * n));
  nodes := b

let rehash ?(grow = true) () =
  let size = if grow then 2 * Array1.dim !table else Array1.dim !table in
  let t = make_store size 0 in
  let mask = size - 1 in
  for n = 2 to !count - 1 do
    if var n >= 0 then begin
      let i = ref (hash3 (var n) (low n) (high n) land mask) in
      while Array1.unsafe_get t !i <> 0l do i := (!i + 1) land mask done;
      t.{!i} <- Int32.of_int n
    end
  done;
  table := t;
  table_mask := mask

let budget_exceeded () =
  Error.fail
    ~notes:[ (None, Printf.sprintf "the compiler stopped while %s" !stage) ]
    ~help:[ "narrow state ranges, use fewer array elements or smaller arrays, or split long chains of \
             conditions into smaller helper functions";
            "values that interact (e.g. comparing every array element against a moving position) multiply in size" ]
    "the program is too large to analyse: it needs more than %d symbolic nodes" !limit

let mk v l h =
  if l = h then l
  else begin
    let t = !table and mask = !table_mask in
    let i = ref (hash3 v l h land mask) in
    let found = ref (-1) in
    while !found < 0 do
      let n = Int32.to_int (Array1.unsafe_get t !i) in
      if n = 0 then found := 0
      else if var n = v && low n = l && high n = h then found := n
      else i := (!i + 1) land mask
    done;
    if !found > 0 then !found
    else begin
      let n =
        if !free_head <> 0 then begin
          let n = !free_head in
          free_head := low n;
          decr free_count;
          n
        end else begin
          if !count >= !limit then budget_exceeded ();
          if 3 * (!count + 1) > Array1.dim !nodes then grow_nodes ();
          let n = !count in
          incr count;
          n
        end in
      let a = !nodes in
      a.{3 * n} <- Int32.of_int v; a.{3 * n + 1} <- Int32.of_int l; a.{3 * n + 2} <- Int32.of_int h;
      t.{!i} <- Int32.of_int n;
      if 4 * !count > 3 * Array1.dim t then rehash ();
      n
    end
  end

(* Frees every node not reachable from [roots]. Node numbers of live nodes are unchanged, so any
   BDD the caller still uses must be among the roots or below one. *)
let collect roots =
  let marks = Bytes.make !count '\000' in
  let rec mark n =
    if n >= 2 && Bytes.unsafe_get marks n = '\000' then begin
      Bytes.unsafe_set marks n '\001';
      mark (low n); mark (high n)
    end in
  List.iter mark roots;
  let a = !nodes in
  free_head := 0;
  free_count := 0;
  for n = !count - 1 downto 2 do
    if Bytes.unsafe_get marks n = '\000' then begin
      a.{3 * n} <- -1l; a.{3 * n + 1} <- Int32.of_int !free_head; a.{3 * n + 2} <- 0l;
      free_head := n;
      incr free_count
    end
  done;
  rehash ~grow:false ();
  Array.fill ite_cache 0 (Array.length ite_cache) (-1);
  Array.fill not_cache 0 (Array.length not_cache) (-1)

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

let restrict_with ?(memo = Tbl.create 64) ~value ~last f =
  let rec go f =
    if f < 2 || var f > last then f
    else match Tbl.find_opt memo f with
      | Some r -> r
      | None ->
        let r = match value (var f) with
          | 0 -> go (low f)
          | 1 -> go (high f)
          | _ -> mk (var f) (go (low f)) (go (high f))
        in
        Tbl.add memo f r; r
  in
  go f

(* [restrictor assignment] restricts any node, sharing one memo across calls. *)
let restrictor assignment =
  let table = Tbl.create 16 and memo = Tbl.create 64 in
  let last = List.fold_left (fun m (v, b) -> Tbl.replace table v b; max m v) (-1) assignment in
  restrict_with ~memo ~value:(fun v -> match Tbl.find_opt table v with Some b -> b | None -> -1) ~last

let restrict f assignment = match assignment with [] -> f | _ -> restrictor assignment f

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
  let seen = Tbl.create 64 and vs = Tbl.create 16 in
  let rec go f =
    if f >= 2 && not (Tbl.mem seen f) then begin
      Tbl.add seen f ();
      Tbl.replace vs (var f) ();
      go (low f); go (high f)
    end in
  go f;
  List.sort compare (Tbl.fold (fun v () acc -> v :: acc) vs [])

let exists vars f =
  match vars with
  | [] -> f
  | _ ->
    let set = Tbl.create 16 in
    List.iter (fun v -> Tbl.replace set v ()) vars;
    let last = List.fold_left max (-1) vars in
    let memo = Tbl.create 64 in
    let rec go f =
      if f < 2 || var f > last then f
      else match Tbl.find_opt memo f with
        | Some r -> r
        | None ->
          let l = go (low f) and h = go (high f) in
          let r = if Tbl.mem set (var f) then or_ l h else mk (var f) l h in
          Tbl.add memo f r; r
    in
    go f

let dag_size roots =
  let seen = Tbl.create 64 in
  let rec go f = if f >= 2 && not (Tbl.mem seen f) then (Tbl.add seen f (); go (low f); go (high f)) in
  List.iter go roots;
  Tbl.length seen
