type t = Bdd.t array

let width = Array.length

let int_bit n i = if i >= 62 then (if n < 0 then 1 else 0) else (n asr i) land 1

let const ?(width = 32) n : t = Array.init width (fun i -> int_bit n i)

let to_const (v : t) =
  if Array.for_all Bdd.is_const v then begin
    let w = Array.length v in
    let n = ref 0 in
    for i = min w 62 - 1 downto 0 do n := (!n lsl 1) lor v.(i) done;
    if w > 0 && w <= 62 && v.(w - 1) = 1 then n := !n - (1 lsl w);
    Some !n
  end else None

let equal (a : t) (b : t) =
  Array.length a = Array.length b &&
  (let rec go i = i < 0 || (Array.unsafe_get a i = Array.unsafe_get b i && go (i - 1)) in
   go (Array.length a - 1))

let map2 f (a : t) (b : t) : t = Array.init (min (width a) (width b)) (fun i -> f a.(i) b.(i))

let resize ~signed n (v : t) : t =
  let w = width v in
  Array.init n (fun i -> if i < w then v.(i) else if signed && w > 0 then v.(w - 1) else 0)

let select c (a : t) (b : t) : t =
  if c = 1 then a else if c = 0 then b else map2 (Bdd.ite c) a b

let eq (a : t) (b : t) =
  let n = min (width a) (width b) in
  let r = ref 1 in
  for i = n - 1 downto 0 do
    if !r <> 0 then r := Bdd.and_ !r (Bdd.xnor a.(i) b.(i))
  done;
  !r

let ult (a : t) (b : t) =
  let less = ref 0 in
  for i = 0 to min (width a) (width b) - 1 do
    let x = a.(i) and y = b.(i) in
    less := Bdd.ite x (Bdd.and_ y !less) (Bdd.or_ y !less)
  done;
  !less

let flip_sign (v : t) =
  let v = Array.copy v in
  let n = width v in
  if n > 0 then v.(n - 1) <- Bdd.not_ v.(n - 1);
  v

let compare (pred : Ir.cmp) a b =
  match pred with
  | Eq -> eq a b
  | Ne -> Bdd.not_ (eq a b)
  | Ult -> ult a b
  | Ule -> Bdd.not_ (ult b a)
  | Ugt -> ult b a
  | Uge -> Bdd.not_ (ult a b)
  | Slt -> ult (flip_sign a) (flip_sign b)
  | Sle -> Bdd.not_ (ult (flip_sign b) (flip_sign a))
  | Sgt -> ult (flip_sign b) (flip_sign a)
  | Sge -> Bdd.not_ (ult (flip_sign a) (flip_sign b))

let add_carry (a : t) (b : t) carry : t =
  let n = min (width a) (width b) in
  let c = ref carry in
  Array.init n (fun i ->
      let x = a.(i) and y = b.(i) in
      let s = Bdd.xor (Bdd.xor x y) !c in
      c := Bdd.ite x (Bdd.or_ y !c) (Bdd.and_ y !c);
      s)

let add a b = add_carry a b 0
let lognot (a : t) : t = Array.map Bdd.not_ a
let sub a b = add_carry a (lognot b) 1
let neg a = sub (const ~width:(width a) 0) a

let mul (a : t) (b : t) : t =
  let n = width a in
  let result = ref (const ~width:n 0) in
  Array.iteri (fun i bit ->
      if bit <> 0 && i < n then
        let shifted = Array.init n (fun j -> if j < i then 0 else Bdd.and_ bit a.(j - i)) in
        result := add !result shifted) b;
  !result

let binary (op : Ir.binop) a b =
  match op with
  | Add -> add a b
  | Sub -> sub a b
  | Mul -> mul a b
  | And -> map2 Bdd.and_ a b
  | Or -> map2 Bdd.or_ a b
  | Xor -> map2 Bdd.xor a b
