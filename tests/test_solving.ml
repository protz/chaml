(* val bug : ('a -> 'b) -> 'a -> 'a -> 'b = <fun> *)
let bug f x =
  let _ = f x in
  f

let s x y z = x z (y z)
let k x y = x
let i = s k k

let bug' = k 2.

let d g x1 x2 =
  let _ = g x1 in
  let _ = g x2 in
  g

(* mini considers those two to be identical *)
let f (x, y, z) = x
let o (x, (y, z)) = x
let n x y z = 1

(* val d : ('a -> 'b) -> 'a -> 'a -> 'b = <fun> *)
let d' f x =
  let _ = f x in
  f

let f' =
  let g x = x in
  let a = g 2 and b = g 'c' in
  g

let id x = x

(* Issues start here *)
let fst (x, y) = x
let snd (x, y) = y
let fst3 (x, y, z) = x
let fst12 (x, (y, z)) = x
