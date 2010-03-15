(*let s x y z = x z (y z)
let k x y = x
let i = s k k

let d g x1 x2 =
  let _ = g x1 in
  let _ = g x2 in
  g

let _ = s k i and e = i i

(* mini considers those two are identical *)
let f (x, y, z) = x
let o (x, (y, z)) = x*)

(* mini doesn't parse this one but can solve the constraint... and flattens the
* tuple *)
let o = function (a, c) -> c | (x, (y, z)) -> x
(* let o x = match x with
  | (a, c) -> c
  | (a, (b, c)) -> b *)
