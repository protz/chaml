let s x y z = x z (y z)
let k x y = x
let i = s k k

let d g x1 x2 =
  let _ = g x1 in
  let _ = g x2 in
  g

let _ = s k i and e = i i

let f (x, y, z) = x
