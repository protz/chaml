let fst (x, y) = x
let snd (x, y) = y
let fst3 (x, y, z) = x
let fst12 (x, (y, z)) = x

(* Misc *)
let f1 (x, y) = y x
let f2 x = match x with (x, y) -> y x
let f3 f =
  let g x = x in
  let a = g 2 and b = g 2. in
  a + (f b)

let v4 f v =
  let g (x, y) =
    let a, b = f x in
    a + y
  in
  g v

let f5 arg = match arg with
  | (x, _) | (_, (x, _)) -> x
  | (_, (_, (_, t))) -> t + 1


