(* val bug : ('a -> 'b) -> 'a -> 'a -> 'b = <fun> *)
let bug f x =
  let _ = f x in
  f

let f =
  let g x = x in
  let a = g 2 and b = g 2. in
  g

let id x = x

let s x y z = x z (y z)
let k x y = x
let v = k 2.
let i = s k k

let generalize_under_match x =
  match (fun x -> x) with f -> let a = f 2 in let b = f 2. in f

let fst (x, y) = x
let snd (x, y) = y
let fst3 (x, y, z) = x
let fst12 (x, (y, z)) = x
