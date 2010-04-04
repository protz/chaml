let generalize_under_match x =
  match (fun x -> x) with f -> let a = f 2 in let b = f '2' in f

let s x y z = x z (y z)
let k x y = x
let i = s k k

let _ = s k i and e = i i

let f1 f =
  let g x = x in
  let a = g 2 and b = g 2. in
  let _ = a + (f b) in
  match g with
    | id -> let b = id 2. in f b
    | id -> let a = id 2 in a
