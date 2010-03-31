let generalize_under_match x =
  match (fun x -> x) with f -> let a = f 2 in let b = f '2' in f

let s x y z = x z (y z)
let k x y = x
let i = s k k

let _ = s k i and e = i i
