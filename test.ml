(* type ('a, 'b) list = Nil | Cons of 'a * 'b * ('a, 'b) list*)

let fst (x, y) = x

let rec1 =
  let rec f x = (x, x)
  and g (y, x) = fst (f y)
  in
  f
