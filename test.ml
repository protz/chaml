let fst (x, _) = x

let rec1 =
  let rec f x = (x, x)
  and g (y, x) = fst (f y)
  in
  f

let rec2 = rec1
