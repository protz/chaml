let fst (x, y) = x

let _ =
  let rec f x = (x, x)
  and g (y, x) = fst (f y)
  in
  f
