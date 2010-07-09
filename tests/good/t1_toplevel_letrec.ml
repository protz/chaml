let rec f (x, y) =
  g x
and g x =
  (x, x)

let g = g

let rec f' (x, y) =
  g' x
and g' x =
  x

let v = g' 1 + 2
