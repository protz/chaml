let rec f x =
  g (x, x)
and g (x, _) =
  f x
