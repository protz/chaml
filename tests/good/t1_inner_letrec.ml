let deux =
  let rec f (x, y) =
    g x
  and g x =
    x

  in

  let v = match 1 with 1 -> (g 1, 2) | 2 -> (2, g 1)

  in

  2
