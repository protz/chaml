let f x =
  fun x ->
    let fst (x, y) =
      y + x
    in
    x
