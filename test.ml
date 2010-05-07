let f, g =
  let id x = x in
  id ((fun x -> x), 2)
