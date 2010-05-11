let x, g, f =
  let id (x, y, z) = (z, y, x) in
  id ((fun x -> x), (fun y -> y),  3)
