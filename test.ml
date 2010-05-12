let x, g, f =
  let id (x, y, z) = (z, y, x)
  and g x y = (x, y) in
  id ((fun x -> x), (fun y -> y), "bonjour")
