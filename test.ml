let x, _, (f | f) | x, f, _ =
  let rev (x, y, z) = (z, y, x)
  and g x y = (x, y) in
  rev ((fun x -> x), (fun y -> y), "bonjour")
