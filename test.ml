let f2 x y =
  let _ = y x x in
  let _ = match x with (z, z') -> y z z' in
  y
