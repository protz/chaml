let test_const_patterns =
  let f _ = 2, 3. in
  let 2, x = f "toto" in
  x
