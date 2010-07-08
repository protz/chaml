let fst (x, y) = x

let rec1 =
  let rec f x = (x, x)
  and g (y, x) = fst (f y)
  in
  f

let rec fib n =
  match n with
  | 0 -> 1
  | 1 -> 1
  | _ ->
      fib (n-1) + fib (n-2)

let test_const_patterns =
  let f _ = 2, 3. in
  let 2, x = f "toto" in
  x

let rec2 = rec1
