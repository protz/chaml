let v =
  let x, _, (f | f) | x, f, _ =
    let rev (x, y, z) = (z, y, x)
    and g x y = (x, y) in
    rev ((fun x -> x), (fun y -> y), (fun x -> x))
  in
  match f, f with
  | _, f3 ->
      f3 2, f3 2., f3
