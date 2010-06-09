let v =
  let x, f =
    let rev (x, y) = (y, x) in
    rev ((fun x -> x), (fun y -> y))
  in
  2
