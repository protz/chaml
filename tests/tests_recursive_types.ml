(* let f1 x y = y (x, x) *)

let f2 x y =
  let _ = y x x in
  let _ = match x with (z, z') -> y z z' in
  y


let f5 d = match d with
  | (c, a)
  | (a, (_, c)) -> a
