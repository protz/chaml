let f2 x y =
  let _ = y x x in
  let _ = match x with (z, z') -> y z z' in
  y

let f3 x = match x with (x, x') -> x | (x', x) -> x | _ -> x

(* let f4 x y = (y (x, x), y x) *)

let f5 d = match d with
  | (c, a)
  | (a, (_, c)) -> a
