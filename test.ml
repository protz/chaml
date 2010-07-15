type 'a t = A of (int * ('a -> 'a))

let g =
  let A (_, f) = (fun x -> x) (A (1, fun x -> x)) in
  f

type ('a, 'b) t = A of int * 'a | B of 'b

let m =
  let v = (fun x -> x) (B 2) in
  match v with
  | A (i, a) -> a
  | B x -> x
