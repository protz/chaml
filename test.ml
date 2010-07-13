type 'a t = A of (int * ('a -> 'a))

let g =
  let A (_, f) = (fun x -> x) (A (1, fun x -> x)) in
  f
