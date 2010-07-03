type 'a t = Nil | Cons of 'a * 'a t

let length =
  let rec length acc = function
    | Nil -> acc
    | Cons (hd, tl) -> length (acc + 1) tl
  in
  length 0

