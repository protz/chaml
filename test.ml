type t = A | B
type t = B

let f = function A -> "a" | B -> "b"

(* type 'a t = Nil | Cons of 'a * 'a t

let length =
  let rec length acc = function
    | Nil -> acc
    | Cons (hd, tl) -> length (acc + 1) tl
  in
  length 0

let map f =
  let rec map acc = function
    | Nil ->
        rev acc
    | Cons (hd, tl) ->
        map ((f hd) :: acc) tl
  in
  map []
 *)
