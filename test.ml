type 'a list = Nil | Cons of 'a * 'a list

let length =
  let rec length acc = function
    | Nil -> acc
    | Cons (hd, tl) -> length (acc + 1) tl
  in
  length 0

let rev =
  let rec rev acc = function
    | Cons (hd, tl) ->
        rev (Cons (hd, acc)) tl
    | Nil ->
        acc
  in
  rev Nil

let map f =
  let rec map acc = function
    | Nil ->
        rev acc
    | Cons (hd, tl) ->
        map (Cons ((f hd), acc)) tl
  in
  map Nil
