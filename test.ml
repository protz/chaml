type 'a t = Nil | Cons of 'a * 'a t
let t = Cons (2, Cons (42, Nil))

type ('a, 'b) t' = Nil | Cons of 'a * ('a, 'b) t'
let t = Cons (2, Cons (42, Nil))

type ('a, 'b) t'' = Nil | Cons of 'b * ('a, 'b) t''
let t = Cons (2, Cons (42, Nil))

let l = 1 :: 2 :: 3 :: 4 :: []
let l = ["un"; "deux"; "trois"; "quatre"]

let hd = function Nil -> assert false | Cons (e, _) -> e

