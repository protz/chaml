type 'a t = Nil | Cons of 'a * 'a t

(* let hd = function Nil -> assert false | Cons (e, _) -> e *)

let test = Cons (1, Nil)
