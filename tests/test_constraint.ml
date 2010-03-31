(* Here are some examples that mini can't parse so we use ChaML for the
* constraint generation. Mini then takes on from the constraints we have
* generated and solves them. *)

let f1 = fun a -> function (a, c) -> c | (x, (y, z)) -> x

(* This one gives val o : ('b * 'a as 'a) * 'a -> 'a (using ocaml -rectypes) *)
let f2 d = match d with
  | (c, a)
  | (a, (_, c)) -> a

(* Surprisingly, mini doesn't seem to recognize + *)
let f3 x y = x + y

(* More complex example *)
let f4 = function (x,y) -> x | (_, (a, b)) -> 42 + 5