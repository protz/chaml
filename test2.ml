(* Here are some examples that mini can't parse so we use ChaML for the
* constraint generation. Mini then takes on from the constraints we have
* generated and solves them. *)

let f1 = fun a -> function (a, c) -> c | (x, (y, z)) -> x

(* This one gives val o : ('b * 'a as 'a) * 'a -> 'a (using ocaml -rectypes) *)
let f2 x = match x with
  | (c, a)
  | (a, (_, c)) -> a
