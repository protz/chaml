(* Here are some examples that mini can't parse so we use ChaML for the
* constraint generation. Mini then takes on from the constraints we have
* generated and solves them. *)

(* FIXME cannot compare because (a * b) * (c * d) = a * b * c * d for Mini :( *)
(* let f1 = fun a -> function (a, c) -> c | (x, (y, z)) -> x *)

let f2 x = match x with (x, y) -> y x

(* This one gives val o : ('b * 'a as 'a) * 'a -> 'a (using ocaml -rectypes) and
* makes mini crash :-( *)
(* let f5 d = match d with
  | (c, a)
  | (a, (_, c)) -> a *)
