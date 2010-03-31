(* Doesnt't work at the moment because I don't have _Tuple constructor. *)

let rec ct_list e i =
  if i <= 0 then [] else e :: ct_list e (i - 1)


let complexity ?(tapl=false) i =
  String.concat "\n"
    ("let x y = (y, y) in " ::
     ct_list "let x y = x (x y) in " i @
     [if tapl then "x (\\z. z)" else "x (fun z -> z)"])
