(* Doesnt't work at the moment because I don't have _Tuple constructor. *)

let rec ct_list e i =
  if i <= 0 then [] else e :: ct_list e (i - 1)


let complexity ~style i =
  String.concat "\n"
    ((fun l ->
      if (style <> "mlf") then
        "let v blah =" :: l
      else
        l
    ) (
      "let x y = (y, y) in " ::
     ct_list "let x y = x (x y) in " i @
     [if (style = "attapl") then "x (\\z. z)"
      else if (style = "ocaml") then "x (fun z -> z)"
      else if (style = "mlf") then "ignore (x (fun z -> z));;"
      else assert false
     ]))

let _main =
  let count = int_of_string (Sys.argv.(1)) in
  let style = Sys.argv.(2) in
  print_string (complexity ~style count)
