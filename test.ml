(* let f =
  let g x = x in
  let a = g 2 in
  a

let f =
  let g x = x in
  let a = g 2 in
  a *)

let apply f x = 
  let a =
    let v = f x in
    v
  in
  a
