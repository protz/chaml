(* let v blah =
let x y = (y, y) in 
let x y = x (x y) in 
let x y = x (x y) in 
let x y = x (x y) in 
let x y = x (x y) in 
let x y = x (x y) in 
let x y = x (x y) in 
let x y = x (x y) in 
let x y = x (x y) in 
let x y = x (x y) in 
let x y = x (x y) in 
let x y = x (x y) in 
let x y = x (x y) in 
x (fun z -> z) *)

let f = fun x ->
  let g = fun y -> (x, y) in
  g

(* let f, g =
  let id = fun x -> x in
  id, id *)

(* let f, g =
  let g y = y in
  let h z = g in
  g, h *)

(* let f2 x y =
  let _ = y x x in
  let _ = match x with (z, z') -> y z z' in
  y *)
