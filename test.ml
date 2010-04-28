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

let f x =
  let g y = (x, y) in
  g

let f, g =
  let id = fun x -> x in
  id, id
