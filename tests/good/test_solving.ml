(* val bug : ('a -> 'b) -> 'a -> 'a -> 'b = <fun> *)
let bug f x =
  let _ = f x in
  f

let s x y z = x z (y z)
let k x y = x
let i = s k k

let bug' = k 2.

let d g x1 x2 =
  let _ = g x1 in
  let _ = g x2 in
  g

(* mini considers those two to be identical *)
let f (x, y, z) = x
let o (x, (y, z)) = x
let n x y z = 1

(* val d : ('a -> 'b) -> 'a -> 'a -> 'b = <fun> *)
let d' f x =
  let _ = f x in
  f

let f' =
  let g x = x in
  let a = g 2 and b = g 'c' in
  g

let id x = x

let fst (x, y) = x
let snd (x, y) = y
let fst3 (x, y, z) = x
let fst12 (x, (y, z)) = x

(* Misc *)
let f1 (x, y) = y x
let f2 x = match x with (x, y) -> y x
let f3 f =
  let g x = x in
  let a = g 2 and b = g 2. in
  a + (f b)

let v4 f v =
  let g (x, y) =
    let a, b = f x in
    a + y
  in
  g v

let f5 arg = match arg with
  | (x, _) | (_, (x, _)) -> x
  | (_, (_, (_, t))) -> t + 1

let v6 =
  let f x = 3 in
  let a = 2 and b = 2. in
  let a = f b and b = f a in
  a + b

(* More complex example *)
let f7 = function (x,y) -> x | (_, (a, b)) -> 42

let v8 f =
  let g x = f x in
  g

let f9 g h =
  let g x = h x g in
  let g =
    let h = fun x -> g x in
    fun _ -> h
  in
  g

(* Tuples *)
let f10 x y =
  let v = (x, (x, y)) in
  snd (snd x)

let f11 (y, x) = (x, x)

let f12 a b = match (a, b) with
  | x -> fst x
  | y -> snd y

let f12 ((a, b), (c, d)) = (a, b, c, d)

let f13 x =
  let g y = (y, x) in
  (g 2, g 3.)

let f14 a = (
  match a with
  | (x, y) -> (y, x)
  ,
  (fun x -> (x, a)) 2
)

(* let f15 f x =
  let a = f x and a = f x in
  "duh" *)

(* let boris _ =
  let x y = (y, y) in 
  let x y = x (x y) in 
  let x y = x (x y) in 
  let x y = x (x y) in 
  x (fun z -> z) *)

let fsharp =
  let (|>) x f = f x in
  let inc x = x + 1 in
  let square x = x * x in
  2 |> inc |> square |> inc |> square
