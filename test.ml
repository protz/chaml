(* let generalize_under_match x =
  match (fun x -> x) with
    | f ->
        let a = f 2 in
        let b = f '2' in
        f
    | g ->
        let a = g 3. in
        let b = g "" in
        (fun x -> x) *)

let v4 f =
  let g x = f x in
  g

let f' =
  let g x = x in
  let a = g 2 and b = g 'c' in
  g
