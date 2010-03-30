(* Generalize under the let ? *)
let v1 = match (fun x -> x) with
  | f ->
      let a = f 2 in
      let b = f '2' in
      f
