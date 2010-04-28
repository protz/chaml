let _ =
  match (1,2) with
  | (x, y) | (y, _) -> y
  | _ -> 3
