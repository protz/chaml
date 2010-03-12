let f =
  let g x = x in
  let h x = g g x in
  h
