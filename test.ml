let bug g h =
  let f =
    let h = fun x -> g x in
    fun y -> h
  in
  2
