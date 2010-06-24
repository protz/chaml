let (|>) x f = f x

let inc x = x + 1
let square x = x * x

let _ =
  2 |> inc |> square |> inc |> square
