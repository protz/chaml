let rec fib n =
  match n with
  | 0 -> 1
  | 1 -> 1
  | _ ->
      fib (n-1) + fib (n-2)

let a = 2 and b = 3
