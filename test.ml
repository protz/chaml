let rec x = x + 1
let fst (x, y) = x

let rec f x = (x, x)
and g (y, x) = fst (f y)
