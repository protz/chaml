let v blah =
let x y = (y, y) in 
let x y = x (x y) in 
x (fun z -> z)
