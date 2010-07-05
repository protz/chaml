let length =
  let rec length acc = function
    | hd :: tl ->
        length (acc + 1) tl
    | [] ->
        acc
  in
  length 0

let four = length [1; 2; 3; 4]

let ignore _ = (); ()


