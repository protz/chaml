let rec split3 = function
  | (x, y, z) :: l ->
      let l1, l2, l3 = split3 l in
      (x :: l1, y :: l2, z :: l3)
  | [] ->
      [], [], []
