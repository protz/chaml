module StringMap = Map.Make(String)
module JSM = Jmap.Make(StringMap)

let _ =
  let m1 = StringMap.empty in
  let m2 = StringMap.empty in
  let m1 = StringMap.add "A" 1 m1 in
  let m1 = StringMap.add "B" 2 m1 in
  let m1 = StringMap.add "D" 3 m1 in
  let m1 = StringMap.add "D" 4 m1 in
  let m2 = StringMap.add "E" 1 m2 in
  let m2 = StringMap.add "D" 2 m2 in
  let m2 = StringMap.add "G" 3 m2 in
  let m2 = StringMap.add "A" 4 m2 in
  print_endline "m1 -----";
  StringMap.iter (fun k v -> Printf.printf "%s: %d\n" k v) m1;
  print_endline "m2 -----";
  StringMap.iter (fun k v -> Printf.printf "%s: %d\n" k v) m2;
  let m3 = JSM.union m1 m2 in
  print_endline "m1 union m2 -----";
  StringMap.iter (fun k v -> Printf.printf "%s: %d\n" k v) m3;
  let m4 = JSM.inter m1 m2 in
  print_endline "m1 inter m2 -----";
  StringMap.iter (fun k v -> Printf.printf "%s: %d\n" k v) m4;

