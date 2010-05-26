module JSM = Jmap.Make(String)

let _ =
  let m1 = JSM.empty in
  let m2 = JSM.empty in
  let m1 = JSM.add "A" 1 m1 in
  let m1 = JSM.add "B" 2 m1 in
  let m1 = JSM.add "D" 3 m1 in
  let m1 = JSM.add "D" 4 m1 in
  let m2 = JSM.add "E" 1 m2 in
  let m2 = JSM.add "D" 2 m2 in
  let m2 = JSM.add "G" 3 m2 in
  let m2 = JSM.add "A" 4 m2 in
  print_endline "m1 -----";
  JSM.iter (fun k v -> Printf.printf "%s: %d\n" k v) m1;
  print_endline "m2 -----";
  JSM.iter (fun k v -> Printf.printf "%s: %d\n" k v) m2;
  let m3 = JSM.union m1 m2 in
  print_endline "m1 union m2 -----";
  JSM.iter (fun k v -> Printf.printf "%s: %d\n" k v) m3;
  let m4 = JSM.inter m1 m2 in
  print_endline "m1 inter m2 -----";
  JSM.iter (fun k v -> Printf.printf "%s: %d\n" k v) m4;
  let m5 = JSM.minus m1 m2 in
  print_endline "m1 minus m2 -----";
  JSM.iter (fun k v -> Printf.printf "%s: %d\n" k v) m5;
  let m6 = JSM.minus m2 m1 in
  print_endline "m2 minus m1 -----";
  JSM.iter (fun k v -> Printf.printf "%s: %d\n" k v) m6;
  let m7 = JSM.xor m2 m1 in
  print_endline "m2 xor m1 -----";
  JSM.iter (fun k v -> Printf.printf "%s: %d\n" k v) m7

let _ =
  let l = [1; 2; 3; 3; 5; 5; 6] in
  let l' = Jlist.remove_duplicates l in
  let l = List.map string_of_int l in
  let l' = List.map string_of_int l' in
  Printf.printf
    "remove_duplicates: [%s] -> [%s]\n"
    (String.concat "; " l)
    (String.concat "; " l')
