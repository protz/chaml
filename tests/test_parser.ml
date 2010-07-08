let _ =
  let lexbuf = Lexing.from_channel stdin in
  let result = Parser.main Lexer.token lexbuf in
  List.map (fun (s, v) ->
    let typ =
      TypePrinter.string_of_type ~string_of_key:(`Auto (fun x -> x)) ~caml_types:true v
    in
    Printf.printf "val %s: %s\n" s typ
  ) result



