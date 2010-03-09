(* NB: let f x = x gives a different AST.
*      let _  also gives a different AST *)
let f = fun x -> x
(*
[
  structure_item (test.ml[1,0+0]..test.ml[1,0+18])
    Pstr_value Nonrec
    [
      <def>
        pattern (test.ml[1,0+4]..test.ml[1,0+5])
          Ppat_var "f"
        expression (test.ml[1,0+8]..test.ml[1,0+18])
          Pexp_function ""
          None
          [
            <case>
              pattern (test.ml[1,0+12]..test.ml[1,0+13])
                Ppat_var "x"
              expression (test.ml[1,0+17]..test.ml[1,0+18])
                Pexp_ident "x"
          ]
    ]
*)

let g = f f
(*
  structure_item (test.ml[4,105+0]..test.ml[4,105+11])
    Pstr_value Nonrec
    [
      <def>
        pattern (test.ml[4,105+4]..test.ml[4,105+5])
          Ppat_var "g"
        expression (test.ml[4,105+8]..test.ml[4,105+11])
          Pexp_apply
          expression (test.ml[4,105+8]..test.ml[4,105+9])
            Pexp_ident "f"
          [
            <label> ""
              expression (test.ml[4,105+10]..test.ml[4,105+11])
                Pexp_ident "f"
          ]
    ]
]
*)
