(*****************************************************************************)
(*  ChaML, a type-checker that uses constraints and a kernel language        *)
(*  Copyright (C) 2010 Jonathan Protzenko                                    *)
(*                                                                           *)
(*  This program is free software: you can redistribute it and/or modify     *)
(*  it under the terms of the GNU General Public License as published by     *)
(*  the Free Software Foundation, either version 3 of the License, or        *)
(*  (at your option) any later version.                                      *)
(*                                                                           *)
(*  This program is distributed in the hope that it will be useful,          *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(*  GNU General Public License for more details.                             *)
(*                                                                           *)
(*  You should have received a copy of the GNU General Public License        *)
(*  along with this program.  If not, see <http://www.gnu.org/licenses/>.    *)
(*                                                                           *)
(*****************************************************************************)

(* This currently runs a series of tests that determine whether the ChaML
 * inferred types and the OCaml-inferred types are equal.
 * - '_a is considered as equal to 'a, because there is no value restriction
 * (yet) in ChaML
 * - there are still two files to deal with: test_solving_chaml_only.ml that
 * emphasizes the extra typing features of ChaML and test_constraint.ml that
 * is meant to give the generated constraints to mini and compare these with the
 * output of OCaml. This will require to update the parser and lexer so that
 * mini-like types can be understood too.
 *
 * The parser and lexer aren't that useful right now, but they will be more
 * useful when we recognize mini's syntax for types. Plus, it also allows us to
 * discard the subtle differences in parenthesing between ChaML and OCaml.
 * *)

module TypePrinter_ = TypePrinter.Make(ParserTypes.BaseSolver) open TypePrinter_
module Constraint_ = Constraint.Make(ParserTypes.BaseSolver) open Constraint_

let parse_output output =
  let lexbuf = Lexing.from_string output in
  let result = Parser.main Lexer.token lexbuf in
  result

let test_pass, test_fail =
  let fill s =
    let l = String.length s in
    let l = Bash.twidth - 3 - l in
    let l = if l < 0 then l + Bash.twidth else l in
    let spaces = String.make l ' ' in
    s ^ spaces
  in
  let pass = Bash.color Bash.colors.Bash.green "✓" in
  let fail = Bash.color Bash.colors.Bash.red "✗" in
  (fun x -> Printf.printf "%s%s  \n" (fill x) pass),
  (fun x -> Printf.printf "%s%s  \n" (fill x) fail)


let conversions =
  (* Hack alert ! *)
  let tbl = Hashtbl.create 4 in
  let expanded_1 = "('a * 'a as 'a) * 'a -> ('a * 'a -> 'a * 'a -> 'b) -> 'a * 'a -> 'a * 'a -> 'b" in
  let correct_1 = "('a * 'a as 'a) -> ('a -> 'a -> 'b) -> 'a -> 'a -> 'b" in
  Hashtbl.add tbl expanded_1 correct_1;
  tbl

let _ =
  let error f =
    Printf.kprintf (fun s -> print_endline (Bash.color Bash.colors.Bash.red "%s\n" s)) f
  in
  let good = ref 0 in
  let bad = ref 0 in
  let compare outputs =
    try
      let ts = List.map parse_output outputs in
      let l = List.length (List.hd ts) in
      let compare_and_print: int -> (string * ParserTypes.pvar) list -> unit = fun i rs ->
        let names, types = List.split rs in
        let types = List.map (string_of_type ~caml_types:true) types in
        let i = i + 1 in
        let sp = if i >= 10 then "" else " " in
        (*Printf.printf "%s = %s\n" (print_type type1) (print_type type2);*)
        let test_name =
          Printf.sprintf
            "[Binding %d/%d]:%s val %s: %s" i l sp (List.hd names) (List.hd types)
        in
        let compare_name n = String.compare (List.hd names) n = 0 in
        let compare_type = (=) (List.hd types) in
        if not (List.for_all compare_name names) then
          error "Top-level bindings do not match: %s" (String.concat ", " names)
        else if (List.for_all compare_type types) then begin
          test_pass test_name;
          good := !good + 1;
        end else begin
          let converted_types =
            List.map
              (fun x -> Option.map_none x (Jhashtbl.find_opt conversions x))
              types
          in
            let compare_type = (=) (List.hd converted_types) in
            if (List.for_all compare_type converted_types) then begin
              test_pass test_name;
              good := !good + 1;
            end else begin
              test_fail test_name;
              bad := !bad + 1;
            end
        end
      in
      let heads: 'a list list -> ('a list * 'a list list) option = fun lists ->
        let tails = ref [] in
        let heads = ref [] in
        let module T = struct exception Stop end in
        try
          List.iter
            (function
               | [] -> raise T.Stop
               | hd :: tl -> heads := hd :: !heads; tails := tl :: !tails
            )
            lists;
          Some (!heads, !tails)
        with T.Stop ->
          None
      in
      let ts = ref ts in
      let i = ref 0 in
      while begin
        match heads !ts with
          | Some (heads, tails) ->
              compare_and_print !i heads;
              ts := tails;
              i := !i + 1;
              true
          | None ->
              false
      end do () done;
    with Lexer.LexingError e ->
      error "Lexing Error: %s" e;
      Printf.printf "The output was:\n%s\n" (List.hd outputs);
  in
  let test1 () =
    print_endline (Bash.box "Constraint Solving - standard tests");
    let o = Ocamlbuild_plugin.run_and_read
      "./chaml.native --enable caml-types --disable generalize-match tests/test_solving.ml"
    in
    (* Disable all warnings. It's a test, so there WILL be useless things such as
     * redundant patterns. *)
    let o' = Ocamlbuild_plugin.run_and_read
      "ocamlc -i -w a tests/test_solving.ml"
    in
    let o'' = Ocamlbuild_plugin.run_and_read
      "./chaml.native --enable caml-types tests/test_solving.ml"
    in
    compare [o; o'; o''];
  in
  let test2 () =
    print_endline (Bash.box "Constraint Solving - ChaML extra features");
    let o = Ocamlbuild_plugin.run_and_read
      "./chaml.native --enable caml-types tests/test_solving_chaml_only.ml"
    in
    let o' = String.concat "\n" [
      "val generalize_under_match: 'a -> 'b -> 'b";
      "val s: ('a -> 'b -> 'c) -> ('a -> 'b) -> 'a -> 'c";
      "val k: 'a -> 'b -> 'a";
      "val i: 'a -> 'a";
      "val e: 'a -> 'a\n";
    ]
    in
    compare [o; o'];
  in
  let test2' () =
    print_endline (Bash.box "Constraint Solving - recursive types");
    let o = Ocamlbuild_plugin.run_and_read
      "./chaml.native --enable caml-types --disable generalize-match tests/tests_recursive_types.ml"
    in
    let o' = Ocamlbuild_plugin.run_and_read
      "ocamlc -rectypes -i -w a tests/tests_recursive_types.ml"
    in
    let o'' = Ocamlbuild_plugin.run_and_read
      "./chaml.native --enable caml-types tests/tests_recursive_types.ml"
    in
    compare [o'; o''; o];
  in
  let test3 () =
    print_endline (Bash.box "Constraint Generation - first series of tests");
    let o = Ocamlbuild_plugin.run_and_read
      ("./chaml.native --dont-print-types --disable generalize-match " ^
      "--disable default-bindings --print-constraint tests/test_constraint.ml")
    in
    let fd = open_out "_constraint" in
    output_string fd o;
    close_out fd;
    let o = Ocamlbuild_plugin.run_and_read
      ("./chaml.native --dont-print-types " ^
      "--disable default-bindings --print-constraint tests/test_constraint.ml")
    in
    let fd = open_out "_constraint2" in
    output_string fd o;
    close_out fd;
    let o = Ocamlbuild_plugin.run_and_read
      "mini --start parse-constraint _constraint"
    in
    let o' = Ocamlbuild_plugin.run_and_read
      "ocamlc -i -w a tests/test_constraint.ml"
    in
    let o'' = Ocamlbuild_plugin.run_and_read
      "mini --start parse-constraint _constraint2"
    in
    compare [o; o'; o''];
  in
  test1 ();
  print_newline ();
  test2 ();
  print_newline ();
  test2' ();
  print_newline ();
  test3 ();
  let open Bash in
  Printf.printf
    "--- %s --- %s ---\n"
    (color colors.green "%d%% good" (100 * !good / (!bad + !good)))
    (color colors.red "%d%% bad" (100 * !bad / (!bad + !good)));
