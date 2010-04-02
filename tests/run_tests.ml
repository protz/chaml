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

open TypePrinter
open ConstraintPrinter

let parse_output output =
  let lexbuf = Lexing.from_string output in
  let result = Parser.main Lexer.token lexbuf in
  result

type colors = { green: int; red: int; blue: int; }
let colors = { green = 82; red = 196; blue = 81; }

let twidth, theight =
  let height, width = ref 0, ref 0 in
  Scanf.sscanf
    (Ocamlbuild_plugin.run_and_read "stty size")
    "%d %d" 
    (fun h w -> width := w; height := h);
  !width, !height

let test_pass, test_fail =
  let fill s =
    let l = String.length s in
    let l = twidth - 3 - l in
    let l = if l < 0 then l + twidth else l in
    let spaces = String.make l ' ' in
    s ^ spaces
  in
  let pass = bash_color colors.green "✓" in
  let fail = bash_color colors.red "✗" in
  (fun x -> Printf.printf "%s%s  \n" (fill x) pass),
  (fun x -> Printf.printf "%s%s  \n" (fill x) fail)

let box txt =
  let boxw = String.length txt + 4 in
  let whitespace = String.make ((twidth - boxw) / 2) ' ' in
  let charw = String.length "║" in
  let line = "═" in
  let top = String.make (charw * boxw) ' ' in
  for i = 1 to boxw - 2 do
    String.blit line 0 top (i * charw) charw;
  done;
  String.blit "╔" 0 top 0 charw;
  String.blit "╗" 0 top (charw * (boxw - 1)) charw;
  let middle = Printf.sprintf "║ %s ║" txt in
  let bottom = String.make (charw * boxw) ' ' in
  for i = 1 to boxw - 2 do
    String.blit line 0 bottom (i * charw) charw;
  done;
  String.blit "╚" 0 bottom 0 charw;
  String.blit "╝" 0 bottom (charw * (boxw - 1)) charw;
  bash_color colors.blue "%s%s\n%s%s\n%s%s\n"
    whitespace top whitespace middle whitespace bottom

let _ =
  let error f =
    Printf.kprintf (fun s -> print_endline (bash_color colors.red "%s\n" s)) f
  in
  let good = ref 0 in
  let bad = ref 0 in
  let compare o o' =
    try 
      let t = parse_output o in
      let t' = parse_output o' in
      let l = List.length t in
      let compare_and_print i r1 r2 =
        let name1, type1 = r1 in
        let name2, type2 = r2 in
        let type1, type2 = string_of_type type1, string_of_type type2 in
        let i = i + 1 in
        let sp = if i >= 10 then "" else " " in
        (*Printf.printf "%s = %s\n" (print_type type1) (print_type type2);*)
        let test_name =
          Printf.sprintf "[Binding %d/%d]:%s val %s: %s but also %s" i l sp name1 type1 type2
        in
        if (String.compare name1 name2) != 0 then
          error "Top-level bindings do not match: %s != %s" name1 name2
        else if type1 = type2 then begin
          test_pass test_name;
          good := !good + 1;
        end else begin
          test_fail test_name;
          bad := !bad + 1;
        end
      in
      Jlist.iter2i compare_and_print t t';
    with Lexer.LexingError e ->
      error "Lexing Error: %s" e;
      Printf.printf "The output was:\n%s\n" o;
  in
  let test1 () =
    print_endline (box "Constraint Solving - standard tests");
    let o = Ocamlbuild_plugin.run_and_read
      "./chaml.native --enable caml-types --disable generalize-match tests/test_solving.ml"
    in
    (* Disable all warnings. It's a test, so there WILL be useless things such as
     * redundant patterns. *)
    let o' = Ocamlbuild_plugin.run_and_read
      "ocamlc -i -w a tests/test_solving.ml"
    in
    compare o o';
  in
  let test2 () =
    print_endline (box "Constraint Solving - ChaML extra features"); 
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
    compare o o';
  in
  let test2' () =
    print_endline (box "Constraint Solving - recursive types");
    let o = Ocamlbuild_plugin.run_and_read
      "./chaml.native --enable caml-types --disable generalize-match tests/tests_recursive_types.ml"
    in
    let o' = Ocamlbuild_plugin.run_and_read
      "ocamlc -rectypes -i -w a tests/tests_recursive_types.ml"
    in
    compare o o';
  in
  let test3 () =
    print_endline (box "Constraint Generation - first series of tests"); 
    let o = Ocamlbuild_plugin.run_and_read
      ("./chaml.native --disable solver --disable generalize-match " ^
      "--disable default-bindings --print-constraint tests/test_constraint.ml")
    in
    let fd = open_out "_constraint" in
    output_string fd o;
    close_out fd;
    let o = Ocamlbuild_plugin.run_and_read 
      "mini --start parse-constraint _constraint"
    in
    let o' = Ocamlbuild_plugin.run_and_read
      "ocamlc -i -w a tests/test_constraint.ml"
    in
    compare o' o;
  in
  Opts.add_opt "caml-types" true;
  test1 ();
  print_newline ();
  test2 ();
  print_newline ();
  test2' ();
  print_newline ();
  test3 ();
  Printf.printf
    "--- %s --- %s ---\n"
    (bash_color colors.green "%d%% good" (100 * !good / (!bad + !good)))
    (bash_color colors.red "%d%% bad" (100 * !bad / (!bad + !good)));
