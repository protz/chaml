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

open ConstraintPrinter

let parse_output output =
  let lexbuf = Lexing.from_string output in
  let result = Parser.main Lexer.token lexbuf in
  result

type colors = { green: int; red: int; blue: int; }
let colors = { green = 82; red = 196; blue = 81; }

let test_pass, test_fail =
  let height, width = ref 0, ref 0 in
  Scanf.sscanf
    (Ocamlbuild_plugin.run_and_read "stty size")
    "%d %d" 
    (fun h w -> width := w; height := h);
  let fill s =
    let l = String.length s in
    let spaces = String.make (!width - 3 - l) ' ' in
    s ^ spaces
  in
  let pass = bash_color colors.green "✓" in
  let fail = bash_color colors.red "✗" in
  (fun x -> Printf.printf "%s%s  \n" (fill x) pass),
  (fun x -> Printf.printf "%s%s  \n" (fill x) fail)

let _ =
  print_endline (bash_color colors.blue "Constraint Solving - first series of tests");
  let o = Ocamlbuild_plugin.run_and_read
    "./chaml.native --enable caml-types tests/test_solving.ml"
  in
  let o' = Ocamlbuild_plugin.run_and_read
    "ocamlc -i tests/test_solving.ml"
  in
  let error =
    Printf.kprintf (fun s -> print_endline (bash_color colors.red "%s\n" s))
  in
  try 
    let t = parse_output o in
    let t' = parse_output o' in
    let l = List.length t in
    let good = ref 0 in
    let bad = ref 0 in
    let compare_and_print i r1 r2 =
      let name1, type1 = r1 in
      let name2, type2 = r2 in
      let i = i + 1 in
      let sp = if i >= 10 then "" else " " in
      let test_name =
        Printf.sprintf "[Binding %d/%d]:%s let %s = ..." i l sp name1
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
    Printf.printf
      "--- %s --- %s ---\n"
      (bash_color colors.green "%d%% good" (100 * !good / l))
      (bash_color colors.red "%d%% bad" (100 * !bad / l));
  with Lexer.LexingError e ->
    Printf.printf "Lexing Error: %s\nThe output was:\n%s\n" e o
