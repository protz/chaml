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

let constraint_files = [
  "test_chaml.ml";
  "test.ml";
  "test2.ml";
  "test3.ml";
]

let test_constraint f =
  Ocamlbuild_plugin.run_and_read

let parse_output output =
  let lexbuf = Lexing.from_string output in
  let result = Parser.main Lexer.token lexbuf in
  result

let _ =
  let o = Ocamlbuild_plugin.run_and_read
    "./chaml.native --enable caml-types tests/test.ml"
  in
  try 
    let t = parse_output o in
    print_endline o;
    ignore t;
  with Lexer.LexingError e ->
    Printf.printf "Lexing Error: %s\nThe output was:\n%s\n" e o
