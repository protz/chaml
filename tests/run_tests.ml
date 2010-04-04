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
  let compare outputs =
    try
      let ts = List.map parse_output outputs in
      let l = List.length (List.hd ts) in
      let compare_and_print: int -> (string * ParserTypes.pvar) list -> unit = fun i rs ->
        let names, types = List.split rs in
        let types = List.map string_of_type types in
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
          test_fail test_name;
          bad := !bad + 1;
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
    print_endline (box "Constraint Solving - standard tests");
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
    compare [o; o'];
  in
  let test2' () =
    print_endline (box "Constraint Solving - recursive types");
    let o = Ocamlbuild_plugin.run_and_read
      "./chaml.native --enable caml-types --disable generalize-match tests/tests_recursive_types.ml"
    in
    let o' = Ocamlbuild_plugin.run_and_read
      "ocamlc -rectypes -i -w a tests/tests_recursive_types.ml"
    in
    let o'' = Ocamlbuild_plugin.run_and_read
      "./chaml.native --enable caml-types tests/tests_recursive_types.ml"
    in
    compare [o; o'; o''];
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
      ("./chaml.native --disable solver " ^
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
    compare [o'; o; o''];
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
