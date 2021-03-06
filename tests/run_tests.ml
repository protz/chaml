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

module Constraint_ = Constraint.Make(ParserTypes.BaseSolver) open Constraint_
open TypePrinter
open Bash

let parse_output output =
  let lexbuf = Lexing.from_string output in
  let result = Parser.main Lexer.token lexbuf in
  result

let test_pass, test_fail =
  let fill s =
    let l = String.length s in
    let l = twidth - 3 - l in
    let rec fill l =
      if l < 0 then fill (l + twidth) else l
    in
    let l = fill l in
    let spaces = String.make l ' ' in
    s ^ spaces
  in
  let pass = color colors.green "✓" in
  let fail = color colors.red "✗" in
  (fun x -> Printf.printf "%s%s  \n" (fill x) pass),
  (fun x -> Printf.printf "%s%s  \n" (fill x) fail)


let conversions =
  (* Hack alert ! *)
  let tbl = Hashtbl.create 4 in
  (* let expanded_1 = "('a * 'a as 'a) * 'a -> ('a * 'a -> 'a * 'a -> 'b) -> 'a * 'a -> 'a * 'a -> 'b" in
  let correct_1 = "('a * 'a as 'a) -> ('a -> 'a -> 'b) -> 'a -> 'a -> 'b" in
  Hashtbl.add tbl expanded_1 correct_1; *)
  tbl

let _ =
  let error f =
    Printf.kprintf (fun s -> print_endline (color colors.red "%s\n" s)) f
  in
  let good = ref 0 in
  let bad = ref 0 in
  let compare outputs =
    try
      let ts = List.map parse_output outputs in
      let l = List.length (List.hd ts) in
      let compare_and_print: int -> (string * ParserTypes.pvar) list -> unit = fun i rs ->
        let names, types = List.split rs in
        let types = List.map (string_of_type ~string_of_key:(`Auto (fun x -> x)) ~caml_types:true) types in
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
    with 
    | Lexer.LexingError e ->
        error "Lexing Error: %s" e;
        Printf.printf "The output was:\n%s\n" (List.hd outputs);
    | e ->
      error "Error. The output was \n";
      List.iter print_endline outputs;
      raise e
  in
  (* We have four sorts of tests.
   * i) Type-1 tests: run ocaml, run chaml, run chaml with generalizing match,
   * and compare the results, and enable chaml type-checking
   * ii) Type-2 tests: same thing, but don't enable chaml type-checking
   * iii) Type-3 tests: (special tests) just run chaml (including type-checking)
   * and compare the output against the expected types
   * iv) Type-4 tests: these are supposed to fail
   * *)
  let test1 filename =
    try
      let o = Ocamlbuild_plugin.run_and_read
        ("./chaml.native --enable caml-types --disable generalize-match " ^ filename)
      in
      (* Disable all warnings. It's a test, so there WILL be useless things such as
       * redundant patterns. *)
      let o' = Ocamlbuild_plugin.run_and_read
        ("ocamlc -strict-sequence -i -w a " ^ filename)
      in
      let o'' = Ocamlbuild_plugin.run_and_read
        ("./chaml.native --enable caml-types " ^ filename)
      in
      compare [o; o'; o'']
    with Failure msg ->
      Printf.printf "%s -- here's the error message\n"
        (color colors.red "\t\t\t!!! FAILED !!!");
      test_fail msg;
      bad := !bad + 1
  in
  let test3_generalizing_match filename =
    let o = Ocamlbuild_plugin.run_and_read
      ("./chaml.native --enable caml-types --im-feeling-lucky " ^ filename)
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
  let test2 filename =
    let o = Ocamlbuild_plugin.run_and_read
      ("./chaml.native --enable recursive-types --im-feeling-lucky --enable caml-types --disable generalize-match " ^ filename)
    in
    let o' = Ocamlbuild_plugin.run_and_read
      ("ocamlc -strict-sequence -rectypes -i -w a " ^ filename)
    in
    let o'' = Ocamlbuild_plugin.run_and_read
      ("./chaml.native --enable recursive-types --im-feeling-lucky --enable caml-types " ^ filename)
    in
    compare [o'; o''; o];
  in
  let _test3 () =
    print_endline (box "Constraint Generation - first series of tests");
    let o = Ocamlbuild_plugin.run_and_read
      ("./chaml.native --dont-print-types --disable generalize-match " ^
      "--im-feeling-lucky --disable default-bindings --print-constraint tests/good/test_constraint.ml")
    in
    let fd = open_out "_constraint" in
    output_string fd o;
    close_out fd;
    let o = Ocamlbuild_plugin.run_and_read
      ("./chaml.native --dont-print-types \
       --im-feeling-lucky --disable default-bindings --print-constraint tests/good/test_constraint.ml")
    in
    let fd = open_out "_constraint2" in
    output_string fd o;
    close_out fd;
    let o = Ocamlbuild_plugin.run_and_read
      "mini --start parse-constraint _constraint"
    in
    let o' = Ocamlbuild_plugin.run_and_read
      "ocamlc -i -w a tests/good/test_constraint.ml"
    in
    let o'' = Ocamlbuild_plugin.run_and_read
      "mini --start parse-constraint _constraint2"
    in
    Unix.unlink "_constraint";
    Unix.unlink "_constraint2";
    compare [o; o'; o''];
  in
  let test_good () =
    print_endline (box "Positive tests");
    let dirname = "tests/good" in
    let dir = Unix.opendir "tests/good" in
    let p f = Printf.sprintf "%s/%s" dirname f in
    let run f file =
      Printf.printf "--- In file %s\n" (p file);
      f (p file)
    in
    let skip file =
      Printf.printf "... skipped %s\n" (p file)
    in
    while try
      let file = Unix.readdir dir in
      if String.length file > 2 && file.[0] <> '.' then begin
        begin match String.sub file 0 2 with
        | "t1" ->
            run test1 file
        | "t2" ->
            run test2 file
        | "t3" when file = "t3_generalizing_match.ml" ->
            run test3_generalizing_match file
        | _ ->
            skip file
        end;
        print_newline ();
        true
      end else if file.[0] = '.' then
        true
      else begin
        skip file;
        print_newline ();
        true
      end
    with End_of_file ->
      false
    do
      ()
    done;
    Unix.closedir dir;
  in
  let test_bad () =
    print_endline (box "Negative tests");
    let dir = Unix.opendir "tests/bad" in
    while try
      let file = Unix.readdir dir in
      if (not (file.[0] = '.')) then begin
        let all_failed =
          (try
            let _ = Ocamlbuild_plugin.run_and_read
              (Printf.sprintf "./chaml.native --enable caml-types tests/bad/%s > /dev/null 2>&1" file) in
            false
          with Failure _ ->
            true)
          &&
          (try
            let _ = Ocamlbuild_plugin.run_and_read
              (Printf.sprintf "./chaml.native --enable generalize-match --enable caml-types tests/bad/%s > /dev/null 2>&1" file) in
            false
          with Failure _ ->
            true)
          &&
          (try
            let _ = Ocamlbuild_plugin.run_and_read
              (Printf.sprintf "ocamlc -i tests/bad/%s > /dev/null 2>&1" file) in
            false
          with Failure _ ->
            true)
        in
        if all_failed then
          test_pass file
        else
          test_fail file
      end;
      true
    with End_of_file ->
      false
    do
      ()
    done;
    Unix.closedir dir;
  in
  test_good ();
  print_newline ();
  test_bad ();
  print_newline ();
  (* print_newline ();
  _test3 (); *)
  Printf.printf
    "--- %s --- %s --- (%d total)\n"
    (color colors.green "%d%% good" (100 * !good / (!bad + !good)))
    (color colors.red "%d%% bad" (100 * !bad / (!bad + !good)))
    (!bad + !good);
