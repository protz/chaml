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

exception Error
exception Outdated_version

(* Stolen from driver/pparse.ml *)
(* val file : formatter -> string -> (Lexing.lexbuf -> 'a) -> string -> 'a *)
let file ppf inputfile parse_fun ast_magic =
  let ic = open_in_bin inputfile in
  let is_ast_file =
    try
      let buffer = String.create (String.length ast_magic) in
      really_input ic buffer 0 (String.length ast_magic);
      if buffer = ast_magic then true
      else if String.sub buffer 0 9 = String.sub ast_magic 0 9 then
        raise Outdated_version
      else false
    with
      Outdated_version ->
        Misc.fatal_error "Ocaml and preprocessor have incompatible versions"
    | _ -> false
  in
  let ast =
    try
      if is_ast_file then begin
        if !Clflags.fast then
          Format.fprintf ppf "@[Warning: %s@]@."
            "option -unsafe used with a preprocessor returning a syntax tree";
        Location.input_name := input_value ic;
        input_value ic
      end else begin
        seek_in ic 0;
        Location.input_name := inputfile;
        let lexbuf = Lexing.from_channel ic in
        Location.init lexbuf inputfile;
        parse_fun lexbuf
      end
    with x -> close_in ic; raise x
  in
  close_in ic;
  ast

let _ =
  let arg_filename = ref "" in
  let arg_print_ast = ref false in
  let arg_print_constraint = ref false in
  let arg_pretty_printing = ref false in
  let add_opt v k = Opts.add_opt k v in
  let usage = String.concat ""
                ["ChaML: a type-checker for OCaml programs.\n";
                 "Usage: "; Sys.argv.(0); " [OPTIONS] FILE\n"] in
  Arg.parse
    [
      "--print-ast", Arg.Set arg_print_ast, "print the AST as parsed by the OCaml frontend";
      "--print-constraint", Arg.Set arg_print_constraint, "print the constraint in a format mini can parse";
      "--pretty-printing", Arg.Set arg_pretty_printing, "print the constraint using advanced terminal features";
      "--enable", Arg.String (add_opt true), "enable one of the following options: generalize-match (on by default)";
      "--disable", Arg.String (add_opt false), "disable one of the options above";
    ]
    (fun f -> if !arg_filename = "" then arg_filename := f else print_endline "*** More than one file given, keeping the first one.")
    usage;
  if !arg_filename = "" then begin
    print_string usage
  end else begin
    let ast = file Format.err_formatter !arg_filename Parse.implementation Config.ast_impl_magic_number in
    if !arg_print_ast then
      Format.fprintf Format.std_formatter "%a@." Printast.implementation ast;
    let konstraint = Constraint.generate_constraint ast in
    if !arg_print_constraint then begin
      let pp_env = ConstraintPrinter.fresh_pp_env ~pretty_printing:!arg_pretty_printing () in
      print_string (ConstraintPrinter.string_of_constraint pp_env konstraint)
    end;
  end
