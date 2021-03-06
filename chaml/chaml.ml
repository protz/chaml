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

module TheConstraintGenerator = OCamlConstraintGenerator.Make(Solver.BaseSolver)

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

module Options = struct
  let options = Hashtbl.create 8

  let _ =
    List.iter
      (fun (k, v) -> Hashtbl.add options k v)
      [
        ("generalize-match",
          (true, "Generalize the pattern which is matched under a branch"));
        ("recursive-types",
          (false, "Allow equirecursive types"));
        ("default-bindings",
          (true, "Include default bindings for arithmetic operations (+, *, ...)"));
        ("caml-types",
          (false, "Print OCaml-style 'a types instead of unicode greek characters"));
        ("debug",
          (false, "Output debug information"));
        ("pretty-printing",
          (false, "Use colors for matching parentheses when dumping constraints"));
      ]

  let set_opt: string -> bool -> unit = fun k v ->
    match Jhashtbl.find_opt options k with
      | Some (_, desc) ->
          Hashtbl.replace options k (v, desc)
      | None ->
          Error.exit_error "No such option %s" k

  let get_opt: string -> bool = fun k ->
    match Jhashtbl.find_opt options k with
      | None ->
          Error.exit_error "No such option %s" k
      | Some (v, _) ->
          v

  let descriptions =
    let descriptions =
      Jhashtbl.map_list
        options
        (fun k (def, desc) -> Printf.sprintf "  %s (default: %b): %s" (Bash.underline "%s" k) def desc)
    in
    String.concat "\n" (descriptions @ ["\n"])

end

let _ =
  let arg_filename = ref "" in
  let arg_print_ast = ref false in
  let arg_print_constraint = ref false in
  let arg_print_types = ref true in
  let arg_print_typed_ast = ref false in
  let arg_print_core_ast = ref false in
  let arg_type_check = ref true in
  let arg_print_useless = ref false in
  let add_opt v k = Options.set_opt k v in
  let usage = String.concat ""
                ["ChaML: a type-checker for OCaml programs.\n";
                 "Usage: "; Sys.argv.(0); " [OPTIONS] FILE\n";
                 "\nAvailable features:\n\n";
                 Options.descriptions;
                 "Available options:\n"
                ] in
  Arg.parse
    [
      "--print-ast", Arg.Set arg_print_ast, "print the AST as parsed by the OCaml frontend";
      "--print-constraint", Arg.Set arg_print_constraint, "print the constraint in a format mini can parse";
      "--dont-print-types", Arg.Clear arg_print_types, "don't print the inferred types, à la ocamlc -i";
      "--print-typed-ast", Arg.Set arg_print_typed_ast, "print the AST annotated with the types found by the solver";
      "--print-core-ast", Arg.Set arg_print_core_ast, "print the System F generated term";
      "--print-useless-information", Arg.Set arg_print_useless, "print useless information";
      "--im-feeling-lucky", Arg.Clear arg_type_check, "don't type-check";
      "--enable", Arg.String (add_opt true), "enable one of the features above";
      "--disable", Arg.String (add_opt false), "disable one of the features above";
    ]
    (fun f -> if !arg_filename = "" then arg_filename := f else print_endline "*** More than one file given, keeping the first one.")
    usage;
  if !arg_filename = "" then begin
    print_string usage
  end else begin
    (* Do this right now as all the modules are likely to use it. *)
    if Options.get_opt "debug" then begin
      Error.enable_debug ();
    end;
    (* Get the AST from OCaml lexer/parser *)
    let ast = file Format.err_formatter !arg_filename Parse.implementation Config.ast_impl_magic_number in
    if !arg_print_ast then
      Format.fprintf Format.std_formatter "%a@." Printast.implementation ast;
    (* Constraint generation *)
    let generalize_match = Options.get_opt "generalize-match" in
    let default_bindings = Options.get_opt "default-bindings" in
    let konstraint = TheConstraintGenerator.generate_constraint ~generalize_match ~default_bindings ast in
    let konstraint, hterm = match konstraint with
      | `Error e ->
          let e = OCamlConstraintGenerator.string_of_error e in
          output_string stderr
            (Bash.color Bash.colors.Bash.red "!!! Constraint generation failed\n");
          Error.exit_error "%s" e
      | `Ok v ->
          v
    in
    (* Print the constraint, possibly with pretty-printing *)
    if !arg_print_constraint then begin
      let pretty_printing = Options.get_opt "pretty-printing" in
      let str =
        TheConstraintGenerator.string_of_constraint ~pretty_printing konstraint
      in
      print_endline str;
      flush stdout
    end;
    (* Constraint solving *)
    let print_types = !arg_print_types in
    let caml_types = Options.get_opt "caml-types" in
    let recursive_types = Options.get_opt "recursive-types" in
    let r = Solver.solve ~caml_types ~print_types ~recursive_types konstraint in
    begin match r with
      | `Error e ->
          let e = Solver.string_of_error e in
          output_string stderr
            (Bash.color Bash.colors.Bash.red "!!! Constraint solving failed\n");
          Error.exit_error "%s" e
      | `Ok ->
          ()
    end;
    (* By default, we type-check. This is usually disabled in the tests for
     * recursive types. *)
    if not !arg_type_check then
      exit(0);
    (* Translate to the first intermediate language *)
    let camlx_ast = Translator.translate hterm in
    if !arg_print_typed_ast then begin
      flush stdout; flush stderr;
      print_string (Translator.string_of_struct camlx_ast);
    end;
    Error.debug "\n[Driver] Translation done, now desugaring...\n";
    (* Translate to the core language *)
    let minimal_env, core_ast = Desugar.desugar camlx_ast in
    if !arg_print_core_ast then begin
      flush stdout; flush stderr;
      print_string (Desugar.string_of_struct core_ast);
    end;
    (* The final type-checking part *)
    TypeCheck.check minimal_env core_ast;
    Error.debug "[Driver] Done.\n";
    (* Statistics *)
    if !arg_print_useless then begin
      Printf.printf "[Driver] %d nodes in the OCaml ast\n"
        (Count.count_ocaml_nodes ast);
      Printf.printf "[Driver] %d nodes in the constraint\n"
        (Count.count_constraint_nodes konstraint);
      Printf.printf "[Driver] %d nodes in the CamlX AST\n"
        (Count.count_camlx_nodes camlx_ast);
      Printf.printf "[Driver] %d nodes in the Core AST\n"
        (Count.count_core_nodes core_ast);
    end;
    flush stdout; flush stderr;
  end
