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

open Arg
open Misc
open Format
open Location

(* Compile a .ml file *)

let print_if ppf flag printer arg =
  if !flag then fprintf ppf "%a@." printer arg;
  arg

let (++) x f = f x

let implementation ppf sourcefile outputprefix =
  Location.input_name := sourcefile;
  init_path ();
  let modulename =
    String.capitalize(Filename.basename(chop_extension_if_any sourcefile)) in
  check_unit_name ppf sourcefile modulename;
  Env.set_unit_name modulename;
  let inputfile = Pparse.preprocess sourcefile in
  let env = initial_env() in
  if !Clflags.print_types then begin
    try ignore(
      Pparse.file ppf inputfile Parse.implementation ast_impl_magic_number
      ++ print_if ppf Clflags.dump_parsetree Printast.implementation
      ++ Typemod.type_implementation sourcefile outputprefix modulename env)
    with x ->
      Pparse.remove_preprocessed_if_ast inputfile;
      raise x
  end else begin
    let objfile = outputprefix ^ ".cmo" in
    let oc = open_out_bin objfile in
    try
      Pparse.file ppf inputfile Parse.implementation ast_impl_magic_number
      ++ print_if ppf Clflags.dump_parsetree Printast.implementation
      ++ Unused_var.warn ppf
      ++ Typemod.type_implementation sourcefile outputprefix modulename env
      ++ Translmod.transl_implementation modulename
      ++ print_if ppf Clflags.dump_rawlambda Printlambda.lambda
      ++ Simplif.simplify_lambda
      ++ print_if ppf Clflags.dump_lambda Printlambda.lambda
      ++ Bytegen.compile_implementation modulename
      ++ print_if ppf Clflags.dump_instr Printinstr.instrlist
      ++ Emitcode.to_file oc modulename;
      Warnings.check_fatal ();
      close_out oc;
      Pparse.remove_preprocessed inputfile;
      Stypes.dump (outputprefix ^ ".annot");
    with x ->
      close_out oc;
      remove_file objfile;
      Pparse.remove_preprocessed_if_ast inputfile;
      Stypes.dump (outputprefix ^ ".annot");
      raise x
  end

let c_file name =
  Location.input_name := name;
  if Ccomp.compile_file name <> 0 then exit 2

let process_implementation_file ppf name =
  let opref = Misc.chop_extension_if_any name in
  Compile.implementation ppf name opref

let impl = process_implementation_file Format.err_formatter

let _ =
  let filename = ref "" in
  Arg.parse
    []
    (fun f -> if !filename = "" then filename := f else failwith "Only one file must be specified")
    "ChaML: a type-checker for OCaml programs."
    ();


