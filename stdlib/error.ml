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

let fatal_error f = Printf.kprintf failwith f
let exit_error fmt = Printf.kprintf (fun e -> output_string stderr e; exit 255) fmt

let debug_enabled = ref false
let enable_debug () = debug_enabled := true

let debug_level = ref 0
let dinc () = debug_level := !debug_level + 1
let ddec () = debug_level := !debug_level - 1
let write_indent oc = output_string oc (String.make !debug_level ' ')

let debug fmt =
  if !debug_enabled then
    (write_indent stderr; Jstring.bfprintf stderr fmt)
  else
    Jstring.biprintf fmt

let debug_simple fmt =
  if !debug_enabled then
    (write_indent stderr; Jstring.bfprintf stderr "%s" fmt)
  else
    Jstring.biprintf "%s" fmt
