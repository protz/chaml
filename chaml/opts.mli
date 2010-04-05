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

(** This module abstracts command-line options. Use [add_opt] to add a value and
    later in the program, use [get_opt] to test the value of the option. Default
    values are hardcoded in [opts.ml], see there for a list of valid options. *)

(** [add_opt key val] is called when used has enabled or disabled option [key].
    *)
val add_opt : string -> bool -> unit

(** [get_opt key] returns the value of the option [key]. *)
val get_opt : string -> bool
