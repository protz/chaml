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

type t = {
  identifier: Algebra.Identifiers.ident;
  id: int
}

let fresh identifier = {
  identifier;
  id = Oo.id (object end);
}

let phantom () = fresh (Algebra.Identifiers.ident "_phantom" Location.none)

let ident { identifier; _ } = identifier

let compare { id = id1; _ } { id = id2; _ } = compare id1 id2

let equal = (==)

let string_of_atom { identifier; id } = 
  Printf.sprintf "%s/%d" (Algebra.Identifiers.string_of_ident identifier) id
