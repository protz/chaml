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
 
let find_opt tbl key =
  if Hashtbl.mem tbl key then
    Some (Hashtbl.find tbl key)
  else
    None

let map_list tbl f =
  let acc = ref [] in
  Hashtbl.iter (fun k v -> acc := (f k v) :: !acc) tbl;
  !acc

module type S = sig
  include Hashtbl.S

  val find_opt : 'a t -> key -> 'a option
  val map_list : 'a t -> (key -> 'a -> 'b) -> 'b list
end

module Make (H: Hashtbl.HashedType) = struct

  module Hashtbl = Hashtbl.Make(H)
  include Hashtbl

  let find_opt tbl key =
    if Hashtbl.mem tbl key then
      Some (Hashtbl.find tbl key)
    else
      None

  let map_list tbl f =
    let acc = ref [] in
    Hashtbl.iter (fun k v -> acc := (f k v) :: !acc) tbl;
    !acc

end

