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

module Make = functor (Ord: Map.OrderedType) -> struct

  module Map = Map.Make(Ord)
  include Map

  let keys m =
    Map.fold (fun k _ acc -> k :: acc) m []

  (* m1's values are kept *)
  let union m1 m2 =
    Map.fold (fun k v m -> Map.add k v m) m1 m2

  (* m1's values are kept *)
  let inter m1 m2 =
    Map.fold (fun k _ m1 -> if Map.mem k m2 then m1 else Map.remove k m1) m1 m1

  (* m1 minus all its elements that also belong to m2 *)
  let minus m1 m2 =
    Map.fold (fun k _ m1 -> if Map.mem k m2 then Map.remove k m1 else m1) m1 m1

  let xor m1 m2 =
    (* minus (union m1 m2) (inter m1 m2) *)
    union (minus m2 m1) (minus m1 m2)

  let to_list m1 =
    Map.fold (fun k v acc -> (k,v) :: acc) m1 []

end
