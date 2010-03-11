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

module Make: functor (M: Map.S) -> sig

  val keys: 'a M.t -> M.key list
  val union: 'a M.t -> 'a M.t -> 'a M.t
  val inter: 'a M.t -> 'a M.t -> 'a M.t
  
end = functor (M: Map.S) -> struct

  let keys m =
    M.fold (fun k _ acc -> k :: acc) m []

  let union m1 m2 =
    M.fold (fun k v m -> M.add k v m) m1 m2

  let inter m1 m2 =
    M.fold (fun k v m1 -> if M.mem k m2 then m1 else M.remove k m1) m1 m1

end
