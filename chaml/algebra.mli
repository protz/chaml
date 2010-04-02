type ident = [ `Var of Longident.t ] * Location.t
module IdentMap :
  sig
    type key = ident
    type +'a t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val add : key -> 'a -> 'a t -> 'a t
    val find : key -> 'a t -> 'a
    val remove : key -> 'a t -> 'a t
    val mem : key -> 'a t -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  end
type type_cons = { cons_name : string; cons_arity : int; }
type 'a generic_var = [ `Var of 'a ]
type 'a generic_term =
    [ `Cons of type_cons * 'a generic_term list | `Var of 'a ]
type 'a generic_scheme =
    'a generic_var list * 'a generic_constraint * 'a generic_var IdentMap.t
and 'a generic_constraint =
    [ `Conj of 'a generic_constraint * 'a generic_constraint
    | `Dump
    | `Equals of 'a generic_var * 'a generic_term
    | `Exists of 'a generic_var list * 'a generic_constraint
    | `Instance of ident * 'a generic_var
    | `Let of 'a generic_scheme list * 'a generic_constraint
    | `True ]
val global_constructor_table : (string, type_cons) Hashtbl.t
val type_cons : string -> 'a list -> [> `Cons of type_cons * 'a list ]
val type_cons_arrow : 'a -> 'a -> [> `Cons of type_cons * 'a list ]
val type_cons_int : [> `Cons of type_cons * 'a list ]
val type_cons_char : [> `Cons of type_cons * 'a list ]
val type_cons_string : [> `Cons of type_cons * 'a list ]
val type_cons_float : [> `Cons of type_cons * 'a list ]
val type_cons_unit : [> `Cons of type_cons * 'a list ]
