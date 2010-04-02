type 'a inspected_var =
    [ `Alias of 'a inspected_var * [ `Var of 'a ]
    | `Cons of Algebra.type_cons * 'a inspected_var list
    | `Var of 'a ]
val prec : string -> int
val string_of_type : ?string_of_key:('a -> string) -> 'a inspected_var -> string
val string_of_term : 'a Algebra.generic_term -> string
