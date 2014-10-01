(* Parsing for different data-types. *)
val parse_lit : Model.t -> Genlex.token Stream.t -> MTypes.lit
val parse_clause : Model.t -> Genlex.token Stream.t -> MTypes.clause
