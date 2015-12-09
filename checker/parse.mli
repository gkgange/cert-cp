(* Parsing for different data-types. *)
(*
val parse_ivar : Model.t -> Genlex.token Stream.t -> MTypes.ivar
val parse_bvar : Model.t -> Genlex.token Stream.t -> MTypes.bvar
val parse_vprop : Model.t -> Genlex.token Stream.t -> MTypes.lit
(* val parse_vprop : Model.t -> Genlex.token Stream.t -> MTypes.vprop *)
val parse_lit : Model.t -> Genlex.token Stream.t -> MTypes.lit
val parse_clause : Model.t -> Genlex.token Stream.t -> MTypes.clause
*)

val grab_args : Genlex.token Stream.t -> Genlex.token list
