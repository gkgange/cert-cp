(* Types for models. *)
type model

type t = model

val create : unit -> model

val add_ivar : t -> MTypes.ident -> (int*int) option -> unit
val add_bvar : t -> MTypes.ident -> unit
val add_lit : t -> MTypes.ident -> MTypes.lit -> unit
val add_checker : t -> MTypes.ident -> Checker.t -> unit
val add_sol_check : t -> MTypes.ident -> SolCheck.t -> unit

val get_ivar : t -> MTypes.ident -> MTypes.ivar
val get_bvar : t -> MTypes.ident -> MTypes.bvar

val ivar_name : t -> MTypes.ivar -> MTypes.ident
val bvar_name : t -> MTypes.bvar -> MTypes.ident

val get_lit : t -> MTypes.ident -> MTypes.lit

val get_checker : t -> MTypes.ident -> Checker.t
val get_all_checkers : t -> Checker.t list

val get_sol_checkers : t -> SolCheck.t list

val string_of_vprop : t -> MTypes.vprop -> string
val string_of_lit : t -> MTypes.lit -> string
val string_of_clause : t -> MTypes.clause -> string

val get_bounds : t -> MTypes.bounds

val lits_iteri : (int -> MTypes.ident -> MTypes.lit -> unit) -> t -> unit
