(* Types for models. *)
type model

type t = model

val create : unit -> model

val add_ivar : t -> MTypes.ident -> (int*int) option -> unit
val add_bvar : t -> MTypes.ident -> unit
val add_vprop : t -> MTypes.ident -> MTypes.vprop -> unit
val add_checker : t -> MTypes.ident -> Checker.t -> unit

val get_ivar : t -> MTypes.ident -> MTypes.ivar

val get_vprop : t -> MTypes.ident -> MTypes.vprop

val get_checker : t -> MTypes.ident -> Checker.t
