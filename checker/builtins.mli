(* Registering built-in checkers. *)
val register : unit -> unit

val tauto : MTypes.bounds -> MTypes.clause -> bool
val clause_subsumes : MTypes.clause -> MTypes.clause -> bool
