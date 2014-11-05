(* Registering built-in checkers. *)
val register : unit -> unit

val tauto : MTypes.bounds -> MTypes.clause -> bool
val tauto_dbnd : Checker_impl.domset -> MTypes.clause -> bool
val clause_subsumes : MTypes.clause -> MTypes.clause -> bool
