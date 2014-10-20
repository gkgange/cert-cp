(* Registering built-in checkers. *)
val register : unit -> unit

val tauto : MTypes.bounds -> MTypes.clause -> bool
