(* Check correspondence between a model (with inferences)
 * and the initial clauses of a resolution proof. *)
val check : Model.t -> MTypes.clause list -> 
  Genlex.token Stream.t -> bool
