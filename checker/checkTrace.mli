(* Check correspondence between a model
 * and the initial clauses of a resolution proof. *)
val assumptions : Model.t -> (int, MTypes.lit) Hashtbl.t ->
  Genlex.token Stream.t -> MTypes.clause list
