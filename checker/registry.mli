(* Registry of checkers for constraint classes. *)

(* Register a new checker kind. *)
val add : MTypes.ident -> (Model.t -> Genlex.token Stream.t -> Checker.t) -> unit
val add_sol : MTypes.ident -> (Model.t -> Genlex.token Stream.t -> SolCheck.t) -> unit

(* Find the checker-constructor for the given class. *)
val find : MTypes.ident -> Model.t -> Genlex.token Stream.t -> Checker.t
val find_sol : MTypes.ident -> Model.t -> Genlex.token Stream.t -> SolCheck.t

(* A null checker; always returns false. *)
val null_checker : Model.t -> Genlex.token Stream.t -> Checker.t
val null_sol_checker : Model.t -> Genlex.token Stream.t -> SolCheck.t
