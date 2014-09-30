(* Registry of checkers for constraint classes. *)

(* Register a new checker kind. *)
val add : MTypes.ident -> (Genlex.token Stream.t -> Checker.t) -> unit

(* Find the checker-constructor for the given class. *)
val find : MTypes.ident -> Genlex.token Stream.t -> Checker.t
