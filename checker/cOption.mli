(** Options and command-line parsing **)
val infile : string option ref
val tracefile : string option ref
val bintrace : bool ref
val solfile : string option ref
val objective : string option ref
val litfile : string option ref
val modules : string list ref
val verbosity : int ref
val stream : bool ref
val no_resolve : bool ref
val debug : bool ref

type trace_kind =
  | IDrup (* DRUP with axiom introduction. *)
  | Dres (* Resolution proof with deletion *)

val tracemode : trace_kind ref

(* --------------------------------------------- *)
(*       Specification list for options          *)
(* --------------------------------------------- *)
val speclist : (Arg.key * Arg.spec * Arg.doc) list ;;
