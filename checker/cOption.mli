(** Options and command-line parsing **)
val infile : string option ref
val modules : string list ref
val verbosity : int ref
val stream : bool ref

(* --------------------------------------------- *)
(*       Specification list for options          *)
(* --------------------------------------------- *)
val speclist : (Arg.key * Arg.spec * Arg.doc) list ;;
