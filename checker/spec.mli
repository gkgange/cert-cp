(* Parameter specifications for constraints. *)
val lexer : char Stream.t -> Genlex.token Stream.t

type 'a spec = (Genlex.token Stream.t -> 'a)

val ident : string spec
val intconst : int spec
val boolconst : bool spec
val listof : 'a spec -> ('a list) spec
val cons : 'a spec -> 'b spec -> ('a * 'b) spec
