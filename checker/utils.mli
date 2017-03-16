(* Assorted utility functions *)
val print_list :
  ?pre:((unit, Format.formatter, unit) format) ->
  ?sep:((unit, Format.formatter, unit) format) ->
  ?post:((unit, Format.formatter, unit) format) ->
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit
val print_dynarray :
  ?sep:(unit, Format.formatter, unit) format -> (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a DynArray.t -> unit

val chomp : 'a Stream.t -> 'a -> unit
