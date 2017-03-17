(** Module for reading binary logs *)
val create : (string, int) Hashtbl.t -> in_channel -> (unit -> Checker_impl.step)
