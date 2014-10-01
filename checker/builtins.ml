(* Built-in checkers.
 * Additional checkers can also be registered
 * at runtime. *)
module R = Registry
module C = Checker
module MT = MTypes
module P = Parse

let null_checker spec =
  fun tokens ->
    let _ = spec tokens in
    {
      C.repr = "null-checker" ;
      C.check = (fun cl -> false)
    }

let register () =
  R.add "clause" (fun model -> null_checker (P.parse_clause model))
