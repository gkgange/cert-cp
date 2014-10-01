(* Built-in checkers.
 * Additional checkers can also be registered
 * at runtime. *)
module R = Registry
module C = Checker
module MT = MTypes
module P = Parse
module S = Spec

let int_list = S.listof S.intconst
let ivar_list model = S.listof (P.parse_ivar model)

let register () = ()
(*
  R.add "clause" R.null_checker ;
  R.add "linear_le" R.null_checker
  *)
