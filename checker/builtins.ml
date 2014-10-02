(* Built-in checkers.
 * Additional checkers can also be registered
 * at runtime. *)
module R = Registry
module C = Checker
module MT = MTypes
module P = Parse
module S = Spec
module C_impl = Checker_impl

let impl_vprop_of_vprop = function
| MT.ILe (x, k) -> C_impl.ILeq (C_impl.nat_of_int x, k)
| MT.IEq (x, k) -> C_impl.IEq (C_impl.nat_of_int x, k)
| MT.BTrue x -> C_impl.BTrue (C_impl.nat_of_int x)

let impl_lit_of_lit = function
| MT.Pos vp -> C_impl.Pos (impl_vprop_of_vprop vp)
| MT.Neg vp -> C_impl.Neg (impl_vprop_of_vprop vp)

let impl_clause_of_clause = List.map impl_lit_of_lit

let int_list = S.listof S.intconst
let ivar_list model = S.listof (P.parse_ivar model)

let check_linear_le model =
 fun tokens ->
   let (coeffs, (vars, k)) =
     (S.cons int_list (S.cons (ivar_list model) S.intconst)) tokens in
   let linterms = List.map2 (fun c v -> (c, C_impl.nat_of_int v)) coeffs vars in
{
  C.repr = "linear_le" ;
  C.check =
    (fun cl ->
      C_impl.check_lincon (linterms, k) (impl_clause_of_clause cl))
}

let register () =
  R.add "linear_le" check_linear_le
(*
  R.add "clause" R.null_checker ;
  R.add "linear_le" R.null_checker
  *)
