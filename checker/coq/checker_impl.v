(* Extraction of the implemented checkers. *)
Require Import ExtrOcamlIntConv.
Require Import ExtrOcamlZInt.
Require prim.
Require bounds.
Require linear.
Require cumulative.
Require reif.
Require element.

Set Extraction Optimize.
Extraction "checker_impl.ml"
  prim.check_inf prim.check_clause
  cumulative.check_cumul
  cumulative.check_cumul_tt
  cumulative.check_cumul_bnd
  reif.check_reif
  linear.check_lincon
  linear.check_linear_bnd
  element.check_element
  element.check_element_bnd
  nat_of_int int_of_nat.
