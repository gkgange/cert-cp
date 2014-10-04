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
  prim.check_inf prim.CheckClause prim.check_clause
  cumulative.check_cumul reif.check_reif
  linear.CheckLinear linear.check_lincon
  element.check_element
  nat_of_int int_of_nat.
