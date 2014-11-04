(* Extraction of the implemented checkers. *)
Require Import ExtrOcamlIntConv.
Require Import ExtrOcamlZInt.
Require prim.
Require bounds.
Require linear.
Require cumulative.
Require cumul_dset.
Require reif.
Require element.

Extract Constant prim.Z_eqb => "(=)".

Set Extraction Optimize.
Extraction "checker_impl.ml"
  prim.check_inf prim.check_clause
  (* domain.check_tauto *)
  domain.check_tauto_bnd
  domset.bounds_domset
  (*
  cumulative.check_cumul
  cumulative.check_cumul_tt
  *)
  cumulative.check_cumul_bnd
  cumulative.check_cumul_tt_bnd
  cumul_dset.check_cumul_tt_dbnd
  reif.check_reif
  (* linear.check_lincon *)
  linear.check_linear_bnd
  (* element.check_element *)
  element.check_element_bnd
  nat_of_int int_of_nat.
