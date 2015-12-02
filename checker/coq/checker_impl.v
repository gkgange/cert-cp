(* Extraction of the implemented checkers. *)
Require Import ExtrOcamlIntConv.
Require Import ExtrOcamlZInt.
Require prim.
Require bounds.
Require linear.
Require linear_dset.
Require cumulative.
Require cumul_dset.
Require reif.
Require element.
Require element_dset.
Require log.

Extract Constant prim.Z_eqb => "(=)".

Set Extraction Optimize.
Extraction "checker_impl.ml"
  sol.asg_of_alist
  prim.check_inf prim.check_clause
  (* domain.check_tauto *)
  domain.check_tauto_bnd
  domset.bounds_domset
  domset.check_tauto_dbnd
  (*
  cumulative.check_cumul
  cumulative.check_cumul_tt
  *)
  cumulative.check_cumul_sol
  cumulative.check_cumul_bnd
  cumulative.check_cumul_tt_bnd
  cumul_dset.check_cumul_tt_dbnd
  reif.check_reif
  (* linear.check_lincon *)
  linear.check_lincon_sol
  linear.check_linear_bnd
  linear_dset.check_linear_dbnd
  linear_dset.check_reif_linear_dbnd
  (* element.check_element *)
  element.check_element_bnd
  element_dset.check_elem_dbnd
  element_dset.check_reif_elem_dbnd
  model.cst
  model.make_linear
  model.make_cumul
  model.make_element
  log.certify_unsat
  nat_of_int int_of_nat.

