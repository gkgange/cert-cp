(* Extraction of the implemented checkers. *)
Require Import ExtrOcamlIntConv.
Require Import ExtrOcamlZInt.
Require model.
Require resolution.
Require log.

(*
Extract Constant Z.eqb => "(=)".
Extract Constant Z.leb => "(<=)".
Extract Constant Z.ltb => "(<)".
*)

Set Extraction Optimize.
Extraction "checker_impl.ml"
  model.cst
  model.make_linear
  model.make_lin_ne
  model.make_cumul
  model.make_element
  model.make_clause
  model.make_arith_eq
  model.make_arith_ne
  model.domset_of_bounds

  resolution.resolvable

  log.asg
  log.asg_of_alist
  log.cst_map_of_csts
  log.certify_unsat
  log.certify_optimal
  log.check_inference_model
  log.check_inference_domset

  log.domset_with_lt
  log.check_inference

  nat_of_int int_of_nat.
