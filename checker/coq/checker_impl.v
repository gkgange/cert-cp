(* Extraction of the implemented checkers. *)
Require Import ExtrOcamlIntConv.
Require Import ExtrOcamlZInt.
Require model.
Require resolution.
Require log.

(*
Extract Constant prim.Z_eqb => "(=)".
*)

Set Extraction Optimize.
Extraction "checker_impl.ml"
  model.cst
  model.make_linear
  model.make_cumul
  model.make_element
  model.make_clause

  resolution.resolvable

  log.asg
  log.asg_of_alist
  log.certify_unsat
  log.certify_optimal
  log.check_inference_model

  nat_of_int int_of_nat.
