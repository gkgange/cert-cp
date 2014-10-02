(* Extraction of the implemented checkers. *)
Require Import ExtrOcamlIntConv.
Require Import ExtrOcamlZInt.
Require bounds.
Require linear.
Require cumulative.
Require reif.
Require element.

Set Extraction Optimize.
Extraction "checker_impl.ml" cumulative.check_cumul reif.check_reif linear.check_lincon
  nat_of_int int_of_nat.
