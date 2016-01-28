(* Abstract types for constraints. *)
Require Import assign.
Require Import domain.

Record Constraint : Type := mkConstraint
  { T : Type ;
    eval : T -> valuation -> Prop }.

Definition cst_is_unsat (C : Constraint) (x : C.(T)) (ds : domset) :=
  forall theta, eval_domset ds theta -> C.(eval) x theta -> False.

Record UnsatChecker (C : Constraint) := mkUnsatChecker
  {
    check_unsat : C.(T) -> domset -> bool ;
    check_unsat_valid :
      forall (x : C.(T)) (ds : domset), check_unsat x ds = true -> cst_is_unsat C x ds
  }.

Record SolChecker (C : Constraint) := mkSolChecker
  {
    check_sol : C.(T) -> valuation -> bool ;
    check_sol_valid :
      forall (x : C.(T)) (sol : valuation), check_sol x sol = true -> C.(eval) x sol
  }.