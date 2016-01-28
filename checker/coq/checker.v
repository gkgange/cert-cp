(* Constraint checkers *)
Require Import assign.
Require Import domain.
Require Import constraint.
Require model.
Require Import clause_domain.
Require Import lit.

Definition infer_check_bnd (C : Constraint) (Ch : UnsatChecker C) (x : C.(T)) (ds : domset) (cl : clause) := 
  check_unsat C Ch x (domset_with_prod ds (negclause cl)).
Lemma infer_check_bnd_valid : forall C Ch x ds cl,
  infer_check_bnd C Ch x ds cl = true -> forall theta,
    eval_domset ds theta -> eval C x theta -> eval_clause cl theta.
Proof.
  intros C Ch x ds cl; unfold infer_check_bnd; intros.
  apply check_unsat_valid in H; unfold cst_is_unsat in H; specialize (H theta).

  rewrite domset_with_prod_iff in H.
  
  apply eval_clause_notprod; intro; tauto.
Qed.

