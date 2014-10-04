Require Import Bool.
Require Import prim.

Definition reified (C : Constraint) : Type :=
  (lit * C.(T))%type.

Definition eval_reif (C : Constraint) (r : reified C) (theta : asg) :=
  (eval_lit (neglit (fst r)) theta) \/ C.(eval) (snd r) theta.

Definition check_reif (C : Constraint) (r : reified C) (cl : clause) : bool :=
  andb (check_clause (cons (neglit (fst r)) nil) cl) (C.(check) (snd r) cl).
Theorem check_reif_valid : forall (C : Constraint) (r : reified C) (cl : clause),
  check_reif C r cl = true -> implies (eval_reif C r) (eval_clause cl).
Proof.
  unfold check_reif, implies, eval_reif. intros C r cl.
  rewrite andb_true_iff.
  intros.
  destruct H.
  destruct H0 as [Hnr | Hc].
  assert (implies (eval_clause (cons (neglit (fst r)) nil)) (eval_clause cl)).
  apply check_clause_valid ; exact H.
  unfold implies in H0.
  apply H0.
  unfold eval_clause. tauto.

  assert (C.(check) (snd r) cl = true -> implies (C.(eval) (snd r)) (eval_clause cl)).
  apply C.(check_valid).
  unfold implies in H0.
  apply H0. exact H1. exact Hc.
Qed.

Definition ReifiedConstraint (C : Constraint) : Constraint :=
  mkConstraint (reified C) (eval_reif C) (check_reif C) (check_reif_valid C).
