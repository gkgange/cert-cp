Require Import Bool.
Require Import prim.

Definition reified (C : Constraint) : Type :=
  (lit * C.(T))%type.

Definition eval_reif (C : Constraint) (r : reified C) (theta : asg) :=
  (eval_lit (neglit (fst r)) theta) \/ C.(eval) (snd r) theta.

Definition check_reif (C : Constraint) (Ch : Checker C) (r : reified C) (cl : clause) : bool :=
  andb (check_clause (cons (neglit (fst r)) nil) cl) ((check C Ch) (snd r) cl).
Theorem check_reif_valid : forall (C : Constraint) (Ch : Checker C) (r : reified C) (cl : clause),
  check_reif C Ch r cl = true -> implies (eval_reif C r) (eval_clause cl).
Proof.
  unfold check_reif, implies, eval_reif. intros C Ch r cl.
  rewrite andb_true_iff.
  intros.
  destruct H.
  destruct H0 as [Hnr | Hc].
  assert (implies (eval_clause (cons (neglit (fst r)) nil)) (eval_clause cl)).
  apply check_clause_valid ; exact H.
  unfold implies in H0.
  apply H0.
  unfold eval_clause. tauto.

  assert ((check C Ch) (snd r) cl = true -> implies (C.(eval) (snd r)) (eval_clause cl)).
  apply (check_valid C Ch).
  unfold implies in H0.
  apply H0. exact H1. exact Hc.
Qed.

Definition ReifiedConstraint (C : Constraint) : Constraint :=
  mkConstraint (reified C) (eval_reif C).
Definition ReifiedCheck (C : Constraint) (Ch : Checker C) :=
  mkChecker (ReifiedConstraint C) (check_reif C Ch) (check_reif_valid C Ch).