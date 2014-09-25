Require Import Bool.
Require Import ZArith.
Require List.
Require Import prim.
Require Import bounds.

(* Exact representation of a variable domain. *)

(* A bounded interval, and a set of gaps. *)
Definition dom : Type := (dbound * (list Z))%type.

Definition dom_unconstrained : dom := ((Unbounded, Unbounded), nil).
Definition dom_const (k : Z) : dom := ((Bounded k, Bounded k), nil).
Definition dom_neq (k : Z) : dom := ((Unbounded, Unbounded), cons k nil).
Definition dom_le (k : Z) : dom := ((Unbounded, Bounded k), nil).
Definition dom_ge (k : Z) : dom := ((Bounded k, Unbounded), nil).

Fixpoint sat_holes (xs : list Z) (k : Z) := 
  match xs with
  | nil => True
  | cons x xs' => x <> k /\ (sat_holes xs' k)
  end.

Fixpoint satb_holes (xs : list Z) (k : Z) :=
  match xs with
  | nil => true
  | cons x xs' => negb (Z_eqb x k) && (satb_holes xs' k)
  end.

Theorem satb_holes_iff_holes : forall (ls : list Z) (k : Z),
  satb_holes ls k = true <-> sat_holes ls k.
Proof.
  intros. induction ls.
  unfold satb_holes, sat_holes. tauto.
  
  unfold satb_holes, sat_holes; fold satb_holes; fold sat_holes.
  rewrite andb_true_iff. rewrite negb_true_iff.
  assert (Z_eqb a k = true <-> a = k). apply Z_eqb_iff_eq.
  destruct (Z_eqb a k).
  split.
 
  intro. destruct H0. discriminate.
  
  intro. destruct H0. assert (a = k). apply H. tauto.
  rewrite H2 in H0. tauto.

  assert (a = k \/ a <> k). tauto.
  destruct H0.
  apply H in H0. discriminate.
  rewrite IHls.
  tauto.
Qed.

Definition sat_dom (d : dom) (k : Z) :=
  sat_dbound (fst d) k /\ sat_holes (snd d) k. 

Definition satb_dom (d : dom) (k : Z) :=
  satb_dbound (fst d) k && satb_holes (snd d) k.

Theorem satb_dom_true_iff_dom : forall (d : dom) (k : Z),
  satb_dom d k = true <-> sat_dom d k.
Proof.
  unfold satb_dom; unfold sat_dom. intros.
  rewrite andb_true_iff.
  rewrite satb_dbound_iff_db; rewrite satb_holes_iff_holes.
  tauto.
Qed.

Definition dom_from_lit (x : ivar) (l : lit) :=
  match l with
  | Pos (IEq x' k) =>
     if beq_nat x x' then dom_const k else dom_unconstrained
  | Neg (IEq x' k) =>
     if beq_nat x x' then dom_neq k else dom_unconstrained
  | Pos (ILeq x' k) =>
     if beq_nat x x' then dom_le k else dom_unconstrained
  | Neg (ILeq x' k) =>
     if beq_nat x x' then dom_ge (k+1) else dom_unconstrained
  | _ => dom_unconstrained
  end.
Theorem dom_from_lit_exact : forall (x : ivar) (l : lit) (theta : asg),
  eval_lit l theta <-> sat_dom (dom_from_lit x l) (eval_ivar x theta).
Proof.
  unfold eval_lit, eval_vprop, dom_from_lit, sat_dom, sat_dbound.
  unfold sat_lb, sat_ub. intros.
  destruct l. destruct v.

  unfold dom_le, dom_unconstrained.
  assert (beq_nat x i = true <-> x = i). apply beq_nat_true_iff.
  destruct beq_nat; simpl in *.
  assert (x = i). apply H; trivial.
  rewrite <- H0. tauto.
Qed.

Fixpoint dom_from_negclause (x : ivar) (cl : clause) :=
  match cl with
  | nil => dom_unconstrained
  | cons l : ls =>
      dom_meet (dom_from_neglit l) (
