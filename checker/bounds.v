(* Most of these than probably go. *)
Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import Compare_dec.
Require Import Omega.
Require Import Decidable.
(*
Require Import Logic.
Require Import Classical_Prop.
Require Import ClassicalFacts.
*)

Require Import prim.

Open Scope Z_scope.

(* Bounds on a variable. *)
Inductive bound :=
  | Unbounded : bound
  | Bounded : Z -> bound.

(* Evaluating bounds under an assignment. *)
Definition sat_lb (b : bound) (k : Z) :=
  match b with
  | Unbounded => True
  | Bounded k' => k' <= k
  end.

Definition eval_lb (x : ivar) (b : bound) (theta : asg) :=
  sat_lb b (eval_ivar x theta).

Definition sat_ub (b : bound) (k : Z) :=
  match b with
  | Unbounded => True
  | Bounded k' => k <= k'
  end.

Definition eval_ub (x : ivar) (b : bound) (theta : asg) :=
  sat_ub b (eval_ivar x theta).

Definition bound_le (x : bound) (y : bound) : Prop :=
  match x with
  | Unbounded => True
  | Bounded kx =>
    match y with
    | Unbounded => False
    | Bounded ky => kx <= ky
    end
  end.

Theorem bound_le_valid : forall (x y : bound),
  bound_le x y ->
    forall (v : ivar) (theta : asg),
      implies (eval_lb v y) (eval_lb v x).
Proof.
  intros. unfold implies; intros.
  unfold eval_lb in *; unfold sat_lb in *; unfold bound_le in H.
  destruct x. tauto.
  destruct y. omega. omega.
Qed.

Definition bound_leb (x : bound) (y : bound) : bool :=
  match x with
  | Unbounded => true
  | Bounded kx =>
    match y with
    | Unbounded => false
    | Bounded ky => Z_leb kx ky
    end
  end.
Theorem bound_le_iff : forall (x y : bound),
  bound_le x y <-> bound_leb x y = true.
Proof.
  intros. unfold bound_le; unfold bound_leb.
  destruct x. tauto.
  destruct y.
  split. tauto. intro; discriminate.
  assert (Z_leb z z0 = true <-> z <= z0).
  apply Z_leb_iff_le.
  rewrite H. tauto.
Qed.

Theorem unbound_le_l : forall (x : bound),
  bound_le Unbounded x.
Proof.
  intros. unfold bound_le; trivial.
Qed.

Theorem unbound_le_r : forall (x : bound),
  bound_le x Unbounded -> x = Unbounded.
Proof.
  intros. unfold bound_le in H.
  destruct x. trivial. tauto.
Qed.

Definition bound_max (x : bound) (y : bound) :=
  match x with
  | Unbounded => y
  | Bounded kx =>
    match y with
    | Unbounded => Bounded kx
    | Bounded ky =>
       Bounded (Zmax kx ky)
    end
  end.
Theorem bmax_ub_l : forall (x y : bound),
  bound_le x (bound_max x y).
Proof.
  intros. unfold bound_max.
  destruct x. apply unbound_le_l.
  destruct y.
  unfold bound_le. omega.
  unfold bound_le.
  Hint Resolve Z.le_max_l. eauto.
Qed.

Theorem bmax_valid : forall (v : ivar) (x : bound) (y : bound) (theta : asg),
  eval_lb v x theta /\ eval_lb v y theta -> eval_lb v (bound_max x y) theta.
Proof.
  intros. destruct H.
  unfold bound_max. destruct x. destruct y.
  exact H. exact H0.
  destruct y. exact H.
  unfold eval_lb in *.
  assert (z <= eval_ivar v theta ->
    z0 <= eval_ivar v theta -> Zmax z z0 <= eval_ivar v theta).
  apply Zmax_lub. apply H1. exact H. exact H0.
Qed.


Definition bound_add (x : bound) (y : bound) :=
  match x with
  | Unbounded => Unbounded
  | Bounded kx =>
    match y with 
    | Unbounded => Unbounded
    | Bounded ky => Bounded (kx + ky)
    end
  end.

Theorem lb_impl_addlb : forall (k k' : Z) (bk bk' : bound),
  sat_lb bk k /\ sat_lb bk' k' -> sat_lb (bound_add bk bk') (k + k').
Proof.
  intros.
  destruct H as [H1 H2].
  unfold sat_lb in *; unfold bound_add.
  destruct bk, bk'.
  trivial. trivial. trivial. omega.
Qed.
  

Definition lb_from_lit (x : ivar) (l : lit) :=
  match l with
  | Pos (IEq x' k) =>
      if beq_nat x x' then Bounded k else Unbounded
  | Neg (ILeq x' k) =>
      if beq_nat x x' then Bounded (k+1%Z) else Unbounded
  | _ => Unbounded
  end.
Theorem lb_from_lit_valid : forall (x : ivar) (l : lit),
  implies (eval_lit l) (eval_lb x (lb_from_lit x l)).
Proof.
  intros. unfold implies; intros.
  unfold eval_lb; unfold sat_lb; unfold lb_from_lit.
  destruct l. unfold eval_lit in H; unfold eval_vprop in H.
  induction v.
  trivial.
  assert (beq_nat x i = true <-> x = i).
  apply beq_nat_true_iff.
  destruct (beq_nat x i).
  destruct H0.
  assert (x = i). apply H0; tauto. rewrite H2. rewrite H. omega.
  trivial. trivial.
  induction v.
  assert (beq_nat x i = true <-> x = i). apply beq_nat_true_iff.
  destruct (beq_nat x i).
  assert (x = i). apply H0; trivial. rewrite H1.
  unfold eval_lit in H; unfold eval_vprop in H.
  assert (~(eval_ivar i theta <= z) -> eval_ivar i theta > z).
  apply Znot_le_gt.
  assert (eval_ivar i theta > z).
  apply H2; exact H.
  apply Zlt_le_succ. apply Zgt_lt. exact H3.
  trivial.
  trivial.
  trivial.
Qed.

Fixpoint lb_from_negclause (x : ivar) (cl : clause) :=
  match cl with
  | nil => Unbounded
  | cons l ls => bound_max (lb_from_lit x (neglit l)) (lb_from_negclause x ls)
  end.

Theorem lb_from_negclause_valid : forall (x : ivar) (cl : clause) (theta : asg),
 ~eval_clause cl theta -> eval_lb x (lb_from_negclause x cl) theta.
Proof.
  intros.
  induction cl.
  unfold lb_from_negclause; unfold eval_lb; unfold sat_lb; trivial.
  unfold eval_clause in H; fold eval_clause in H.
  assert (~(eval_lit a theta) /\ ~(eval_clause cl theta)).
  apply Decidable.not_or; exact H. destruct H0.
  assert (eval_lit (neglit a) theta).
  apply neglit_not_lit. exact H0.
  unfold lb_from_negclause ; fold lb_from_negclause.
  assert (eval_lb x (lb_from_lit x (neglit a)) theta).
  apply lb_from_lit_valid; exact H2.
  assert (eval_lb x (lb_from_negclause x cl) theta).
  apply IHcl; exact H1.
  apply bmax_valid. split. exact H3. exact H4.
Qed.

(* FIXME: Implement UB handling. *)
