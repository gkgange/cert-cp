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

Definition dbound := (bound * bound)%type.

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

Definition sat_dbound (db : dbound) (k : Z) :=
  sat_lb (fst db) k /\ sat_ub (snd db) k.

Definition satb_lb (b : bound) (k : Z) :=
  match b with
  | Unbounded => true
  | Bounded k' => Z_leb k' k
  end.
Theorem satb_lb_iff_lb : forall (b : bound) (k : Z),
  satb_lb b k = true <-> sat_lb b k.
Proof.
  unfold satb_lb, sat_lb; intros; destruct b.
  tauto.
  apply Z_leb_iff_le.
Qed.

Definition satb_ub (b : bound) (k : Z) :=
  match b with
  | Unbounded => true
  | Bounded k' => Z_leb k k'
  end.
Theorem satb_ub_iff_ub : forall (b : bound) (k : Z),
  satb_ub b k = true <-> sat_ub b k.
Proof.
  unfold satb_ub, sat_ub; intros; destruct b.
  tauto.
  apply Z_leb_iff_le.
Qed.
Definition satb_dbound (db : dbound) (k : Z) :=
  satb_lb (fst db) k && satb_ub (snd db) k.
Theorem satb_dbound_iff_db : forall (db : dbound) (k : Z),
  satb_dbound db k = true <-> sat_dbound db k.
Proof.
  unfold satb_dbound, sat_dbound. intros.
  destruct db; simpl.

  assert (satb_lb b k = true <-> sat_lb b k).
  apply satb_lb_iff_lb.
  assert (satb_ub b0 k = true <-> sat_ub b0 k).
  apply satb_ub_iff_ub.
  rewrite <- H; rewrite <- H0.
  apply andb_true_iff.
Qed.

Theorem decidable_sat_db : forall (db : dbound) (k : Z),
  sat_dbound db k \/ ~ sat_dbound db k.
Proof.
  unfold sat_dbound, sat_lb, sat_ub; intros.
  destruct db; simpl.

  destruct b, b0.
  tauto.
  tauto.
  tauto.
  omega.
Qed.

Theorem Zle_satub_trans : forall (b : bound) (k k' : Z),
  Zle k k' -> sat_ub b k' -> sat_ub b k.
Proof.
  unfold sat_ub; intros.
  destruct b.
  trivial. omega.
Qed.
  
Theorem Zle_notub_trans : forall (b : bound) (k k' : Z),
  Zle k k' -> ~sat_ub b k -> ~sat_ub b k'.
Proof.
  unfold sat_ub; intros.
  destruct b.
  exact H0.
  omega.
Qed.

Theorem Zle_notlb_trans : forall (b : bound) (k k' : Z),
  Zle k k' -> ~sat_lb b k' -> ~sat_lb b k.
Proof.
  unfold sat_lb; intros.
  destruct b.
  exact H0. omega.
Qed.

Theorem satb_ub_false_iff_notub : forall (b : bound) (k : Z),
  satb_ub b k = false <-> ~ sat_ub b k.
Proof.
  intros.
  unfold satb_ub, sat_ub.
  destruct b.
 
  split.
  intro; discriminate.
  tauto.
  apply Z_leb_false_iff_notle.
Qed.

Theorem satb_lb_false_iff_notlb : forall (b : bound) (k : Z),
  satb_lb b k = false <-> ~ sat_lb b k.
Proof.
  intros.
  unfold satb_lb, sat_lb; destruct b.

  split.
  intro; discriminate.
  intro. tauto.
  apply Z_leb_false_iff_notle.
Qed.

Theorem satb_db_false_iff_notdb : forall (db : dbound) (k : Z),
  satb_dbound db k = false <-> ~ sat_dbound db k.
Proof.
  intros.
  assert (sat_dbound db k \/ ~sat_dbound db k). apply decidable_sat_db.
  destruct H.
  assert (satb_dbound db k = true). apply satb_dbound_iff_db. exact H.
  rewrite H0.
  split. discriminate.
  intro. assert False. tauto. tauto.
 
  split.
  assert (sat_dbound db k -> satb_dbound db k = true). apply satb_dbound_iff_db.
  intro. tauto.
  
  intro.
  apply not_true_is_false.
  rewrite satb_dbound_iff_db. exact H.
Qed.

Definition eval_dbound (x : ivar) (db : dbound) (theta : asg) :=
  sat_dbound db (eval_ivar x theta).

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

Theorem bmax_valid : forall (x : bound) (y : bound) (k : Z),
  sat_lb x k /\ sat_lb y k -> sat_lb (bound_max x y) k.
Proof.
  intros. destruct H.
  unfold bound_max. destruct x. destruct y.
  exact H. exact H0.
  destruct y. exact H.
  unfold sat_lb in *.
  assert (z <= k ->
    z0 <= k -> Zmax z z0 <= k).
  apply Zmax_lub. apply H1. exact H. exact H0.
Qed.

Definition bound_min (x : bound) (y : bound) :=
  match x with
  | Unbounded => y
  | Bounded kx =>
    match y with
    | Unbounded => Bounded kx
    | Bounded ky =>
       Bounded (Zmin kx ky)
    end
  end.

Theorem bmin_valid : forall (x : bound) (y : bound) (k : Z),
  sat_ub x k /\ sat_ub y k -> sat_ub (bound_min x y) k.
Proof.
  intros. destruct H.
  unfold bound_min. destruct x. destruct y.
  exact H. exact H0.
  destruct y. exact H. unfold sat_ub in *.
  assert (k <= z ->
    k <= z0 -> k <= Zmin z z0).
  apply Zmin_glb. apply H1. exact H. exact H0.
Qed.

Definition bound_add (u v : bound) :=
  match u with
  | Unbounded => Unbounded
  | Bounded x =>
    match v with
    | Unbounded => Unbounded
    | Bounded y => Bounded (x + y)
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

Definition db_add (du dv : dbound) :=
  (bound_add (fst du) (fst dv), bound_add (snd du) (snd dv)).
Theorem db_impl_adddb : forall (k k' : Z) (bk bk' : dbound),
  sat_dbound bk k /\ sat_dbound bk' k' -> sat_dbound (db_add bk bk') (k+k').
Proof.
  unfold sat_dbound, db_add; unfold sat_lb, sat_ub, bound_add.
  destruct bk, bk'; simpl.
  intros. destruct H as [Hk Hk'].
  destruct Hk as [Hkl Hku]; destruct Hk' as [Hk'l Hk'u].
  split.
  
  destruct b.

  trivial.
  destruct b1.
  trivial.
  omega.

  destruct b0.
  trivial.
  destruct b2.
  trivial.
  omega.
Qed.

Definition db_meet (dx : dbound) (dy : dbound) :=
  (bound_max (fst dx) (fst dy), bound_min (snd dx) (snd dy)).
Theorem db_sat_impl_meet : forall (dx dy : dbound) (k : Z),
  sat_dbound dx k /\ sat_dbound dy k -> sat_dbound (db_meet dx dy) k.
Proof.
  unfold sat_dbound; intros.
  destruct H as [Hx Hy].
  destruct Hx as [Hlx Hux]; destruct Hy as [Hly Huy].
  unfold db_meet.
  destruct dx, dy.
  simpl in *. 
  split.
  apply bmax_valid.
  split. exact Hlx. exact Hly.
  apply bmin_valid.
  split. exact Hux. exact Huy.
Qed.

Definition minus_bound (u : bound) :=
  match u with
  | Unbounded => Unbounded
  | Bounded x => Bounded (-x)
  end.
Theorem sat_lb_iff_minus_ub : forall (u : bound) (k : Z),
  sat_lb u k <-> sat_ub (minus_bound u) (-k).
Proof.
  unfold minus_bound; unfold sat_lb; unfold sat_ub; intros.
  destruct u. tauto. omega.
Qed.

Theorem sat_ub_iff_minus_lb : forall (u : bound) (k : Z),
  sat_ub u k <-> sat_lb (minus_bound u) (-k).
Proof.
  unfold minus_bound, sat_lb, sat_ub; intros.
  destruct u. tauto. omega.
Qed.

Definition mul_pos_bound (k : Z) (u : bound) :=
  match u with
  | Unbounded => Unbounded
  | Bounded x => Bounded (k*x)
  end.
Theorem mul_pos_bound_ub_valid : forall (k k' : Z) (u : bound),
  k > 0%Z -> (sat_ub u k' <-> sat_ub (mul_pos_bound k u) (k*k')).
Proof.
  unfold mul_pos_bound, sat_ub; intros.
  destruct u. tauto.
  split.
  intro. 
  assert (k > 0 -> k' <= z -> k'*k <= z*k). apply Zmult_gt_0_le_compat_r.
  eauto with zarith.
  intro.
  assert (k > 0 -> k'*k <= z*k -> k' <= z). apply Zmult_le_reg_r.
  apply H1. exact H.
  rewrite Zmult_comm; apply Zge_le; rewrite Zmult_comm; apply Zle_ge; exact H0.
Qed.

Theorem mul_pos_bound_lb_valid : forall (k k' : Z) (u : bound),
  k > 0%Z -> (sat_lb u k' <-> sat_lb (mul_pos_bound k u) (k*k')).
Proof.
  unfold mul_pos_bound, sat_lb; intros.
  destruct u. tauto.
  split.
  intro. 
  assert (k > 0 -> k' <= z -> k'*k <= z*k). apply Zmult_gt_0_le_compat_r.
  eauto with zarith.
  intro.
  assert (k > 0 -> z*k <= k'*k -> z <= k'). apply Zmult_le_reg_r.
  apply H1. exact H.
  rewrite Zmult_comm; apply Zge_le; rewrite Zmult_comm; apply Zle_ge; exact H0.
Qed.

Definition minus_dbound (db : dbound) :=
  (minus_bound (snd db), minus_bound (fst db)).
Theorem sat_minus_dbound_iff : forall (db : dbound) (k : Z),
  sat_dbound db k <-> sat_dbound (minus_dbound db) (-k).
Proof.
  unfold sat_dbound; unfold minus_dbound; intros.
  destruct db; simpl.
  split.
  intro. destruct H as [Hpl Hpu].
  split.
  apply sat_ub_iff_minus_lb; exact Hpu.
  apply sat_lb_iff_minus_ub; exact Hpl.
  intro. destruct H as [Hml Hmu].
  split.
  apply sat_lb_iff_minus_ub; exact Hmu.
  apply sat_ub_iff_minus_lb; exact Hml.
Qed.

Theorem sat_minus_dbound_if : forall (db : dbound) (k : Z),
  sat_dbound db k -> sat_dbound (minus_dbound db) (-k).
Proof.
  intros.
  assert (sat_dbound db k <-> sat_dbound (minus_dbound db) (-k)) as Hiff.
  apply sat_minus_dbound_iff.
  destruct Hiff.
  apply H0. exact H.
Qed.


Definition mul_pos_dbound (k : Z) (db : dbound) :=
  (mul_pos_bound k (fst db), mul_pos_bound k (snd db)).
Theorem mul_pos_dbound_valid : forall (c : Z) (k : Z) (db : dbound),
  c > 0 -> sat_dbound db k -> sat_dbound (mul_pos_dbound c db) (c*k).
Proof.
  unfold sat_dbound, mul_pos_dbound; destruct db. simpl. intros.
  destruct H0 as [Hl Hu].
  split.
  apply mul_pos_bound_lb_valid. exact H. exact Hl.
  apply mul_pos_bound_ub_valid. exact H. exact Hu.
Qed.

Definition mul_neg_dbound (k : Z) (db : dbound) :=
  minus_dbound (mul_pos_dbound (-k) db).
Theorem mul_neg_dbound_valid : forall (c : Z) (k : Z) (db : dbound),
  c < 0 -> sat_dbound db k -> sat_dbound (mul_neg_dbound c db) (c*k).
Proof.
  unfold mul_neg_dbound. intros.
  assert ((-c) > 0). omega.
  assert (sat_dbound (mul_pos_dbound (- c) db) ((-c)*k)).
  apply mul_pos_dbound_valid. exact H1. exact H0.
  rewrite <- Zopp_involutive with (n := c*k).
  apply sat_minus_dbound_if.
  rewrite Zopp_mult_distr_l. exact H2.
Qed.

Definition mul_z_dbound (k : Z) (db : dbound) :=
  match Zcompare k 0%Z with
  | Eq => (Bounded 0%Z, Bounded 0%Z)
  | Gt => mul_pos_dbound k db
  | Lt => mul_neg_dbound k db
  end.

Theorem mul_z_dbound_valid : forall (c : Z) (k : Z) (db : dbound),
  sat_dbound db k -> sat_dbound (mul_z_dbound c db) (c*k).
Proof.
  intros.
  unfold mul_z_dbound; intros.
  apply Zcompare_rec with (n := c) (m := 0%Z).
  intro.
  assert (c = 0) as Hc0. apply Zcompare_Eq_iff_eq; exact H0.
  destruct (Zcompare c 0).
  unfold sat_dbound, sat_lb, sat_ub; rewrite Hc0; simpl. omega.
  discriminate. discriminate.

  intro.
  assert (c < 0). eauto with zarith.
  destruct (Zcompare c 0).
  discriminate.
  apply mul_neg_dbound_valid. exact H1. exact H.
  discriminate.
  
  intro.
  assert (c > 0). eauto with zarith.
  destruct (Zcompare c 0).
  discriminate.
  discriminate.
  apply mul_pos_dbound_valid. exact H1. exact H.
Qed.

Definition db_from_lit (x : ivar) (l : lit) :=
  match l with
  | Pos (IEq x' k) =>
      if beq_nat x x' then (Bounded k, Bounded k) else (Unbounded, Unbounded)
  | Pos (ILeq x' k) =>
      if beq_nat x x' then (Unbounded, Bounded k) else (Unbounded, Unbounded)
  | Neg (ILeq x' k) =>
      if beq_nat x x' then (Bounded (k+1), Unbounded) else (Unbounded, Unbounded)
  | _ => (Unbounded, Unbounded)
  end.
Theorem db_from_lit_valid : forall (x : ivar) (l : lit) (theta : asg),
  (eval_lit l theta) -> sat_dbound (db_from_lit x l) (eval_ivar x theta).
Proof.
  intros. unfold sat_dbound; unfold db_from_lit.
  unfold sat_lb, sat_ub.

  destruct l.
  unfold eval_lit in H. unfold eval_vprop in H.
  induction v.

  assert (beq_nat x i = true <-> x = i).
  apply beq_nat_true_iff.
  destruct (beq_nat x i). simpl.
  assert (x = i). apply H0. trivial.
  split. trivial. rewrite H1. exact H.

  simpl. tauto.

  assert (beq_nat x i = true <-> x = i). apply beq_nat_true_iff.
  destruct (beq_nat x i).

  simpl. assert (x = i). apply H0; trivial.
  rewrite H1; rewrite H. eauto with zarith.

  simpl. tauto.

  simpl. tauto.

  unfold eval_lit in H; unfold eval_vprop in H; induction v.

  assert (beq_nat x i = true <-> x = i).
  apply beq_nat_true_iff.
  destruct (beq_nat x i).

  simpl. assert (x = i). apply H0; trivial.
  rewrite H1. split.
  clear H0; omega. trivial.

  simpl. tauto.

  simpl. tauto.
 
  simpl. tauto.
Qed.
  
Fixpoint db_from_negclause (x : ivar) (cl : clause) :=
  match cl with
  | nil => (Unbounded, Unbounded)
  | cons l ls => db_meet (db_from_lit x (neglit l)) (db_from_negclause x ls)
  end.

Theorem db_from_negclause_valid : forall (x : ivar) (cl : clause) (theta : asg),
 ~eval_clause cl theta -> sat_dbound (db_from_negclause x cl) (eval_ivar x theta).
Proof.
  intros.
  induction cl.
  unfold db_from_negclause; unfold sat_dbound; unfold sat_lb; unfold sat_ub; simpl.
  tauto.

  unfold eval_clause in H; fold eval_clause in H.
  assert (~(eval_lit a theta) /\ ~(eval_clause cl theta)).
  apply Decidable.not_or; exact H. destruct H0.
  assert (eval_lit (neglit a) theta).
  apply neglit_not_lit. exact H0.
  unfold db_from_negclause ; fold db_from_negclause.
  assert (sat_dbound (db_from_lit x (neglit a)) (eval_ivar x theta)).
  apply db_from_lit_valid; exact H2.
  assert (sat_dbound (db_from_negclause x cl) (eval_ivar x theta)).
  apply IHcl; exact H1.
  apply db_sat_impl_meet. split. exact H3. exact H4.
Qed.

Theorem notdb_negclause_impl_clause : forall (x : ivar) (cl : clause) (theta : asg),
  ~ sat_dbound (db_from_negclause x cl) (eval_ivar x theta) -> eval_clause cl theta.
Proof.
  intros.
  assert (eval_clause cl theta \/ ~ eval_clause cl theta). apply dec_evalclause.
  destruct H0.
  
  exact H0.
  assert (sat_dbound (db_from_negclause x cl) (eval_ivar x theta)).
  apply db_from_negclause_valid. exact H0.
  tauto.
Qed.

Theorem notsat_ub_impl_notdb : forall (db : dbound) (k : Z),
  ~ sat_ub (snd db) k -> ~ sat_dbound db k.
Proof.
  unfold sat_dbound; destruct db; simpl; intros.
  tauto.
Qed.

Theorem notsat_lb_impl_notdb : forall (db : dbound) (k : Z),
  ~ sat_lb (fst db) k -> ~ sat_dbound db k.
Proof.
  unfold sat_dbound; destruct db; simpl; intros. tauto.
Qed.