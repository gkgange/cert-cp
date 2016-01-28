(* Lemmas on ranges *)
Require Import ZArith.
Require Import assign.
Require Import range.
Require Import Psatz.

Local Open Scope Z_scope.

Theorem satb_ub_iff_ub : forall (b : bound) (k : Z),
  satb_ub b k = true <-> sat_ub b k.
Proof.
  unfold satb_ub, sat_ub; intros; destruct b; tsimpl.
Qed.

Theorem satb_dbound_iff_db : forall (db : dbound) (k : Z),
  satb_dbound db k = true <-> sat_dbound db k.
Proof.
  unfold_satdb; unfold satb_dbound; intros; destruct db; destruct b, b0; split; simpl in *; tsimpl.
Qed.

Theorem decidable_sat_db : forall (db : dbound) (k : Z),
  sat_dbound db k \/ ~ sat_dbound db k.
Proof.
  unfold sat_dbound, sat_lb, sat_ub; intros;
  destruct db; destruct b, b0; simpl; Psatz.lia.
Qed.

Theorem Zle_satub_trans : forall (b : bound) (k k' : Z),
  Zle k k' -> sat_ub b k' -> sat_ub b k.
Proof.
  unfold_satdb; intros; destruct b; tsimpl.
Qed.
  
Theorem Zle_notub_trans : forall (b : bound) (k k' : Z),
  Zle k k' -> ~sat_ub b k -> ~sat_ub b k'.
Proof.
  unfold_satdb; intros; destruct b; tsimpl.
Qed.

Theorem Zle_notlb_trans : forall (b : bound) (k k' : Z),
  Zle k k' -> ~sat_lb b k' -> ~sat_lb b k.
Proof.
  unfold_satdb; intros; destruct b; tsimpl.
Qed.

Theorem satb_ub_false_iff_notub : forall (b : bound) (k : Z),
  satb_ub b k = false <-> ~ sat_ub b k.
Proof.
  intros; unfold satb_ub; unfold_satdb; destruct b; split; tsimpl.
Qed.

Theorem satb_lb_false_iff_notlb : forall (b : bound) (k : Z),
  satb_lb b k = false <-> ~ sat_lb b k.
Proof.
  intros.
  unfold satb_lb, sat_lb; destruct b; tsimpl.
Qed.

Theorem satb_db_false_iff_notdb : forall (db : dbound) (k : Z),
  satb_dbound db k = false <-> ~ sat_dbound db k.
Proof.
  unfold_satdb; unfold satb_dbound; unfold satb_lb, satb_ub; intros; destruct db; destruct b, b0; simpl in *; tsimpl.
  destruct H; tsimpl.  
Qed.

Theorem unsatb_db_true_iff : forall (db : dbound),
  unsatb_db db = true <-> unsat_db db.
Proof.
  intro; destruct db; simpl.
  unfold unsat_db; unfold_satdb; unfold unsatb_db; intros. destruct b, b0; simpl; tsimpl;
   try assert (H' := H 0); try assert (H'' := H z); tsimpl.
Qed.

Theorem unsat_bounded_iff : forall (k k' : Z),
  unsat_db (Bounded k, Bounded k') <-> k' < k. 
Proof.
  intros; unfold unsat_db; unfold_satdb; tsimpl.
  assert (H' := H k); tsimpl.
Qed.

Theorem bound_le_valid : forall (x y : bound),
  bound_le x y ->
    forall (v : ivar) (theta : valuation),
      eval_lb v y theta -> eval_lb v x theta.
Proof.
  unfold eval_lb, bound_le; unfold_satdb; intros; destruct x, y; tsimpl.
Qed.

Theorem bound_le_iff : forall (x y : bound),
  bound_le x y <-> bound_leb x y = true.
Proof.
  unfold bound_le, bound_leb; intros; destruct x, y; tsimpl.
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

Theorem bmax_ub_l : forall (x y : bound),
  bound_le x (bound_max x y).
Proof.
  intros. unfold bound_max; destruct x, y; simpl; tsimpl.
Qed.

Theorem bmax_valid : forall (x : bound) (y : bound) (k : Z),
  sat_lb x k /\ sat_lb y k -> sat_lb (bound_max x y) k.
Proof.
  unfold_satdb; destruct x, y; simpl; tsimpl.
Qed.
Theorem bmax_b : forall (x : bound) (y : bound) (k : Z),
  sat_lb (bound_max x y) k -> sat_lb x k /\ sat_lb y k.
Proof.
  unfold_satdb; destruct x, y; simpl; tsimpl.
Qed.
  
Theorem bmin_valid : forall (x : bound) (y : bound) (k : Z),
  sat_ub x k /\ sat_ub y k -> sat_ub (bound_min x y) k.
Proof.
  unfold_satdb; destruct x, y; simpl; tsimpl.
Qed.

Theorem bmin_b : forall (x : bound) (y : bound) (k : Z),
  sat_ub (bound_min x y) k -> sat_ub x k /\ sat_ub y k.
Proof.
  unfold_satdb; destruct x, y; simpl; tsimpl.
Qed.

Theorem lb_impl_addlb : forall (k k' : Z) (bk bk' : bound),
  sat_lb bk k /\ sat_lb bk' k' -> sat_lb (bound_add bk bk') (k + k').
Proof.
  unfold_satdb; destruct bk, bk'; simpl; tsimpl.
Qed.

Theorem db_impl_adddb : forall (k k' : Z) (bk bk' : dbound),
  sat_dbound bk k /\ sat_dbound bk' k' -> sat_dbound (db_add bk bk') (k+k').
Proof.
  unfold sat_dbound, db_add; unfold sat_lb, sat_ub, bound_add.
  intros k k' bk bk'; destruct bk, bk'; destruct b, b0, b1, b2; simpl in *; tsimpl.
Qed.

Theorem db_sat_impl_meet : forall (dx dy : dbound) (k : Z),
  sat_dbound dx k /\ sat_dbound dy k -> sat_dbound (db_meet dx dy) k.
Proof.
  unfold sat_dbound, db_add; unfold sat_lb, sat_ub, bound_add.
  intros dx dy k; destruct dx, dy; destruct b, b0, b1, b2; simpl in *; tsimpl.
Qed.

Theorem db_satmeet : forall (dx dy : dbound) (k : Z),
  sat_dbound (db_meet dx dy) k -> sat_dbound dx k /\ sat_dbound dy k.
Proof.
  unfold_satdb; intros dx dy k; destruct dx, dy; destruct b, b0, b1, b2; tsimpl.
Qed.

Lemma db_join_l : forall x y k, sat_dbound x k -> sat_dbound (db_join x y) k.
Proof.
  unfold_satdb; unfold db_join; intros; destruct x, y; destruct b, b0, b1, b2; simpl in *; tsimpl;
    apply unsatb_db_true_iff in H2; apply unsat_bounded_iff in H2; tsimpl.
Qed.
 
Lemma db_join_r : forall y x k, sat_dbound x k -> sat_dbound (db_join y x) k.
Proof.
  unfold_satdb; unfold db_join; destruct x, y; destruct b, b0, b1, b2; tsimpl;
    try (rewrite unsatb_db_true_iff in *; rewrite unsat_bounded_iff in *); tsimpl.
Qed.

Lemma db_join_comm : forall x y k, sat_dbound (db_join x y) k <-> sat_dbound (db_join y x) k.
Proof.
  intros x y k.
  unfold db_join; unfold_satdb.
  destruct x, y; destruct b, b0, b1, b2; tsimpl;
    try (rewrite unsatb_db_true_iff in *; rewrite unsat_bounded_iff in *); tsimpl.
Qed.
  
Lemma db_join_if : forall x y k, sat_dbound x k \/ sat_dbound y k -> sat_dbound (db_join x y) k.
Proof.
  intros; destruct H; [now apply db_join_l | now apply db_join_r].
Qed.
  
Theorem bound_max_assoc : forall (x y z : bound),
  bound_max (bound_max x y) z = bound_max x (bound_max y z).
Proof.
  intros; unfold bound_max; destruct x, y, z; try tauto; try apply f_equal.
  symmetry; apply Zmax_assoc.
Qed.

Theorem bound_min_assoc : forall (x y z : bound),
  bound_min (bound_min x y) z = bound_min x (bound_min y z).
Proof.
  intros; unfold bound_min, bound_may2; destruct x, y, z; try tauto; try apply f_equal.
  symmetry; apply Zmin_assoc.
Qed.
  
Theorem db_meet_assoc : forall (x y z : dbound),
  db_meet (db_meet x y) z = db_meet x (db_meet y z).
Proof.
  intros.
  unfold db_meet; destruct x, y, z; simpl.
  rewrite bound_max_assoc, bound_min_assoc. congruence.
Qed.

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


Theorem mul_pos_dbound_valid : forall (c : Z) (k : Z) (db : dbound),
  c > 0 -> sat_dbound db k -> sat_dbound (mul_pos_dbound c db) (c*k).
Proof.
  unfold sat_dbound, mul_pos_dbound; destruct db. simpl. intros.
  destruct H0 as [Hl Hu].
  split.
  apply mul_pos_bound_lb_valid. exact H. exact Hl.
  apply mul_pos_bound_ub_valid. exact H. exact Hu.
Qed.


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

Theorem db_containedb_iff_contained :
  forall (db : dbound) (lb ub : Z),
    db_containedb db lb ub = true <-> db_contained db lb ub.
Proof.
  unfold db_containedb, db_contained; destruct db; simpl; intros.
  destruct b, b0; tsimpl.
Qed.

Theorem db_contained_impl_inbounds :
  forall (db : dbound) (lb ub : Z),
    db_contained db lb ub -> forall (k : Z),
      sat_dbound db k -> Zle lb k /\ Zle k ub.
Proof.
  unfold sat_dbound, db_contained; destruct db; simpl.
  destruct b, b0; tsimpl.
Qed.

Ltac db_simpl :=
  repeat
    (match goal with
      | [ H : context[satb_dbound _ _ = true] |- _ ] => rewrite satb_dbound_iff_db in H
      | [ H : context[satb_dbound _ _ = false] |- _ ] => rewrite satb_db_false_iff_notdb in H
      | [ |- context[satb_dbound _ _ = true] ] => rewrite satb_dbound_iff_db
      | [ |- context[satb_dbound _ _ = false] ] => rewrite satb_db_false_iff_notdb
      | [ H : sat_dbound (db_meet ?X ?Y) ?K |- _ ] => apply db_satmeet in H
      | [ H : sat_dbound ?X ?K |- sat_dbound (db_join ?X ?Y) ?K ] =>
        apply db_join_l with (y := Y); exact H
      | [ H : sat_dbound ?Y ?K |- sat_dbound (db_join ?X ?Y) ?K ] =>
        apply db_join_r with (x := X); exact H
      | [ H1 : sat_dbound ?X ?K , H2 : sat_dbound ?Y ?K |- sat_dbound (db_meet ?X ?Y) ?K ] =>
      apply db_sat_impl_meet ; split ; [exact H1 | exact H2]
      | [ |- sat_dbound (Unbounded, Unbounded) _ ] => unfold_satdb; tsimpl
     end
    ).