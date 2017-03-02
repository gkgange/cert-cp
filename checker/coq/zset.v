(* Module for integer sets. *)
Require Import Bool.
Require Import ZArith.
Require Import ZArith.Zwf.
Require Import Recdef.
Require MSets.

Require Import Orders.
Require Import Relations.
Require OrdersEx.

Local Open Scope Z_scope.
Module Z_as_Int := Int.Z_as_Int.
Module Z_as_OT := OrdersEx.Z_as_OT.
Module ZSets := MSetAVL.IntMake(Z_as_Int)(Z_as_OT).

Definition zset : Type := ZSets.t.

Definition empty : zset := ZSets.empty.

Definition mem (s : zset) (k : Z) : Prop := ZSets.In k s.
Definition memb (s : zset) (k : Z) : bool := ZSets.mem k s.
Definition memb_iff_mem : forall (s : zset) (k : Z),
  memb s k = true <-> mem s k.
Proof.
  unfold memb, mem.
  intros. apply ZSets.mem_spec.
Qed.

Definition memb_false_iff_notmem : forall (s : zset) (k : Z),
  memb s k = false <-> ~ mem s k.
Proof.
  intros; split; intros.
  intro.
  apply memb_iff_mem in H0.
  now rewrite H in H0.

  apply Bool.not_true_is_false; intro.
  now rewrite memb_iff_mem in H0.
Qed.

Theorem notmem_empty : forall (k : Z),
  ~ mem empty k.
Proof.
  unfold mem.
  apply ZSets.empty_spec.
Qed.

Definition add (s : zset) (k : Z) : zset := ZSets.add k s.
Theorem mem_mem_add : forall (s : zset) (k : Z) (k' : Z),
  mem s k -> mem (add s k') k.
Proof.
  unfold mem; intros. apply ZSets.add_spec.
  right. assumption.
Qed.
Theorem mem_k_addk : forall (s : zset) (k : Z),
  mem (add s k) k.
Proof.
  intros; unfold add, mem. rewrite ZSets.add_spec.
  left. trivial.
Qed.
Theorem mem_addk_if : forall (s : zset) (k k' : Z),
  mem (add s k) k' -> k = k' \/ mem s k'.
Proof.
  unfold add, mem;  intros.
  apply ZSets.add_spec in H.
  destruct H. eauto. eauto.
Qed.
Theorem notmem_add_if : forall (s : zset) (k k' : Z),
  ~ mem (add s k) k' -> k <> k' /\ ~ mem s k'.
Proof.
  intros; split.
  intro.
  rewrite H0 in H.
  assert (mem (add s k') k'). apply mem_k_addk.
  tauto.

  intro.
  now apply mem_mem_add with (k' := k) in H0.
Qed.
  
Definition union (xs ys : zset) := ZSets.union xs ys.
Theorem mem_union_iff : forall (xs ys : zset) (k : Z),
  mem (union xs ys) k <-> mem xs k \/ mem ys k.
Proof.
  unfold mem, union; apply ZSets.union_spec.
Qed.
Fixpoint zset_covers_nat (xs : zset) (k : Z) (sz : nat) :=
  match sz with
  | O => true
  | S sz' => memb xs (k + (Z_of_nat sz')) && zset_covers_nat xs k sz'
  end.
Theorem zset_covers_nat_iff_covers :
  forall (xs : zset) (k : Z) (sz : nat),
    zset_covers_nat xs k sz = true <->
      forall (sz' : nat), lt sz' sz -> mem xs (k + (Z_of_nat sz')).
Proof.
  intros xs k sz; induction sz.
  unfold zset_covers_nat.
  split.
    intros; absurd (le sz' 0); omega.
    intros; trivial.

  unfold zset_covers_nat; fold zset_covers_nat; rewrite andb_true_iff.
  split.
    intros; destruct H as [Hm Hc].
    rewrite memb_iff_mem in Hm.
    assert (lt sz' sz \/ sz' = sz) as Hle.
      clear Hm Hc IHsz; omega.
    destruct Hle as [Hle | Hle].
    apply IHsz.
      assumption. assumption.
      rewrite Hle; assumption.

  intros; rewrite memb_iff_mem.
  split.
    apply H; clear IHsz; omega.
    apply IHsz.
    intros; apply H. clear IHsz; omega.
Qed.

Function zset_covers_Z (xs : zset) (k : Z) (sz : Z) { wf (Zwf 0) sz} :=
  if Z.leb sz 0 then
    true
  else
    let sz' := Z.pred sz in
    memb xs (k + sz') && zset_covers_Z xs k sz'.
  intros _ _ sz Hsz.
  apply Z.leb_nle, Z.nle_gt in Hsz; unfold Zwf; omega.
  apply Zwf_well_founded.
Defined.

Lemma z_ind :
  forall x0 P x,
    Z.lt x0 x ->
    ((P x /\ (forall k, Z.le x0 k /\ Z.le k (Z.pred x) -> P k)) <-> (forall k, Z.le x0 k /\ Z.le k x -> P k)).
Proof.
  intros x0 P x Hlt.
  split; intros.
  + destruct H as [Hx Hys].
    assert (Hd := Z_le_dec k (Z.pred x)); destruct Hd.
    specialize (Hys k); intuition.
    apply Z.nle_gt in n.
    assert (x = k). omega.
    rewrite <- H; exact Hx.
  + split.
    apply (H x); omega.
    intro k; specialize (H k).
    intro Hp; apply H; omega.
Qed.

Definition covers_range xs k sz := forall sz', Z.le 0 sz' -> Z.lt sz' sz -> mem xs (k + sz').
Lemma covers_range_1 : forall xs k sz, Z.lt 0 sz -> (covers_range xs k sz <-> mem xs (k + (Z.pred sz)) /\ covers_range xs k (Z.pred sz)).
Proof.
  intros xs k sz Hlt.
  split.
  + intro Hc.
    unfold covers_range in Hc; split.
    apply (Hc (Z.pred sz)); omega.
    unfold covers_range.
    intros; apply Hc; try omega.
  + intro H; destruct H as [Hp Hks].
    unfold covers_range; intros sz' Hlt' Hsz'.
    assert (Hd := Z_lt_dec sz' (Z.pred sz)); destruct Hd as [Hd | Hd].
    apply Hks; omega.
    assert (sz' = Z.pred sz). omega.
    rewrite H; apply Hp.
Qed.

Require ZArith.Wf_Z.
Lemma zset_covers_Z_1 :
  forall xs k sz, zset_covers_Z xs k sz = true <-> covers_range xs k sz.
Proof.
  intros xs k.
  intro sz.
  destruct (Z_le_dec 0 sz) as [Hge | Hlt].
  + generalize sz Hge.
    apply natlike_ind.
    unfold covers_range; rewrite zset_covers_Z_equation.
    simpl; split; intros; try omega.
    trivial.

    intros.
    rewrite zset_covers_Z_equation, covers_range_1.
    assert (x = Z.pred (Z.succ x)). omega.
    rewrite <- H1.
    assert (Z.leb (Z.succ x) 0 = false).
      apply Z.leb_gt.
      omega.
      rewrite H2.
      rewrite Bool.andb_true_iff.
      rewrite memb_iff_mem; rewrite H0.
      intuition.
      omega.
  + unfold covers_range; rewrite zset_covers_Z_equation.
    rewrite Z.nle_gt in Hlt.
    assert (Z.leb sz 0 = true).
      apply Z.leb_le; omega.
      rewrite H.
      split; intuition; omega.
Qed.

Definition zset_covers (xs : zset) (lb ub : Z) :=
  if Z.leb lb ub then
    zset_covers_Z xs lb (ub - lb + 1)
  else
    true.
Theorem zset_covers_spec : forall (xs : zset) (lb ub : Z),
  zset_covers xs lb ub = true <->
    forall k, lb <= k <= ub -> mem xs k.
Proof.
  unfold zset_covers.
  intros xs lb ub.
  assert (Z.leb lb ub = true <-> lb <= ub).
    symmetry; apply Zle_is_le_bool.
  destruct Z.leb.
    assert (lb <= ub) as Hle. apply H; trivial. clear H.

    split.
      intros.
      (* assert (k = (lb + (Z_of_nat (Zabs_nat (k - lb))))). *)
      assert (k = (lb + (k - lb))). omega.
      (* rewrite inj_Zabs_nat. *)
      assert (k - lb >= 0).
        omega.
      (*
      rewrite Zabs_eq.
        clear H. omega. omega.
       *)
      (* rewrite zset_covers_nat_iff_covers in H. *)
      rewrite zset_covers_Z_1 in H.
      rewrite H1.
      apply H.
      omega.
      omega.

      intros. rewrite zset_covers_Z_1.
      unfold covers_range; intros; apply H.
      omega.

      assert (Z.lt ub lb).
      apply Z.lt_nge; intro; intuition.
      split; intros; try (intuition || omega).

      assert (false = true).
        apply H5; omega.
        discriminate.
Qed.

Definition zset_min_lb (xs : zset) (k : Z) :=
  match ZSets.min_elt xs with
  | None => k
  | Some k' => Zmin k k'
  end.
Theorem zset_min_lb_le : forall (xs : zset) (k : Z),
  zset_min_lb xs k <= k.
Proof.
  unfold zset_min_lb.
  intros xs k.
  destruct ZSets.min_elt.
    apply Zle_min_l.
    omega.
Qed.

Theorem lt_min_notin_zset : forall (xs :zset) (k k' : Z),
  k' < zset_min_lb xs k -> ~ mem xs k'.
Proof.
  unfold zset_min_lb; intros xs k k'.
  assert (ZSets.min_elt xs = None -> ZSets.Empty xs).
    apply ZSets.min_elt_spec3.
  assert (forall m, ZSets.min_elt xs = Some m -> (forall n, mem xs n -> ~ n < m)).
    unfold mem.
    intros.
    apply ZSets.min_elt_spec2 with (y := n) in H0.
    assumption. assumption.
  intros.
  intro.
  induction ZSets.min_elt.
  apply Z.min_glb_lt_iff in H1.
  destruct H1.
  now apply H0 with (m := a) in H2.
  
  assert (ZSets.Empty xs).
    now apply H.
  unfold ZSets.Empty in H3.
  unfold mem in H2. now apply H3 in H2.
Qed.

Definition zset_max_ub (xs : zset) (k : Z) :=
  match ZSets.max_elt xs with
  | None => k
  | Some k' => Zmax k k'
  end.
Theorem zset_max_ub_lb : forall (xs : zset) (k : Z),
  k <= zset_max_ub xs k.
Proof.
  unfold zset_max_ub.
  intros xs k.
  destruct ZSets.max_elt.
    apply Zle_max_l.
    omega.
Qed.

Theorem max_lt_notin_zset : forall (xs :zset) (k k' : Z),
  zset_max_ub xs k < k' -> ~ mem xs k'.
Proof.
  unfold zset_max_ub; intros xs k k'.
  assert (ZSets.max_elt xs = None -> ZSets.Empty xs).
    apply ZSets.max_elt_spec3.
  assert (forall m, ZSets.max_elt xs = Some m -> (forall n, mem xs n -> ~ m < n)).
    unfold mem.
    intros.
    apply ZSets.max_elt_spec2 with (y := n) in H0.
    assumption. assumption.
  intros; intro.
  induction ZSets.max_elt.
  apply Z.max_lub_lt_iff in H1.
  destruct H1.
  assert (~ a < k').
    apply H0. trivial. assumption.
  omega.
  
  assert (ZSets.Empty xs).
    apply H; trivial.
  unfold ZSets.Empty in H3.
  unfold mem. now apply H3 in H2.
Qed.

Lemma mem_dec : forall s z, Decidable.decidable (mem s z).
Proof.
  unfold Decidable.decidable.
  intros; rewrite <- memb_iff_mem.
  remember (memb s z) as b; destruct b; [tauto | right; apply diff_false_true].
Qed.

Ltac zset_simpl :=
  repeat (match goal with
    | [ |- context[memb ?S ?X = true] ] => rewrite memb_iff_mem
    | [ |- context[memb ?S ?X = false] ] => rewrite memb_false_iff_notmem
    | [ H : context[memb ?S ?X = true] |- _ ] => rewrite memb_iff_mem in H
    | [ H : context[memb ?S ?X = false] |- _ ] => rewrite memb_false_iff_notmem in H
    | [ H : mem empty _ |- _ ] => apply notmem_empty in H; contradiction
    | [ H : mem ?S1 ?X |- mem (union ?S1 _) ?X ] =>
      apply mem_union_iff ; left ; exact H
    | [ H : mem ?S2 ?X |- mem (union _ ?S2) ?X ] =>
      apply mem_union_iff ; right; exact H
    end).
