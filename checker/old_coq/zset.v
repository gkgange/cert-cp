(* Module for integer sets. *)
Require Import Bool.
Require Import ZArith.
Require MSets.
Require Import prim.

Require Import Orders.
Require Import Relations.
Require OrdersEx.

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
  assert (~ mem s k \/ mem s k). tauto.
  destruct H0. assumption.
  apply memb_iff_mem in H0.
  rewrite H in H0; discriminate.

  assert (memb s k = true <-> mem s k).
    apply memb_iff_mem.
  destruct (memb s k).
    tauto. trivial.
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
  assert (k <> k' \/ k = k'). tauto.
  destruct H0. assumption.
  rewrite H0 in H.
  assert (mem (add s k') k'). apply mem_k_addk.
  tauto.

  assert (~ mem s k' \/ mem s k'). tauto.
  destruct H0. assumption.
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
    intros; assert False. omega. tauto.
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
Definition zset_covers (xs : zset) (lb ub : Z) :=
  if Z_leb lb ub then
    zset_covers_nat xs lb (Zabs_nat (ub - lb + 1))
  else
    true.
Theorem zset_covers_spec : forall (xs : zset) (lb ub : Z),
  zset_covers xs lb ub = true <->
    forall k, lb <= k <= ub -> mem xs k.
Proof.
  unfold zset_covers.
  intros xs lb ub.
  assert (Z_leb lb ub = true <-> lb <= ub).
    apply Z_leb_iff_le.
  destruct Z_leb.
    assert (lb <= ub) as Hle. apply H; trivial. clear H.

    split.
      intros.
      assert (k = (lb + (Z_of_nat (Zabs_nat (k - lb))))).
      rewrite inj_Zabs_nat.
      assert (k - lb >= 0).
        omega.
      rewrite Zabs_eq.
        clear H. omega. omega.
      rewrite zset_covers_nat_iff_covers in H.
      rewrite H1.
      apply H.
      apply Zabs_nat_lt. omega.

      intros. rewrite zset_covers_nat_iff_covers.
      intros. apply H.
      split. omega.
      assert (ub = lb + Z_of_nat (Zabs_nat (ub - lb))).
        rewrite inj_Zabs_nat. rewrite Zabs_eq.
        omega.
        omega.
      rewrite H1. apply Zplus_le_compat.
      omega. 
      apply inj_le.
      apply lt_n_Sm_le.
      rewrite <- Zabs_nat_Zsucc.
      assumption. omega.

  assert (lb <= ub \/ ub < lb).
    clear H; omega.
  destruct H0.
    apply H in H0; discriminate.
  clear H.
  split.
    intros.
      assert False. omega. tauto.
    intros; trivial.
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
  assert (~mem xs k' \/ mem xs k'). tauto.
  destruct H2. assumption.
  induction ZSets.min_elt.
  apply Z.min_glb_lt_iff in H1.
  destruct H1.
  assert (~ k' < a).
    apply H0. trivial. assumption.
  omega.
  
  assert (ZSets.Empty xs).
    apply H; trivial.
  unfold ZSets.Empty in H3.
  unfold mem. apply H3.
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
  intros.
  assert (~mem xs k' \/ mem xs k'). tauto.
  destruct H2. assumption.
  induction ZSets.max_elt.
  apply Z.max_lub_lt_iff in H1.
  destruct H1.
  assert (~ a < k').
    apply H0. trivial. assumption.
  omega.
  
  assert (ZSets.Empty xs).
    apply H; trivial.
  unfold ZSets.Empty in H3.
  unfold mem. apply H3.
Qed.
