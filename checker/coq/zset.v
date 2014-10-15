(* Module for integer sets. *)
Require Import Bool.
Require Import ZArith.
Require Import prim.

Definition zset : Type := list Z.

Definition empty : zset := nil.

Fixpoint mem (s : zset) (k : Z) : Prop :=
  match s with
  | nil => False
  | cons x xs => x = k \/ mem xs k
  end.

Fixpoint memb (s : zset) (k : Z) : bool :=
  match s with
  | nil => false
  | cons x xs => (Z_eqb x k) || memb xs k
  end.

Theorem memb_true_iff_mem : forall (s : zset) (k : Z),
  memb s k = true <-> mem s k.
Proof.
  intros. induction s.
  unfold memb, mem.
  split. intros; discriminate.
  intros; tauto.

  unfold memb, mem; fold memb; fold mem.
  rewrite <- Z_eqb_iff_eq. rewrite <- IHs.
  rewrite orb_true_iff. tauto.
Qed.

Definition add (s : zset) (k : Z) : zset :=
  cons k s.
Theorem mem_mem_add : forall (s : zset) (k : Z) (k' : Z),
  mem s k -> mem (add s k') k.
Proof.
  intros; unfold add, mem. fold mem.
  right. exact H.
Qed.
Theorem mem_k_addk : forall (s : zset) (k : Z),
  mem (add s k) k.
Proof.
  intros; unfold add, mem; fold mem.
  left. trivial.
Qed.
Theorem mem_addk_if : forall (s : zset) (k k' : Z),
  mem (add s k) k' -> k = k' \/ mem s k'.
Proof.
  unfold add, mem; fold mem; intros.
  exact H.
Qed.

Fixpoint rem (s : zset) (k : Z) :=
  match s with
  | nil => nil
  | cons x xs =>
    let tail := rem xs k in
    if Z_eqb x k then tail else cons x tail
  end.
Theorem notmem_k_remk : forall (s : zset) (k : Z),
  ~ mem (rem s k) k.
Proof.
  intros; induction s.

  unfold mem, rem. tauto.

  unfold rem; fold rem.
  assert (Z_eqb a k = true <-> a = k). apply Z_eqb_iff_eq.
  destruct (Z_eqb a k).

  exact IHs.
  unfold mem; fold mem.
  rewrite <- memb_true_iff_mem in IHs.
  rewrite <- memb_true_iff_mem.
  rewrite <- H.
  destruct (memb (rem s k) k).
  tauto.
  tauto.
Qed.
Theorem notmem_notmem_remk : forall (s : zset) (k k' : Z),
  ~ mem s k' -> ~ mem (rem s k) k'.
Proof.
  intros s k k'; induction s.

  unfold mem, rem; tauto.

  unfold rem; fold rem. unfold mem; fold mem.
  assert (Z_eqb a k = true <-> a = k). apply Z_eqb_iff_eq.
  destruct (Z_eqb a k).
  intros. apply IHs.
  rewrite <- memb_true_iff_mem.
  rewrite <- memb_true_iff_mem in H0.
  destruct (memb s k').
  tauto. tauto.

  unfold mem; fold mem.
  rewrite <- memb_true_iff_mem in IHs.
  rewrite <- memb_true_iff_mem in IHs.
  rewrite <- memb_true_iff_mem.
  rewrite <- memb_true_iff_mem.
  tauto.
Qed.

Fixpoint union (xs ys : zset) :=
  match xs with
  | nil => ys
  | cons x xs' => add (union xs' ys) x
  end.
Theorem mem_union_iff : forall (xs ys : zset) (k : Z),
  mem (union xs ys) k <-> mem xs k \/ mem ys k.
Proof.
  induction xs.
    unfold union.
    split.
      intro. right. exact H.
    
      unfold mem; fold mem. tauto.

    unfold union, mem; fold union; fold mem.
    unfold add.
    intros ys k.
    assert (a = k \/ (mem xs k \/ mem ys k) <->
      (a = k \/ mem xs k) \/ mem ys k). tauto.
    rewrite <- H.
    rewrite <- IHxs.
    unfold mem; fold mem. tauto.
Qed.