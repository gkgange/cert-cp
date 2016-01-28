(* Module for dealing with maps. *)
Require Import ZArith.
Require ZArith.ZArith_dec.
Require Import OrderedType.
Require FSets.
Require FSets.FMapAVL.
Require FMaps.
Require OrdersEx.
Require OrdersAlt.


Module Z_as_Int := Int.Z_as_Int.
Module Z_as_map_OT := OrdersAlt.Backport_OT(OrdersEx.Z_as_OT).
Module ZMaps := FSets.FMapAVL.IntMake(Z_as_Int)(Z_as_map_OT).
Module ZMapProperties := FMapFacts.WProperties(ZMaps).

Definition zmap (T : Type) : Type := ZMaps.t T.

Lemma find_mapsto_iff : forall (A : Type) (m :ZMaps.t A) x e, ZMaps.MapsTo x e m <-> ZMaps.find x m = Some e.
Proof.
  split; [apply ZMaps.find_1|apply ZMaps.find_2].
Qed.

(* Grabbed from a newer version of coq. *)
Lemma eq_option_alt : forall (elt : Type) (o o' : option elt),
  o = o' <-> (forall e, o=Some e <-> o' = Some e).
Proof.
  split; intros.
  subst; split; auto.
  destruct o; destruct o'; try rewrite H; auto.
  symmetry; rewrite <- H; auto.
Qed.

Lemma not_find_in_iff : forall (A : Type) (m : ZMaps.t A) (x : ZMaps.key), ~ ZMaps.In x m <-> ZMaps.find x m = None.
Proof.
  split; intros.
  rewrite eq_option_alt. intro e. rewrite <- find_mapsto_iff.
  split; try discriminate. intro H'; elim H; exists e; auto.
  intros (e,He).
  assert (ZMaps.MapsTo x e m <-> ZMaps.find x m = Some e) as H'.
    apply find_mapsto_iff.
  unfold ZMaps.MapsTo in H'.
  rewrite H in H'.
  apply H' in He.
  discriminate.
Qed.

Theorem find_empty_none : forall (A : Type) (x : ZMaps.key), ZMaps.find x (ZMaps.empty A) = None.
Proof.
  intros.
  apply not_find_in_iff.
  intros (e,Hc).
  assert (ZMaps.Empty (ZMaps.empty A)).
    apply ZMaps.empty_1.
  unfold ZMaps.Empty, ZMaps.Raw.Proofs.Empty in H.
  assert (~ ZMaps.Raw.MapsTo x e (ZMaps.this (ZMaps.empty A))).
    apply H.
  tauto.
Qed.

Theorem not_in_notmap : forall (A : Type) (xs : ZMaps.t A) (x  : ZMaps.key),
  ~ ZMaps.In x xs <-> forall e, ~ ZMaps.MapsTo x e xs.
  split; intros.
    intro.
      apply not_find_in_iff in H.
      apply ZMaps.find_1 in H0. rewrite H in H0. discriminate.
    apply not_find_in_iff.
    apply eq_option_alt.
    split; intros.
      apply ZMaps.find_2 in H0.
      now apply H in H0.

      discriminate.
Qed.

Theorem find_add_none : forall (A : Type) (xs : ZMaps.t A) (x a : ZMaps.key) (e : A),
  ZMaps.find a (ZMaps.add x e xs) = None <-> a <> x /\ ZMaps.find a xs = None.
  split; intros.
    split.
      apply not_find_in_iff in H.
      rewrite not_in_notmap in H.
      intro.
        assert (ZMaps.MapsTo a e (ZMaps.add x e xs)).
          rewrite H0.  now apply ZMaps.add_1.
        now apply H in H1.

        apply not_find_in_iff.
        apply not_find_in_iff in H.
        rewrite not_in_notmap in H.
        apply not_in_notmap; intros.
        assert ({x = a} + {x <> a}). apply ZArith.ZArith_dec.Z_eq_dec.
        destruct H0 as [H0 | H0]; intros; intro.
          assert (ZMaps.MapsTo a e (ZMaps.add x e xs)).
            rewrite H0; now apply ZMaps.add_1. now apply H in H2.
          assert (ZMaps.MapsTo a e0 (ZMaps.add x e xs)).
            apply ZMaps.add_2. assumption. assumption.
            now apply H in H2.
    destruct H as [Hne Hnf].
    apply eq_option_alt; split; intros.
      apply not_find_in_iff in Hnf; rewrite not_in_notmap in Hnf.
      assert (ZMaps.MapsTo a e0 xs).
        apply ZMaps.add_3 with (x := x) (e' := e).
          congruence.
          now apply ZMaps.find_2.
          now apply Hnf in H0.
        discriminate.
Qed.

Definition asg_map := ZMaps.t Z.

Fixpoint asg_map_of_alist (ls : list (Z * Z)) :=
  match ls with
  | nil => ZMaps.empty Z
  | cons (x, k) ls' => ZMaps.add x k (asg_map_of_alist ls')
  end.
