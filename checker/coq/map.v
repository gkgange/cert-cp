(* Module for dealing with maps. *)
Require Import ZArith.
Require ZArith.ZArith_dec.
Require Import OrderedType.
Require FSets.
Require FSets.FMapAVL.
Require FMaps.


Module Z_as_Int.
  Open Scope Z_scope.
  Definition t := Z.
  Definition int := t.
  Definition _0 := 0.
  Definition _1 := 1.
  Definition _2 := 2.
  Definition _3 := 3.
  Definition plus := Zplus.
  Definition opp := Zopp.
  Definition minus := Zminus.
  Definition mult := Zmult.
  Definition max := Zmax.
  Definition gt_le_dec := Z_gt_le_dec.
  Definition ge_lt_dec := Z_ge_lt_dec.
  Definition eq_dec := Z_eq_dec.
  Definition i2z : int -> Z := fun n => n.
  Lemma i2z_eq : forall n p, i2z n=i2z p -> n = p.
  Proof. intros; tauto. Qed.
  Lemma i2z_0 : i2z _0 = 0.
  Proof. intros; tauto. Qed.
  Lemma i2z_1 : i2z _1 = 1.
  Proof. intros; tauto. Qed.
  Lemma i2z_2 : i2z _2 = 2.
  Proof. intros; tauto. Qed.
  Lemma i2z_3 : i2z _3 = 3.
  Proof. intros; tauto. Qed.
  Lemma i2z_plus : forall n p, i2z (n + p) = i2z n + i2z p.
  Proof. intros; tauto. Qed.
  Lemma i2z_opp : forall n, i2z (- n) = - i2z n.
  Proof. intros; tauto. Qed.
  Lemma i2z_minus : forall n p, i2z (n - p) = i2z n - i2z p.
  Proof. intros; tauto. Qed.
  Lemma i2z_mult : forall n p, i2z (n * p) = i2z n * i2z p.
  Proof. intros; tauto. Qed.
  Lemma i2z_max : forall n p, i2z (max n p) = Zmax (i2z n) (i2z p).
  Proof. intros; tauto. Qed.
End Z_as_Int.

Module Z_as_map_OT.
  Local Open Scope Z_scope.
  Definition t := Z.
  Definition eq := @eq Z.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.

  Program Instance eq_equiv : Equivalence eq.

  Definition lt (x y:Z) := (x<y).

  Lemma lt_trans : forall x y z, x<y -> y<z -> x<z.
  Proof. intros; omega. Qed.

  Lemma lt_not_eq : forall x y, x<y -> ~ x=y.
  Proof. intros; omega. Qed.

  Definition compare x y : Compare lt eq x y.
  Proof.
    case_eq (Zcompare x y); intro.
      apply EQ; now apply Zcompare_Eq_eq.
      apply LT; assumption.
      apply GT; now apply Zgt_lt.
  Qed.
  Definition eq_dec := Z_eq_dec.

  Program Instance lt_strorder : StrictOrder lt.
  Program Definition lt_compat : Proper (eq ==> eq ==> iff) lt := _.
  Lemma compare_spec : forall n m : Z, CompSpec eq lt n m (n ?= m).
  Proof. apply Zcompare_spec. Qed.
End Z_as_map_OT.

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
