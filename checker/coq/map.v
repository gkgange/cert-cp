(* Module for dealing with maps. *)
Require Import ZArith.
Require Import OrderedType.
Require FSets.
Require FSets.FMapAVL.

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

Definition zmap (T : Type) : Type := ZMaps.t T.
