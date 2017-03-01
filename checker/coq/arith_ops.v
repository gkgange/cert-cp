(* Operations on domains/intervals. *)
Require Import ZArith.
Require Import Psatz.
Require Import range.
Require Import range_properties.
Require Import domain.
Require Import assign.

Ltac unfold_satdb := unfold sat_dbound, sat_lb, sat_ub in *; simpl.

Fixpoint db_sat_list ys k :=
  match ys with
  | nil => False
  | cons y ys' => (sat_dbound y k) \/ db_sat_list ys' k
  end.

Fixpoint db_disjoint_list (x : dbound) (ys : list dbound) :=
  match ys with
  | nil => true
  | cons y ys' => andb (negb (unsatb_db (db_meet x y))) (db_disjoint_list x ys')
  end.

Definition db_split_at (x : dbound) (k : Z) :=
  (db_meet x (Unbounded, Bounded k), db_meet x (Bounded (Zsucc k), Unbounded)).

Definition db_split_m x := db_split_at x (-1).
Definition db_split_0 x := db_split_at x 0.
(*
Definition db_split (x : dbound) :=
  (db_meet x (Unbounded, Bounded (-1)), db_meet x (Bounded 0, Unbounded)).

Definition db_split_pos (x : dbound) :=
  (db_meet x (Unbounded, Bounded 0), db_meet x (Bounded 1, Unbounded)).
*)

Definition bound_neg (b : bound) :=
  match b with
  | Unbounded => Unbounded
  | Bounded x => Bounded (-x)
  end.
Definition db_neg (x : dbound) := (bound_neg (snd x), bound_neg (fst x)).
Lemma db_neg_valid : forall x k, sat_dbound x k <-> sat_dbound (db_neg x) (-k).
Proof.
  intros; unfold_satdb; unfold db_neg; destruct x; destruct b, b0; simpl in *; split; intros; try tauto;
    split ; try tauto; try omega.
Qed.

Lemma db_neg_valid_2 : forall x k, sat_dbound (db_neg x) k <-> sat_dbound x (-k).
Proof.
  intros; unfold_satdb; unfold db_neg; destruct x; destruct b, b0; simpl; try lia.
Qed.
  
Theorem db_split_iff : forall (x : dbound) (c k : Z),
  sat_dbound x k <-> sat_dbound (fst (db_split_at x c)) k \/ sat_dbound (snd (db_split_at x c)) k.
Proof.
  unfold db_split_at; simpl; intros.
  assert (k <= c \/ (Zsucc c) <= k) as Hk. omega.
  split; intros.
  destruct Hk ; [left | right]; apply db_sat_impl_meet;
    split; try assumption; unfold_satdb; split; try trivial; try omega.
  destruct Hk ; destruct H ; apply db_satmeet in H; destruct H as [Hx Hb]; assumption. 
Qed.

Definition mul_bound u v :=
  match u with
  | Bounded bu =>
    match v with
    | Bounded bv => Bounded (bu*bv)
    | _ => Unbounded
    end
  | _ => Unbounded
  end.
      
Definition db_is_positive x := forall k, sat_dbound x k -> 0 < k.
Definition db_is_nonneg x := forall k, sat_dbound x k -> 0 <= k.
Lemma db_pos_nonneg : forall x, db_is_positive x -> db_is_nonneg x.
Proof. unfold db_is_positive, db_is_nonneg; intros. apply H in H0; lia. Qed.

Lemma db_meet_pos_l : forall x y,
  db_is_positive x -> db_is_positive (db_meet x y).
Proof. unfold db_is_positive; intros; apply db_satmeet in H0; destruct H0 as [Hl Hr]; now apply (H k) in Hl. Qed.

Lemma db_meet_pos_r : forall x y,
  db_is_positive y -> db_is_positive (db_meet x y).
Proof. unfold db_is_positive; intros; apply db_satmeet in H0; destruct H0 as [Hl Hr]; now apply (H k) in Hr. Qed.

(*
Lemma db_meet_pos : forall x y,
  db_is_positive (db_meet x y) -> db_is_positive x \/ db_is_positive y.                      
Proof.
  unfold db_is_positive; intros.
  *)

Definition db_is_positive_1 (x : dbound) :=
  match x with
  | (Unbounded, _) => False
  | (Bounded k, Unbounded) => 0 < k
  | (Bounded k, Bounded k') => k' < k \/ 0 < k
  end.
Lemma db_positive_iff : forall x, db_is_positive x <-> db_is_positive_1 x.
Proof.
  intros.
  unfold db_is_positive, db_is_positive_1; split; intros; destruct x; destruct b, b0; simpl in *;
    try tauto.
  assert (sat_dbound (Unbounded, Unbounded) (-1)). unfold_satdb; tauto.
  apply H in H0. omega.
  assert (0 <= z \/ z < 0). omega.
  destruct H0.
    assert (sat_dbound (Unbounded, Bounded z) (-1)). unfold_satdb; split; [tauto | omega].
    apply H in H1; omega.

    assert (sat_dbound (Unbounded, Bounded z) z). unfold_satdb; split; [tauto | omega].
    apply H in H1; omega.

  apply H with (k := z); unfold_satdb; split; [omega | tauto].
  assert (z0 < z \/ z <= z0) as Hz. omega.
  destruct Hz; [left; assumption | right].
  apply H with (k := z); unfold_satdb; split; simpl in *.
  omega. assumption.
  unfold_satdb; simpl in *; omega.
  unfold_satdb; simpl in *; omega.
Qed.

Lemma db_positive_lb_pos : forall x k,
  db_is_positive x -> ((fst x) = Bounded k) ->
    (unsat_db x \/ (0 < k)).
Proof.
  unfold db_is_positive, unsat_db; unfold_satdb;
    destruct x; destruct b, b0;
    simpl; intros; try congruence; inversion H0.
    right; apply H; now rewrite H2.
  assert (z0 < z \/ z <= z0) as Hz. omega.
  destruct Hz; [left; intros; omega | right; apply H; rewrite H2; omega].
Qed. 
Lemma db_nonneg_lb_nonneg : forall x k,
  db_is_nonneg x -> ((fst x) = Bounded k) -> (unsat_db x \/ (0 <= k)).                              
Proof.
  unfold db_is_nonneg; intros x k; destruct x; destruct b, b0; simpl; unfold unsat_db; unfold_satdb; intros;
    try congruence; assert (Hk := H k); try inversion H0;
    try (right; lia).
  assert (k <= z0 \/ z0 < k) as Hd. lia.
  destruct Hd; [right | left; intro]; lia.
Qed.

Lemma db_nonneg_bounded : forall x, db_is_nonneg x -> (fst x) <> Unbounded.
Proof.
  intro x.
  unfold db_is_nonneg; unfold_satdb; destruct x; destruct b, b0; simpl; intros; try congruence.
    assert (Hf := H (-1)); lia.
    assert (Hf := H (Z.min z (-1))). lia.
Qed.

Lemma db_split_left : forall x k k', sat_dbound (fst (db_split_at x k)) k' -> k' <= k.
Proof.
  intros x k k'; unfold db_split_at; unfold_satdb; destruct x; simpl.
  destruct b, b0; simpl; try lia.
Qed.

Lemma db_split_right : forall x k k', sat_dbound (snd (db_split_at x k)) k' -> k < k'.
Proof.
  intros x k k'; unfold db_split_at; unfold_satdb; destruct x; destruct b, b0; simpl; try lia.
Qed.

Lemma db_split_pos : forall x, db_is_positive (snd (db_split_at x 0)).
Proof.
  intro x; unfold db_is_positive; intro k; apply db_split_right.
Qed.

Lemma db_split_neg : forall x, db_is_positive (db_neg (fst (db_split_at x (-1)))).
Proof.
  intro x; unfold db_is_positive; intro k; rewrite db_neg_valid_2.
  intro Hn; apply db_split_left in Hn; lia.
Qed.

Lemma db_split_nonneg : forall x, db_is_nonneg (snd (db_split_at x (-1))).
Proof.
  intro x; unfold db_is_nonneg; intro k; unfold_satdb; destruct x; destruct b, b0; simpl; lia.
Qed.

Lemma db_split_mid : forall x k, sat_dbound (snd (db_split_at (fst (db_split_at x 0)) (-1))) k -> k = 0.
Proof.
  intros x k.
  unfold_satdb; unfold db_split_at; destruct x; destruct b, b0; simpl; lia.
Qed.

Definition db_mul_pos (x y : dbound) :=
  if unsatb_db x then
    x
  else if unsatb_db y then
    y
  else
    match x with
    | (lx, ux) =>
        match y with
        | (ly, uy) => (mul_bound lx ly, mul_bound ux uy)
        end
    end.

Lemma nonneg_mul_monotone_r : forall k k' x x',
  0 <= k -> 0 <= k' -> k <= x -> k' <= x' -> k * k' <= x * x'.
Proof.
  intros.
  assert (k = 0 \/ 0 < k) as Hk. omega.
  assert (k' = 0 \/ 0 < k') as Hk'. omega.
  destruct Hk as [Hk | Hk].
    rewrite Hk in *.
    rewrite Z.mul_0_l.
    apply Z.mul_nonneg_nonneg; [assumption | omega].

  destruct Hk' as [Hk' | Hk'].
    rewrite Hk' in *.
    rewrite Z.mul_0_r.
    apply Z.mul_nonneg_nonneg; [omega | assumption].

  assert (Hx := Z.mul_le_mono_pos_l k' x' x).
  assert (0 < x) as Hxy. omega. apply Hx in Hxy.
  assert (H_lex := Z.mul_le_mono_pos_r k x k').
  assert (Hxk' := Hk').
  apply H_lex in Hxk'.
  apply Z.le_trans with (m := (x*k')).
  now apply Hxk'. 
  apply Hx. now apply Z.lt_le_trans with (m := k).
  assumption.
Qed.

(*
Lemma nonneg_mul_monotone_l : forall k x y,
  0 <= x -> 0 <= y -> x <= k -> y <= k -> x * y <= k.
Proof.
  intros.
  assert (Hx := Z.mul_le_mono_pos_l y 1 x).
  rewrite Z.mul_1_r in Hx.
  assert (x = 0 \/ 0 < x) as Hk. omega.
  destruct Hk as [Hk | Hk].
    rewrite Hk in *.
    now rewrite Z.mul_0_l.

    assert (x * y <= x).
      apply Hx. assumption.
*)
Ltac nonneg_mul_r H H0 :=
  apply nonneg_mul_monotone_r; try (apply H; split; [trivial | assumption]); try (apply H0; split; [trivial | assumption]).

Lemma Z_lt_le : forall (x y : Z), x < y \/ y <= x.
Proof. intros; omega. Qed.

Lemma db_mul_nonneg_valid : forall x y k k',
  db_is_nonneg x -> db_is_nonneg y -> (sat_dbound x k -> sat_dbound y k' -> sat_dbound (db_mul_pos x y) (k * k')).
Proof.
  intros x y k k'.
  intros Hnx Hny.
  assert (Hk := Hnx k).
  assert (Hk' := Hny k').
  intros Hkx Hk'y.
  assert (Hpk := Hkx); apply Hk in Hpk.
  assert (Hpk' := Hk'y); apply Hk' in Hpk'.
  unfold db_mul_pos;
    eqelim (unsatb_db x).
    rewrite unsatb_db_true_iff in H0; specialize (H0 k); contradiction.
    eqelim (unsatb_db y).
    rewrite unsatb_db_true_iff in H1; specialize (H1 k'); contradiction.
  unfold db_is_nonneg in *; unfold db_mul_pos, mul_bound; destruct x, y; destruct b, b0, b1, b2; simpl in *;
    unfold_satdb; simpl in *; split; try trivial; destruct Hkx, Hk'y;
    apply nonneg_mul_monotone_r; try lia; try apply (Hnx z); try apply (Hny z0);
    try apply (Hny z1); lia.
Qed.
  
Definition db_mul (x y : dbound) :=
  let (xn, xp) := db_split_at x (-1) in
  let (yn, yp) := db_split_at y (-1) in
  let pp := db_mul_pos xp yp in
  let pn := db_neg (db_mul_pos xp (db_neg yn)) in
  let np := db_neg (db_mul_pos (db_neg xn) yp) in
  let nn := db_mul_pos (db_neg xn) (db_neg yn) in
  db_join (db_join pp pn) (db_join np nn).

Definition split_nzp (x : dbound) :=
  let (xnp, xp) := db_split_at x 0 in
  let (xn, xz) := db_split_at xnp (-1) in
  (xn, xz, xp).

Definition db_mul_check (x y z : dbound) :=
  (*
  let (ynz, yp) := split_nzp y in
  let (yn, yz) := ynz in
  let (znz, zp) := split_nzp z in
  let (zn, zz) := znz in
  let pp := db_mul_pos yp zp in
  let pn := db_neg (db_mul_pos yp (db_neg zn)) in
  let np := db_neg (db_mul_pos (db_neg yp) zp) in
  let nn := db_mul_pos (db_neg yn) (db_neg zn) in
  *)
  negb (unsatb_db (db_meet x (db_mul y z))).

Theorem db_mul_sound : forall (x x' : dbound) (k k' : Z),
  sat_dbound x k -> sat_dbound x' k' -> sat_dbound (db_mul x x') (k * k').
Proof.
  intros.
  unfold db_mul.
  assert (Hp := db_split_nonneg x).
  assert (Hn := db_split_neg x).
  assert (Hp' := db_split_nonneg x').
  assert (Hn' := db_split_neg x').
  rewrite (db_split_iff x (-1)) in H.
  rewrite (db_split_iff x' (-1)) in H0.
  remember (db_split_at x (-1)) as spx.
  remember (db_split_at x' (-1)) as spx'.
  destruct spx, spx'; simpl in H, H0, Hp, Hp', Hn, Hn'.
  apply db_join_if.
  remember (k * k') as kk'.
  destruct H as [Hxn | Hxp]; [right | left];
    apply db_join_if;
    (destruct H0 as [Hxn' | Hxp'] ; [right | left]).

  assert (kk' = (-k) * (-k')) as Hneg. 
    rewrite <- Zopp_mult_distr_l;
    rewrite <- Zopp_mult_distr_r;
    now rewrite Zopp_involutive.
  rewrite Hneg.

  apply db_mul_nonneg_valid. now apply db_pos_nonneg. now apply db_pos_nonneg.
  rewrite <- db_neg_valid. assumption.
  rewrite <- db_neg_valid. assumption.

  assert (kk' = - ((-k) * k')) as Hneg.
    rewrite <- Zopp_mult_distr_l; now rewrite Zopp_involutive.
  rewrite Hneg; rewrite <- db_neg_valid;
    apply db_mul_nonneg_valid. now apply db_pos_nonneg. assumption.
  rewrite <- db_neg_valid. assumption.
  assumption.

  assert (kk' = -(k * (-k'))) as Hneg. rewrite <- Zopp_mult_distr_r; now rewrite Zopp_involutive.
  rewrite Hneg; rewrite <- db_neg_valid; apply db_mul_nonneg_valid; repeat assumption.
  now apply db_pos_nonneg. rewrite <- db_neg_valid; repeat assumption.

  rewrite Heqkk'; apply db_mul_nonneg_valid; repeat assumption.
Qed.
  
Lemma db_mul_check_sound : forall (x y z : dbound) (k k' : Z),
  sat_dbound y k -> sat_dbound z k' -> sat_dbound x (k * k') -> db_mul_check x y z = true.
Proof.
  intros; unfold db_mul_check.
  rewrite Bool.negb_true_iff.
  assert (Hm := db_mul_sound y z k k').
  apply Hm in H0.
  apply Bool.not_true_is_false; intro.
  apply unsatb_db_true_iff in H2; unfold unsat_db in H2.
  assert (sat_dbound (db_meet x (db_mul y z)) (k*k')).
  apply db_sat_impl_meet; split; assumption.
  now apply H2 in H3.
  assumption.
Qed.

Lemma quot_mono_pos : forall a a' b b',
  0 <= a <= a' -> 0 < b' <= b -> Z.quot a b <= Z.quot a' b'.
Proof.
  intros.
  apply Z.le_trans with (m := Z.quot a b').
  apply Z.quot_le_compat_l; lia.
  apply Z.quot_le_mono; lia.
Qed.
  
Definition bound_div_pos x y :=
  match x with
  | Unbounded => Unbounded
  | Bounded kx =>
    match y with
    | Unbounded => Bounded 0
    | Bounded ky => Bounded (Z.quot kx ky)
    end
  end.

Lemma unbounded_db_not_nonneg : forall (b : bound),
  ~ db_is_nonneg (Unbounded, b).
Proof.
  intro b; unfold db_is_nonneg; unfold_satdb; intro; destruct b; simpl.
  assert (Hf := H (-1)); lia.
  assert (Hf := H (Z.min (-1) z)); lia.
Qed.
  
Definition db_div_pos (x y : dbound) :=
  (bound_div_pos (fst x) (snd y), bound_div_pos (snd x) (fst y)).

Lemma db_div_pos_sound : forall (x y : dbound) (k k' : Z),
  db_is_nonneg x -> db_is_positive y ->
    sat_dbound x k -> sat_dbound y k' -> sat_dbound (db_div_pos x y) (Z.quot k k').
Proof.
  intros x y k k' Hpx Hpy.
  unfold db_div_pos; destruct x, y; destruct b, b0, b1, b2; simpl in *;
    intros; try trivial;
    try apply unbounded_db_not_nonneg in Hpx;
    try (apply db_pos_nonneg in Hpy; apply unbounded_db_not_nonneg in Hpy);
    unfold db_is_positive, db_is_nonneg in *; unfold_satdb; simpl in *; try lia;
        assert (Hpk := Hpx k); assert (Hpk' := Hpy k').
    split; [apply Z.quot_pos; lia | trivial].
    split; [apply quot_mono_pos | trivial].
      assert (Hpz := Hpx z). lia. lia.
    split; [apply Z.quot_pos ; lia | apply quot_mono_pos].
      lia. assert (Hpz1 := Hpy z1). lia.
    split; apply quot_mono_pos; try lia.
      assert (Hpz := Hpx z); assert (Hpz0 := Hpx z0); lia.
      assert (Hpz1 := Hpy z1); assert (hpz2 := Hpy z2); lia.
Qed.

Definition db_div (x y : dbound) :=
  let (xn, xnn) := db_split_at x (-1) in
  (* let (xz, xp) := db_split_at xnn 0 in *)
  let (yn, ynn) := db_split_at y (-1) in
  let (yz, yp) := db_split_at ynn 0 in
  let pp := db_div_pos xnn yp in
  let pn := db_neg (db_div_pos xnn (db_neg yn)) in
  let np := db_neg (db_div_pos (db_neg xn) yp) in
  let nn := db_div_pos (db_neg xn) (db_neg yn) in
  db_join (db_join pp pn) (db_join np nn).

Definition db_div_check (x y z : dbound) :=
  negb (unsatb_db (db_meet x (db_div y z))).

Theorem db_div_sound : forall (x x' : dbound) (k k' : Z),
  k' <> 0 -> sat_dbound x k -> sat_dbound x' k' -> sat_dbound (db_div x x') (Z.quot k k').
Proof.
  intros.
  unfold db_div.
  assert (Hxn := db_split_neg x);
    assert (Hxnn := db_split_nonneg x).
  assert (Hyn := db_split_neg x');
    assert (Hynn := db_split_nonneg x');
    assert (Hyp := db_split_pos (snd (db_split_at x' (-1)))).
  remember (db_split_at x (-1)) as xs; remember (db_split_at x' (-1)) as x's;
  remember (db_split_at (snd x's) 0) as x'ss.
  rewrite (db_split_iff x (-1)) in H0; rewrite (db_split_iff  x' (-1)) in H1.
  destruct xs, x's, x'ss; unfold db_split_at in Heqxs, Heqx's;
    inversion Heqxs; inversion Heqx's; inversion Heqx'ss; simpl in *.
  destruct H0; [apply db_join_r | apply db_join_l];
    destruct H1; [apply db_join_r | apply db_join_l | apply db_join_r | apply db_join_l ];
    assert (Sk := H0); try apply Hxn in Sk; try apply Hxnn in Sk;
    assert (Sk' := H1); try apply Hyn in Sk'; try apply Hynn in Sk'.

  assert (Z.quot k k' = Z.quot (-k) (-k')) as Heq.
    rewrite Z.quot_opp_l; [rewrite <- Z.quot_opp_r; [now rewrite Z.opp_involutive | lia] | lia].
  rewrite Heq.
  apply db_div_pos_sound.
    rewrite <- H3; apply db_pos_nonneg; assumption.
    rewrite <- H5; assumption.
    rewrite <- db_neg_valid; assumption.
    rewrite <- db_neg_valid; assumption.

  assert (- (Z.quot k k') = Z.quot (-k) k') as Heq.
    rewrite Z.quot_opp_l; [trivial | lia].
  rewrite db_neg_valid_2; rewrite Heq.
  apply db_div_pos_sound.
    rewrite <- H3; apply db_pos_nonneg; assumption.
    rewrite <- H6; rewrite <- H8; assumption.
    now rewrite <- db_neg_valid.
    rewrite <- H6; apply db_sat_impl_meet; split;
      [rewrite H6; assumption |
       apply db_satmeet in Sk' ; unfold_satdb; simpl in *; lia].

  
  assert (- (Z.quot k k') = Z.quot k (-k')) as Heq.
    rewrite Z.quot_opp_r; [lia | trivial].
  rewrite db_neg_valid_2; rewrite Heq.
  apply db_div_pos_sound.
    rewrite <- H4; assumption.
    rewrite <- H5; assumption.
    assumption.
    now rewrite <- db_neg_valid.
  
  apply db_div_pos_sound.
    rewrite <- H4; assumption.
    rewrite <- H6; rewrite <- H8; assumption.
    assumption.
    rewrite <- H6; apply db_sat_impl_meet; split;
      [rewrite H6; assumption |
       apply db_satmeet in Sk' ; unfold_satdb; simpl in *; lia].
Qed.

Theorem db_div_check_sound : forall (x y z : dbound) (k k' : Z),
  k' <> 0 -> sat_dbound y k -> sat_dbound z k' -> sat_dbound x (Z.quot k k')
    -> db_div_check x y z = true.
Proof.
  intros. unfold db_div_check.
  rewrite Bool.negb_true_iff.
  apply Bool.not_true_is_false; intro.
  rewrite unsatb_db_true_iff in H3.
  assert (sat_dbound (db_meet x (db_div y z)) (Z.quot k k')) as Hs.
    apply db_sat_impl_meet; split; [assumption | apply db_div_sound; assumption].
  now apply H3 in Hs.
Qed.
