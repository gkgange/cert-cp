(* Operations on domains/intervals. *)
Require Import ZArith.
Require Import bounds.
Require Import domain.
(* Require Import Psatz. *)

Ltac unfold_satdb := unfold sat_dbound, sat_lb, sat_ub in *; simpl.

Definition db_split (x : dbound) :=
  (db_meet x (Unbounded, Bounded (-1)), db_meet x (Bounded 0, Unbounded)).

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
  
Theorem db_split_iff : forall (x : dbound) (k : Z),
  sat_dbound x k <-> sat_dbound (fst (db_split x)) k \/ sat_dbound (snd (db_split x)) k.
Proof.
  unfold db_split; simpl; intros.
  assert (k < 0 \/ 0 <= k) as Hk. omega.
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
      
Definition db_is_positive x := forall k, sat_dbound x k -> 0 <= k.
Definition db_is_positive_1 (x : dbound) :=
  match x with
  | (Unbounded, _) => False
  | (Bounded k, Unbounded) => 0 <= k
  | (Bounded k, Bounded k') => k' < k \/ 0 <= k
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
    (unsat_db x \/ (0 <= k)).
Proof.
  unfold db_is_positive, unsat_db; unfold_satdb;
    destruct x; destruct b, b0;
    simpl; intros; try congruence; inversion H0.
    right; apply H; now rewrite H2.
  assert (z0 < z \/ z <= z0) as Hz. omega.
  destruct Hz; [left; intros; omega | right; apply H; rewrite H2; omega].
Qed. 

Lemma db_positive_bounded : forall x, db_is_positive x -> (fst x) <> Unbounded.
Proof.
  intros. assert (Hl := db_positive_lb_pos x).
  rewrite db_positive_iff in H. unfold db_is_positive_1 in H.
  intro.
  destruct x; destruct b, b0; simpl in *; try tauto; try congruence.
Qed.

Lemma db_split_pos : forall x, db_is_positive (snd (db_split x)).
Proof.
  intro x; rewrite db_positive_iff; unfold db_split, db_is_positive_1; intros.
  destruct x; destruct b, b0; simpl in *; try omega.
  apply Z.le_max_r.
  right; apply Z.le_max_r.
Qed.

Lemma db_split_neg : forall x, db_is_positive (db_neg (fst (db_split x))).
Proof.
  intro x; rewrite db_positive_iff; unfold db_split, db_is_positive_1; intros.
  destruct x; destruct b, b0; simpl in *; try omega.
  assert (Z.min z (-1) <= -1).
    apply Z.le_min_r.
  omega.

  right; assert (Z.min z0 (-1) <= -1).
    apply Z.le_min_r.
  omega.
Qed.

Definition db_mul_pos (x y : dbound) :=
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

Lemma db_mul_pos_valid : forall x y k k',
  db_is_positive x -> db_is_positive y -> (sat_dbound x k -> sat_dbound y k' -> sat_dbound (db_mul_pos x y) (k * k')).
Proof.
  intros.
  assert (Hlx_pos := db_positive_lb_pos x).
  assert (Hly_pos := db_positive_lb_pos y).
  assert (Hx_bnd := H); apply db_positive_bounded in Hx_bnd.
  assert (Hy_bnd := H0); apply db_positive_bounded in Hy_bnd.
  rewrite db_positive_iff in H, H0.
  unfold db_is_positive_1 in H, H0.
  destruct x, y; destruct b, b0, b1, b2;
    unfold db_mul_pos, mul_bound; simpl in *;
    try (unfold_satdb; tauto);
    try (unfold_satdb; split; [tauto | omega]);
    unfold_satdb; simpl in *.
  split; [apply nonneg_mul_monotone_r | trivial]; try omega.
  split; [apply nonneg_mul_monotone_r | trivial]; try omega.
  split; [apply nonneg_mul_monotone_r | trivial]; try omega.
  split; [apply nonneg_mul_monotone_r | trivial]; try omega.
  apply nonneg_mul_monotone_r; try omega.
Qed.
  
Definition db_mul (x y : dbound) :=
  let (xn, xp) := db_split x in
  let (yn, yp) := db_split y in
  let pp := db_mul_pos xp yp in
  let pn := db_neg (db_mul_pos xp (db_neg yn)) in
  let np := db_neg (db_mul_pos (db_neg xn) yp) in
  let nn := db_mul_pos (db_neg xn) (db_neg yn) in
  db_join (db_join pp pn) (db_join np nn).

Theorem db_mul_sound : forall (x x' : dbound) (k k' : Z),
  sat_dbound x k -> sat_dbound x' k' -> sat_dbound (db_mul x x') (k * k').
Proof.
  intros.
  unfold db_mul.
  assert (Hp := db_split_pos x).
  assert (Hn := db_split_neg x).
  assert (Hp' := db_split_pos x').
  assert (Hn' := db_split_neg x').
  rewrite db_split_iff in H.
  rewrite db_split_iff in H0.
  remember (db_split x) as spx.
  remember (db_split x') as spx'.
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
  apply db_mul_pos_valid. assumption. assumption.
  rewrite <- db_neg_valid. assumption.
  rewrite <- db_neg_valid. assumption.

  assert (kk' = - ((-k) * k')) as Hneg.
    rewrite <- Zopp_mult_distr_l; now rewrite Zopp_involutive.
  rewrite Hneg; rewrite <- db_neg_valid;
    apply db_mul_pos_valid. assumption. assumption.
  rewrite <- db_neg_valid. assumption.
  assumption.

  assert (kk' = -(k * (-k'))) as Hneg. rewrite <- Zopp_mult_distr_r; now rewrite Zopp_involutive.
  rewrite Hneg; rewrite <- db_neg_valid; apply db_mul_pos_valid; repeat assumption.
  rewrite <- db_neg_valid; repeat assumption.

  rewrite Heqkk'; apply db_mul_pos_valid; repeat assumption.
Qed.
  

Definition db_div (x y : dbound) :=
  (Unbounded, Unbounded).

Theorem db_div_sound : forall (x x' : dbound) (k k' : Z),
  sat_dbound x k /\ sat_dbound x' k' -> sat_dbound (db_div x x') (k / k').
Proof.
  intros; destruct H as [Hx Hx'].
  unfold sat_dbound, sat_lb, sat_ub, db_mul; simpl; tauto.
Qed.