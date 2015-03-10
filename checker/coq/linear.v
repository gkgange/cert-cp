Require Import ZArith.
Require Import Bool.
Require Import prim. Require Import bounds.
Require Import sol.
Require Import map.

Definition linterm : Type := (Z * ivar)%type.

(* c_1 x_1 + ... + c_n x_n <= k *)
Definition lin_leq : Type := ((list linterm) * Z)%type.

Definition eval_linterm term theta := (fst term)*(eval_ivar (snd term) theta).

Fixpoint eval_linsum ts theta :=
  match ts with
  | nil => 0%Z
  | cons t ts' => (eval_linterm t theta) + (eval_linsum ts' theta)
  end.

Definition linterm_db_from_negclause (t : linterm) (cl : clause) :=
  mul_z_dbound (fst t) (db_from_negclause (snd t) cl).

Theorem linterm_db_from_negclause_valid :
  forall (t : linterm) (cl : clause) (theta : asg),
    ~eval_clause cl theta ->
      sat_dbound (linterm_db_from_negclause t cl) (eval_linterm t theta).
Proof.
  intros. destruct t. unfold linterm_db_from_negclause.
  apply mul_z_dbound_valid. apply db_from_negclause_valid. exact H.
Qed.

(* Compute the lb of a linear sum implied by ~cl. *)
Fixpoint linsum_db_from_negclause (ts : list linterm) (cl : clause) :=
  match ts with
  | nil => (Bounded 0%Z, Bounded 0%Z)
  | cons t ts' =>
      db_add (linterm_db_from_negclause t cl)
             (linsum_db_from_negclause ts' cl)
  end.

Theorem linsum_db_valid : forall (ts : list linterm) (cl : clause) (theta : asg),
  ~ eval_clause cl theta ->
      sat_dbound (linsum_db_from_negclause ts cl) (eval_linsum ts theta).
Proof.
  intros.
  induction ts.
  unfold linsum_db_from_negclause, sat_dbound; simpl. omega.

  unfold linsum_db_from_negclause ; fold linsum_db_from_negclause.
  unfold eval_linsum; fold eval_linsum.
  apply db_impl_adddb.
  split.

  apply linterm_db_from_negclause_valid; exact H.
  exact IHts.
Qed.

Theorem notlinsumdb_negcl_impl_clause : forall (ts : list linterm) (cl : clause) (theta : asg),
  ~ sat_dbound (linsum_db_from_negclause ts cl) (eval_linsum ts theta) -> eval_clause cl theta.
Proof.
  intros.
  assert (eval_clause cl theta \/ ~ eval_clause cl theta). apply dec_evalclause.
  destruct H0.
  exact H0.
  assert (sat_dbound (linsum_db_from_negclause ts cl) (eval_linsum ts theta)).
  apply linsum_db_valid. exact H0.
  tauto.
Qed.

Definition eval_lincon lincon (theta : asg) :=
  (eval_linsum (fst lincon) theta) <= (snd lincon).
  
Definition check_lincon (lincon : lin_leq) (cl : clause) : bool :=
  negb (satb_lb (fst (linsum_db_from_negclause (fst lincon) cl)) (snd lincon)).

Theorem check_lincon_valid : forall (lincon : lin_leq) (cl : clause),
  check_lincon lincon cl = true ->
    implies (eval_lincon lincon) (eval_clause cl).
Proof.
  unfold implies, check_lincon, eval_lincon.
  intros lincon cl.
  destruct lincon; simpl.
  rewrite negb_true_iff.
  rewrite satb_lb_false_iff_notlb.
  intros.
  apply notlinsumdb_negcl_impl_clause with (ts := l).
  apply notsat_lb_impl_notdb.
  destruct (linsum_db_from_negclause l cl); simpl in *.
  apply Zle_notlb_trans with (k' := z).
  exact H0.
  exact H.
Qed.

Definition LinearCon := mkConstraint lin_leq eval_lincon.
Definition CheckLinear := mkChecker LinearCon check_lincon check_lincon_valid.

Definition BoundedLinCheck := BoundedChecker LinearCon CheckLinear.
Definition check_linear_bnd (x : lin_leq) (bs : list (ivar*Z*Z)) (cl : clause) :=
  check (BoundedConstraint LinearCon) (BoundedChecker LinearCon CheckLinear) (bs, x) cl.

(* Computing solutions. *)
Definition eval_linterm_zsol term zs :=
  match zsol_val zs (snd term) with
  | None => None
  | Some x => Some ((fst term)*x)
  end.

Fixpoint eval_linsum_zsol ts zs :=
  match ts with
  | nil => Some 0%Z
  | cons t ts' =>
    match eval_linterm_zsol t zs with
    | Some x =>
      match eval_linsum_zsol ts' zs with
      | Some r => Some (x + r)
      | None => None
      end
    | None => None
    end
  end.

Definition check_lincon_zsol lincon zs :=
  match eval_linsum_zsol (fst lincon) zs with
  | None => false
  | Some k => Z_leb k (snd lincon)
  end.

Theorem eval_linterm_zsol_valid :
  forall (zs : zsol) (v : Z) (theta : asg) (t : linterm),
    eval_linterm_zsol t zs = Some v -> 
      eval_zsol zs theta -> eval_linterm t theta = v.
Proof.
  intros.
  unfold eval_linterm, eval_linterm_zsol in *; simpl.
  remember (zsol_val zs (snd t)) as f; destruct f; destruct t; simpl in *.
  apply eq_sym in Heqf; apply zsol_val_valid with (theta := theta) in Heqf; try assumption.
  injection H; intros.
  now rewrite Heqf.
  discriminate.
Qed.
  
Theorem eval_linsum_zsol_plus :
  forall (zs : zsol) (v v' : Z) (a : linterm) (ts : list linterm),
    eval_linterm_zsol a zs = Some v /\ eval_linsum_zsol ts zs = Some v' ->
      eval_linsum_zsol (a :: ts) zs = Some (v + v').
Proof.
  intros.
  unfold eval_linsum_zsol; fold eval_linsum_zsol.
  remember (eval_linterm_zsol a zs) as ea; destruct ea.
  remember (eval_linsum_zsol ts zs) as ets; destruct ets.
  destruct H as [Hz Hz0]; inversion Hz; inversion Hz0.
  trivial.
  now destruct H. now destruct H.
Qed.

Fixpoint linsum_is_ground (zs : zsol) (ts : list linterm) :=
  match ts with
  | nil => True
  | cons (_, x) ts' => ZMaps.In x zs /\ linsum_is_ground zs ts'
  end.

Theorem linsum_zsol_some_is_ground :
  forall (zs : zsol) (ts : list linterm),
    (exists k, eval_linsum_zsol ts zs = Some k) -> linsum_is_ground zs ts.
Proof.
  intros zs ts H.
  induction ts; unfold eval_linsum_zsol, linsum_is_ground; simpl; try trivial.
  eelim H; intro.
  fold eval_linsum_zsol; fold eval_linsum; fold linsum_is_ground; destruct a; simpl.
  intros; remember (eval_linterm_zsol (z, i) zs) as ez;
    remember (eval_linsum_zsol ts zs) as ets.
  destruct ez, ets; try congruence.
  symmetry in Heqets, Heqez.
  split.
  unfold eval_linterm_zsol, zsol_val in Heqez; simpl in Heqez.
  remember (ZMaps.find i zs) as fi; destruct fi; try congruence.
  assert (ZMaps.In i zs \/ ~ ZMaps.In i zs).
    tauto.
  destruct H1; try assumption.
  apply not_find_in_iff in H1. congruence.
  apply IHts. eexists.
  now instantiate (1 := z1).
Qed.

Theorem ground_linsum_eq :
  forall (zs : zsol) (theta : asg) (ts : list linterm),
    linsum_is_ground zs ts ->
      eval_zsol zs theta -> eval_linsum_zsol ts zs = Some (eval_linsum ts theta).
Proof.
  intros zs theta ts.
  induction ts.
  unfold linsum_is_ground, eval_linsum_zsol, eval_linsum; tauto.
  
  unfold linsum_is_ground, eval_linsum_zsol, eval_linsum;
    fold linsum_is_ground; fold eval_linsum_zsol; fold eval_linsum; intros.
  destruct a; simpl in *. destruct H as [Hi Hg].
  remember (eval_linterm_zsol (z, i) zs) as ea.
  remember (eval_linsum_zsol ts zs) as ets.
  apply IHts in Hg.
  destruct ets; simpl in *.
    inversion Hg as [Hz0]; clear Hg. rewrite <- Hz0.
    destruct ea.
    symmetry in Heqea; apply eval_linterm_zsol_valid with (theta := theta) in Heqea.
    now rewrite Heqea. assumption.
    unfold eval_linterm_zsol, zsol_val in Heqea; simpl in *.
    remember (ZMaps.find i zs) as fi.
    destruct fi; try discriminate.
    symmetry in Heqfi; now apply not_find_in_iff in Heqfi.
    discriminate. assumption.
Qed.

Theorem check_lincon_zsol_valid :
    forall lincon zs,
      (check_lincon_zsol lincon zs = true) ->
        implies (eval_zsol zs) (eval_lincon lincon).
Proof.
  intros lincon zs; destruct lincon.
  unfold check_lincon_zsol, implies; simpl.
  remember (eval_linsum_zsol l zs) as el.
  destruct el; symmetry in Heqel; try congruence.
  assert (linsum_is_ground zs l).
    apply linsum_zsol_some_is_ground; eexists; now instantiate (1 := z0).
  unfold eval_lincon.
  intros; simpl in *.
  assert (eval_linsum_zsol l zs = Some (eval_linsum l theta)).
    apply ground_linsum_eq; try assumption.
  rewrite Heqel in H2.
  inversion H2.
  rewrite <- H4.
  now apply Z_leb_iff_le in H0.
Qed.

Definition LinearSolCheck := mkSolCheck LinearCon check_lincon_zsol check_lincon_zsol_valid.