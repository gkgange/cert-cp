Require Import ZArith.
Require Import assign.
Require Import domain.
Require Import range.
Require Import range_properties.
Require Import constraint.

Definition linterm : Type := (Z * iterm)%type.

(* c_1 x_1 + ... + c_n x_n <= k *)
Definition lin_leq : Type := ((list linterm) * Z)%type.
Definition lin_neq : Type := ((list linterm) * Z)%type.

Definition eval_linterm (term : linterm) (theta : valuation) := (fst term)*(eval_iterm (snd term) theta).

Fixpoint eval_linsum ts theta :=
  match ts with
  | nil => 0%Z
  | cons t ts' => (eval_linterm t theta) + (eval_linsum ts' theta)
  end.

Definition linterm_db_from_dom (t : linterm) (ds : domset) :=
  mul_z_dbound (fst t) (fst (term_dom ds (snd t))).

Theorem linterm_db_from_dom_valid :
  forall (t : linterm) (ds : domset) (theta : valuation),
    eval_domset ds theta ->
      sat_dbound (linterm_db_from_dom t ds) (eval_linterm t theta).
Proof.
  intros. destruct t. unfold linterm_db_from_dom.
  assert (Ht := term_dom_valid ds theta H i).
  unfold sat_dom in Ht; destruct Ht as [Ht _].
  apply mul_z_dbound_valid. unfold eval_dom, sat_dom in H; tauto.
Qed.

(* Compute the lb of a linear sum implied by ~cl. *)
Fixpoint linsum_db_from_dom (ts : list linterm) (ds : domset) :=
  match ts with
  | nil => (Bounded 0%Z, Bounded 0%Z)
  | cons t ts' =>
      db_add (linterm_db_from_dom t ds)
             (linsum_db_from_dom ts' ds)
  end.

Theorem linsum_db_valid : forall (ts : list linterm) (ds : domset) (theta : valuation),
    eval_domset ds theta ->
      sat_dbound (linsum_db_from_dom ts ds) (eval_linsum ts theta).
Proof.
  intros.
  induction ts.
  unfold linsum_db_from_dom, sat_dbound; simpl. omega.

  unfold linsum_db_from_dom ; fold linsum_db_from_dom.
  unfold eval_linsum; fold eval_linsum.
  apply db_impl_adddb.
  split.

  apply linterm_db_from_dom_valid; exact H.
  exact IHts.
Qed.

Definition eval_lincon lincon (theta : valuation) :=
  (eval_linsum (fst lincon) theta) <= (snd lincon).

Definition eval_lin_neq diseq theta :=
  (eval_linsum (fst diseq) theta) <> (snd diseq).

Definition check_lincon_unsat (lincon : lin_leq) (ds : domset) : bool :=
  negb (satb_lb (fst (linsum_db_from_dom (fst lincon) ds)) (snd lincon)).

Definition check_lin_neq_unsat diseq ds :=
  match db_constant_value (linsum_db_from_dom (fst diseq) ds) with
    | None => false
    | Some k => Z.eqb k (snd diseq)
  end.
                                    
Definition LinearCon := mkConstraint lin_leq eval_lincon.
Definition LinearNE := mkConstraint lin_neq eval_lin_neq.

Theorem check_lincon_unsat_valid : forall (lincon : lin_leq) (ds : domset),
  check_lincon_unsat lincon ds = true -> cst_is_unsat LinearCon lincon ds.
Proof.
  unfold cst_is_unsat, check_lincon_unsat.
  intros lincon ds;
  destruct lincon; simpl; unfold eval_lincon; intros.
  rewrite Bool.negb_true_iff in H.
  rewrite satb_lb_false_iff_notlb in H.
  apply linsum_db_valid with (ts := l) in H0.
  unfold sat_dbound in H0; unfold sat_lb in *; destruct (linsum_db_from_dom l ds); destruct b, b0; simpl in *;
    try (tauto || omega).
Qed.  

Theorem check_lin_neq_unsat_valid : forall (lincon : lin_neq) (ds : domset),
  check_lin_neq_unsat lincon ds = true -> cst_is_unsat LinearNE lincon ds.
Proof.
  unfold check_lin_neq_unsat, cst_is_unsat, eval; simpl; unfold eval_lin_neq.
  intros cst ds; eqelim (db_constant_value (linsum_db_from_dom (fst cst) ds)); destruct cst as (ls, c).
  assert (Hc := db_constant_value_2 (linsum_db_from_dom (fst (ls, c)) ds) z H0).
  intros Hz theta Hds Hls.
  simpl in *.
  assert (Hsum := linsum_db_valid ls ds theta Hds).
  apply Z.eqb_eq in Hz.
  specialize (Hc _ Hsum).
  congruence.
  intros; congruence.
Qed.

Definition CheckLinearUnsat := mkUnsatChecker LinearCon check_lincon_unsat check_lincon_unsat_valid.
Definition CheckLinearNeqUnsat := mkUnsatChecker LinearNE check_lin_neq_unsat check_lin_neq_unsat_valid.

(* Computing solutions. *)
Definition check_lincon_sol lincon theta :=
  Z.leb (eval_linsum (fst lincon) theta) (snd lincon).

Definition check_lin_neq_sol lincon theta :=
  negb (Z.eqb (eval_linsum (fst lincon) theta) (snd lincon)).
Theorem check_lincon_sol_valid :
    forall lincon theta,
      (check_lincon_sol lincon theta = true) -> eval_lincon lincon theta.
Proof.
  intros lincon zs; destruct lincon.
  unfold check_lincon_sol;  simpl.
  unfold eval_lincon; simpl.
  intros; now apply Z.leb_le.
Qed.

Theorem check_lin_neq_sol_valid :
    forall lincon theta,
      (check_lin_neq_sol lincon theta = true) -> eval_lin_neq lincon theta.
Proof.
  intros lincon zs; destruct lincon.
  unfold check_lin_neq_sol;  simpl.
  unfold eval_lin_neq; simpl.
  rewrite Bool.negb_true_iff; intros.
  intro H'; apply Z.eqb_eq in H'; congruence.
Qed.

Definition LinearSolCheck := mkSolChecker LinearCon check_lincon_sol check_lincon_sol_valid.
Definition LinearNESolCheck := mkSolChecker LinearNE check_lin_neq_sol check_lin_neq_sol_valid.
