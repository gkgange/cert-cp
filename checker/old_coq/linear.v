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
Definition check_lincon_sol lincon theta :=
  Z_leb (eval_linsum (fst lincon) theta) (snd lincon).

Theorem check_lincon_sol_valid :
    forall lincon theta,
      (check_lincon_sol lincon theta = true) -> eval_lincon lincon theta.
Proof.
  intros lincon zs; destruct lincon.
  unfold check_lincon_sol;  simpl.
  unfold eval_lincon; simpl.
  intros; now apply Z_leb_iff_le.
Qed.

Definition LinearSolCheck := mkSolCheck LinearCon check_lincon_sol check_lincon_sol_valid.