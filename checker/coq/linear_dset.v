Require Import ZArith.
Require Import Bool.
Require Import prim.
Require Import bounds.
Require Import domain.
Require Import domset.
Require Import linear.
Require Import reif.

Definition eval_linterm term theta := (fst term)*(eval_ivar (snd term) theta).

Definition linterm_db_from_dbfun (t : linterm) (f : dbfun) :=
  mul_z_dbound (fst t) (f (snd t)).

Theorem linterm_db_from_dbfun_eq :
  forall (t : linterm) (f : dbfun) (cl : clause),
  is_negcl_dbfun f cl ->
    linterm_db_from_dbfun t f = linterm_db_from_negclause t cl.
Proof.
  intros; destruct t; unfold linterm_db_from_negclause, linterm_db_from_dbfun.
  unfold is_negcl_dbfun in H.
  now rewrite H.
Qed.

(* Compute the lb of a linear sum implied by ~cl. *)
Fixpoint linsum_db_from_dbfun (ts : list linterm) (f : dbfun) :=
  match ts with
  | nil => (Bounded 0%Z, Bounded 0%Z)
  | cons t ts' =>
      db_add (linterm_db_from_dbfun t f)
             (linsum_db_from_dbfun ts' f)
  end.

Theorem linsum_db_from_dbfun_eq : forall (ts : list linterm) (f : dbfun) (cl : clause),
  is_negcl_dbfun f cl ->
    linsum_db_from_dbfun ts f  = linsum_db_from_negclause ts cl.
Proof.
  intros; induction ts.
  unfold linsum_db_from_dbfun, linsum_db_from_negclause, sat_dbound; now simpl.

  unfold linsum_db_from_negclause, linsum_db_from_dbfun ; simpl;
    fold linsum_db_from_negclause; fold linsum_db_from_dbfun.
  now rewrite IHts, linterm_db_from_dbfun_eq with (cl := cl).
Qed.

Definition check_lincon_dbfun (lincon : lin_leq) (f : dbfun) : bool :=
  negb (satb_lb (fst (linsum_db_from_dbfun (fst lincon) f)) (snd lincon)).

Theorem check_lincon_dbfun_eq : forall (lincon : lin_leq) (f : dbfun) (cl : clause),
  is_negcl_dbfun f cl ->
    check_lincon_dbfun lincon f = check_lincon lincon cl.
Proof.
  intros; unfold check_lincon_dbfun, check_lincon;
    now rewrite linsum_db_from_dbfun_eq with (cl := cl).
Qed.

Theorem check_lincon_dbfun_valid : forall (lincon : lin_leq) (f : dbfun) (cl : clause),
  is_negcl_dbfun f cl /\ check_lincon_dbfun lincon f = true ->
    implies (eval_lincon lincon) (eval_clause cl).
Proof.
  intros; apply check_lincon_valid; destruct H;
  now rewrite <- check_lincon_dbfun_eq with (f := f).
Qed.
  
Definition LinearDSet : DomDBCheck :=
  mkDomDBCheck (lin_leq) (eval_lincon) (check_lincon_dbfun) (check_lincon_dbfun_valid).

Definition LinearDBCheck : Constraint :=
  (CheckOfDomDBCheck (DomboundedDBCheck LinearDSet)). 

Definition check_linear_dbnd (l : lin_leq) (ds : domset) (cl : clause) :=
  (LinearDBCheck).(check) (ds, l) cl.

Definition check_reif_linear_dbnd (r : lit) (l : lin_leq) (ds : domset) (cl : clause) :=
  (ReifiedConstraint (LinearDBCheck)).(check) (r, (ds, l)) cl.
