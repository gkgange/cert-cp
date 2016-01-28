Require Import ZArith.
Require Import Bool.
Require Import List.
Require Import assign.
Require Import domain.
Require Import range.
Require Import range_properties.
Require Import constraint.
Require arith_ops.
(* Require reif. *)

(* Propagation for multiplication.
 * We're not doing full factorization, just bounds. *)

Inductive int_term :=
  | Const : Z -> int_term
  | Var : ivar -> int_term.

Definition eval_int_term term theta :=
  match term with
  | Const c => c
  | Var v => eval_ivar v theta
  end.

Definition domset_term_dbound term ds :=
  match term with
  | Const c => (Bounded c, Bounded c)
  | Var x => (fst (var_dom ds x))
  end.

Inductive int_arith :=
  | Mul : ivar -> ivar -> ivar -> int_arith
  | Div : ivar -> ivar -> ivar -> int_arith.
  
(* This is kind of an awkward definition. *)
Definition eval_int_arith arith theta :=
  match arith with
  | Mul x y z => (eval_ivar x theta) = (eval_ivar y theta)*(eval_ivar z theta)
  | Div x y z =>
    (eval_ivar z theta) <> 0 /\ (eval_ivar x theta) = Z.quot (eval_ivar y theta) (eval_ivar z theta)
  end.

Definition ArithConstraint := mkConstraint int_arith eval_int_arith.

(* What are the semantics of Div?
   - Round towards zero/round towards -infty?
   - x/0 fails? or x/0 = 0?
   Most sense to have round-towards-zero, x/0 fails. *)
Definition check_int_arith_sol arith theta :=
  match arith with
  | Mul x y z => Z.eqb (eval_ivar x theta) ((eval_ivar y theta)*(eval_ivar z theta))
  | Div x y z =>
    andb (negb (Z.eqb (eval_ivar z theta) 0)) (Z.eqb (eval_ivar x theta) (Z.quot (eval_ivar y theta) (eval_ivar z theta)))
  end.

Definition check_int_arith arith (ds : domset) :=
  match arith with
  | Mul x y z =>
    unsatb_db
      (db_meet
         (db_from_dom x ds)
         (arith_ops.db_mul (db_from_dom y ds) (db_from_dom z ds)))
  | Div x y z => negb (arith_ops.db_div_check (db_from_dom x ds) (db_from_dom y ds) (db_from_dom z ds))
  end.

Theorem check_int_arith_valid :
  forall (arith : int_arith) (ds : domset),
    check_int_arith arith ds = true -> cst_is_unsat ArithConstraint arith ds.
Proof.
  unfold ArithConstraint, cst_is_unsat.
  unfold eval_int_arith, check_int_arith; destruct arith; simpl in *;
    intros; try discriminate.
  rewrite unsatb_db_true_iff in H.
(*   apply evalclause_contra; intros. *)

  assert (Hx := H0); apply db_from_dom_valid with (x := i) in Hx.
  assert (Hy := H0); apply db_from_dom_valid with (x := i0) in Hy.
  assert (Hz := H0); apply db_from_dom_valid with (x := i1) in Hz.
  remember (db_from_dom i ds) as ix.
  remember (db_from_dom i0 ds) as iy.
  remember (db_from_dom i1 ds) as iz.
  assert (Hyz := arith_ops.db_mul_sound iy iz (eval_ivar i0 theta) (eval_ivar i1 theta)).
  assert (Hmeet := db_sat_impl_meet ix (arith_ops.db_mul iy iz) (eval_ivar i theta)).
  assert (sat_dbound (db_meet ix (arith_ops.db_mul iy iz)) (eval_ivar i theta)).
  apply Hmeet; split; try assumption.
    rewrite H1. apply arith_ops.db_mul_sound; try assumption.
  unfold unsat_db in H. now apply H in H2.

  remember (eval_ivar i0 theta) as k; remember (eval_ivar i1 theta) as k'.
  assert (Hsk := H0); apply db_from_dom_valid with (x := i) in Hsk.
  assert (Hsk' := H0); apply db_from_dom_valid with (x := i0) in Hsk'.
  assert (Hskk' := H0); apply db_from_dom_valid with (x := i1) in Hskk'.
  remember (db_from_dom i ds) as x; remember (db_from_dom i0 ds) as y;
    remember (db_from_dom i1 ds) as z.
  destruct H1 as [Hz Hq].
  assert (Hf := arith_ops.db_div_check_sound x y z k k').
  apply negb_true_iff in H.
  assert (arith_ops.db_div_check x y z = true).
  apply Hf; [assumption | rewrite Heqk | rewrite Heqk' | rewrite <- Hq]; assumption.
  congruence.
Qed.

Definition ArithCheck := mkUnsatChecker ArithConstraint (check_int_arith) (check_int_arith_valid).

(*
Definition check_int_arith_dbfun arith (f : dbfun) :=
  match arith with
  | Mul x y z =>
    unsatb_db
      (db_meet (f x)
         (arith_ops.db_mul (f y) (f z)))
  | Div x y z => negb (arith_ops.db_div_check (f x) (f y) (f z))
  end.

Theorem check_int_arith_dbfun_valid : forall (c : int_arith) (f : dbfun) (cl : clause),
  is_domset_dbfun f cl /\ check_int_arith_dbfun c f = true ->
    implies (eval_int_arith c) (eval_clause cl).
Proof.
  unfold check_int_arith; unfold is_domset_dbfun in *.
  intros; apply check_int_arith_valid; destruct H.
  unfold check_int_arith_dbfun in H0; unfold check_int_arith.
  destruct c; try tauto; try contradiction.

  now rewrite <- (H i), <- (H i0), <- (H i1); congruence. 
  now rewrite <- (H i), <- (H i0), <- (H i1); congruence. 
Qed.
 
Definition ArithDSet :=
  mkDomDBCheck ArithConstraint (check_int_arith_dbfun) (check_int_arith_dbfun_valid).
Definition ArithDbnd := DomboundedConstraint ArithConstraint.
Definition ArithDbndCheck := DomboundedDBCheck ArithConstraint ArithDSet.

Definition ArithDomCheck :=
  CheckOfDomDBCheck ArithDbnd (ArithDbndCheck).

Definition check_arith_dbnd (a : int_arith) (ds : domset) (cl : clause) :=
  (check ArithDbnd ArithDomCheck) (ds, a) cl.

Definition check_reif_arith_dbnd (r : lit) (a : int_arith) (ds : domset) (cl : clause) :=
  (check (reif.ReifiedConstraint ArithDbnd) (reif.ReifiedCheck ArithDbnd ArithDomCheck)) (r, (ds, a)) cl.
*)

Theorem eval_int_arith_sol_valid :
    forall arith theta,
      (check_int_arith_sol arith theta = true) -> eval_int_arith arith theta.
Proof.
  intros arith theta; unfold check_int_arith_sol, eval_int_arith; destruct arith;
    [now rewrite Z.eqb_eq |
     rewrite andb_true_iff; rewrite negb_true_iff; rewrite Z.eqb_eq].
  intro H; destruct H as [H0 Hquot].
  split; [intro Heq ; rewrite <- Z.eqb_eq in Heq; now rewrite Heq in H0 | assumption].
Qed.

Definition ArithSolCheck := mkSolChecker ArithConstraint check_int_arith_sol eval_int_arith_sol_valid.