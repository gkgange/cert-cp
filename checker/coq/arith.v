Require Import ZArith.
Require Import Bool.
Require Import List.
Require Import prim.
Require Import sol.
Require Import bounds.
Require Import domain.
Require Import domset.
Require arith_ops.
Require reif.

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

Definition negcl_term_dbound term cl :=
  match term with
  | Const c => (Bounded c, Bounded c)
  | Var x => db_from_negclause x cl
  end.

Inductive int_arith :=
  | Mul : ivar -> ivar -> ivar -> int_arith
  | Div : ivar -> ivar -> ivar -> int_arith.
  
(* This is kind of an awkward definition. *)
Definition eval_int_arith arith theta :=
  match arith with
  | Mul x y z => (eval_ivar x theta) = (eval_ivar y theta)*(eval_ivar z theta)
  | Div x y z => (eval_ivar x theta) = (eval_ivar y theta)/(eval_ivar z theta)
  end.

Definition check_int_arith_sol arith theta :=
  match arith with
  | Mul x y z => Z_eqb (eval_ivar x theta) ((eval_ivar y theta)*(eval_ivar z theta))
  | Div x y z => Z_eqb (eval_ivar x theta) ((eval_ivar y theta)/(eval_ivar z theta))
  end.

Definition check_int_arith arith (cl : clause) :=
  match arith with
  | Mul x y z =>
    unsatb_db
      (db_meet
         (db_from_negclause x cl)
         (arith_ops.db_mul (db_from_negclause y cl) (db_from_negclause z cl)))
  | Div x y z => false
  end.

Theorem check_int_arith_valid :
  forall (arith : int_arith) (cl : clause),
    check_int_arith arith cl = true ->
      implies (eval_int_arith arith) (eval_clause cl).
Proof.
  unfold implies.
  unfold eval_int_arith, check_int_arith; destruct arith; simpl in *;
    intros; try discriminate.
  rewrite unsatb_db_true_iff in H.
  apply evalclause_contra; intros.

  assert (Hx := H1); apply db_from_negclause_valid with (x := i) in Hx.
  assert (Hy := H1); apply db_from_negclause_valid with (x := i0) in Hy.
  assert (Hz := H1); apply db_from_negclause_valid with (x := i1) in Hz.
  remember (db_from_negclause i cl) as ix.
  remember (db_from_negclause i0 cl) as iy.
  remember (db_from_negclause i1 cl) as iz.
  assert (Hyz := arith_ops.db_mul_sound iy iz (eval_ivar i0 theta) (eval_ivar i1 theta)).
  assert (Hmeet := db_sat_impl_meet ix (arith_ops.db_mul iy iz) (eval_ivar i theta)).
  assert (sat_dbound (db_meet ix (arith_ops.db_mul iy iz)) (eval_ivar i theta)).
  apply Hmeet; split; try assumption.
    rewrite H0. apply arith_ops.db_mul_sound; try assumption.
  unfold unsat_db in H. now apply H in H2.
Qed.

Definition ArithConstraint : Constraint :=
  mkConstraint (int_arith) (eval_int_arith).
Definition ArithBnd := BoundedConstraint ArithConstraint.
Definition ArithCheck := mkChecker ArithConstraint (check_int_arith) (check_int_arith_valid).
Definition ArithBndCheck := BoundedChecker ArithConstraint ArithCheck.
Definition check_arith_bnd (x : int_arith) (bs : list (ivar*Z*Z)) (cl : clause) := 
  (check ArithBnd ArithBndCheck) (bs, x) cl.

Definition check_int_arith_dbfun arith (f : dbfun) :=
  match arith with
  | Mul x y z =>
    unsatb_db
      (db_meet (f x)
         (arith_ops.db_mul (f y) (f z)))
  | Div x y z => false
  end.

Theorem check_int_arith_dbfun_valid : forall (c : int_arith) (f : dbfun) (cl : clause),
  is_negcl_dbfun f cl /\ check_int_arith_dbfun c f = true ->
    implies (eval_int_arith c) (eval_clause cl).
Proof.
  unfold check_int_arith; unfold is_negcl_dbfun in *.
  intros; apply check_int_arith_valid; destruct H.
  unfold check_int_arith_dbfun in H0; unfold check_int_arith.
  destruct c; try tauto.

  now rewrite <- (H i), <- (H i0), <- (H i1).
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

Theorem eval_int_arith_sol_valid :
    forall arith theta,
      (check_int_arith_sol arith theta = true) -> eval_int_arith arith theta.
Proof.
  intros arith theta; unfold check_int_arith_sol, eval_int_arith; destruct arith;
    now rewrite Z_eqb_iff_eq.
Qed.

Definition ArithSolCheck := mkSolCheck ArithConstraint check_int_arith_sol eval_int_arith_sol_valid.