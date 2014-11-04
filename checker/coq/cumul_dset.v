(* Implementation of cumulative checkers using
 * cached domains. *)
Require Import ZArith.
Require Import Bool.
Require Import bounds.
Require Import prim.
Require Import domain.
Require Import domset.
Require Import cumulative.

Definition dset_compulsoryb (t : task) (time : Z) (f : dbfun) :=
  match (f t.(svar)) with
  | (Unbounded, Unbounded) => false
  | (Unbounded, Bounded _) => false
  | (Bounded _, Unbounded) => false
  | (Bounded lb, Bounded ub) =>
    Z_ltb time (lb + (Z_of_nat t.(duration))) && Z_leb ub time
  end.
    
Theorem dset_compulsoryb_eq : forall (t : task) (time : Z) (cl : clause) (f: dbfun),
  is_negcl_dbfun f cl ->
    dset_compulsoryb t time f = negcl_compulsoryb t time cl.
Proof.
  unfold is_negcl_dbfun, dset_compulsoryb, negcl_compulsoryb; intros.
  assert (db_from_negclause (svar t) cl = (f (svar t))).
    symmetry; apply H with (x := svar t).
  repeat (rewrite H0). tauto.
Qed.

Fixpoint dset_compulsory_usage' (ts : list task) (time : Z) (f : dbfun) :=
  match ts with
  | nil => O
  | cons t ts' =>
    if dset_compulsoryb t time f then
      plus t.(resource) (dset_compulsory_usage' ts' time f)
    else
      dset_compulsory_usage' ts' time f
  end.

Definition dset_compulsory_usage (c : cumul) (time : Z) (f : dbfun) :=
  dset_compulsory_usage' c.(tasks) time f.

Theorem dset_compulsory_usage'_eq : forall (ts : list task) (time : Z) (cl : clause) (f : dbfun),
  is_negcl_dbfun f cl ->
    (dset_compulsory_usage' ts time f = negcl_compulsory_usage' ts time cl).
Proof.
  intros.
  induction ts; unfold dset_compulsory_usage', negcl_compulsory_usage';
    fold dset_compulsory_usage'; fold negcl_compulsory_usage'.
    trivial.

    apply dset_compulsoryb_eq with (t := a) (time := time) in H.
    rewrite H, IHts; congruence.
Qed.

Theorem dset_compulsory_usage_eq : forall (c : cumul) (time : Z) (cl : clause) (f : dbfun),
  is_negcl_dbfun f cl ->
    (dset_compulsory_usage c time f = negcl_compulsory_usage c time cl).
Proof.
  unfold dset_compulsory_usage, negcl_compulsory_usage; intros.
  apply dset_compulsory_usage'_eq with (ts := (tasks c)) (time := time) in H; now apply H.
Qed.

Definition dset_check_cumul_moment (c : cumul) (f : dbfun) (t : Z) :=
  negb (Compare_dec.leb (dset_compulsory_usage c t f) c.(limit)).

Theorem dset_check_cumul_moment_eq : forall (c : cumul) (cl : clause) (f : dbfun) (t : Z),
  is_negcl_dbfun f cl ->
  dset_check_cumul_moment c f t = check_cumul_moment c cl t.
Proof.
  intros c cl dset t; intro.
  unfold dset_check_cumul_moment, check_cumul_moment.
  apply dset_compulsory_usage_eq with (c := c) (time := t) in H.
  now rewrite H.
Qed.

(* Check the beginning of the (possibly empty) compulsory region for t. *)
Definition dset_check_cumul_tt_start (c : cumul) (f : dbfun) (t : task) :=
  match (f t.(svar)) with
  | (Bounded lb, Bounded ub) =>
      Z_ltb ub (lb + (Z_of_nat t.(duration))) && dset_check_cumul_moment c f ub
  | _ => false
  end.
Theorem dset_check_cumul_tt_start_eq : forall (c : cumul) (cl : clause) (f : dbfun) (t : task),
  is_negcl_dbfun f cl ->
  dset_check_cumul_tt_start c f t = check_cumul_tt_start c cl t.
Proof.
  intros c cl f t H.
  assert (H' := H); unfold is_negcl_dbfun in H'.
  assert (db_from_negclause (svar t) cl = (f (svar t))) as Heq.
    symmetry; apply H'.
  unfold dset_check_cumul_tt_start, check_cumul_tt_start.
  rewrite Heq.
  destruct (f (svar t)); destruct b, b0; simpl; try discriminate; try tauto.
  now rewrite dset_check_cumul_moment_eq with (t := z0) (c := c) (cl := cl).
Qed.    
 
Fixpoint dset_check_cumul_timetable (c : cumul) (f : dbfun) (ts : list task) :=
  match ts with
  | nil => false
  | cons t ts' =>
    dset_check_cumul_tt_start c f t || dset_check_cumul_timetable c f ts'
  end.

Theorem dset_check_cumul_timetable_eq : forall (c : cumul) (cl : clause) (f : dbfun) (ts : list task),
  is_negcl_dbfun f cl ->
    dset_check_cumul_timetable c f ts = check_cumul_timetable c cl ts.
Proof.
  intros; induction ts;
    unfold dset_check_cumul_timetable, check_cumul_timetable; fold dset_check_cumul_timetable; fold check_cumul_timetable;
      try tauto.
    assert (H' := H). apply dset_check_cumul_tt_start_eq with (c := c) (t := a) in H'.
    now rewrite H', IHts.
Qed.

Definition dset_check_cumul_tt (c : cumul) (f : dbfun) :=
  dset_check_cumul_timetable c f c.(tasks).
(*
Definition dset_check_cumul_tt (c : cumul) (cl : clause) :=
  dset_check_cumul_timetable c (negcl_domset cl) c.(tasks).
  *)
Theorem dset_check_cumul_tt_eq : forall (c : cumul) (f : dbfun) (cl : clause),
  is_negcl_dbfun f cl -> dset_check_cumul_tt c f = check_cumul_ttonly c cl.
Proof.
  unfold dset_check_cumul_tt, check_cumul_ttonly; intros.
  apply dset_check_cumul_timetable_eq with (c := c) (ts := tasks c) in H.
  now rewrite H.
Qed.

Theorem dset_check_cumul_tt_valid : forall (c : cumul) (f : dbfun) (cl : clause),
  is_negcl_dbfun f cl /\ dset_check_cumul_tt c f = true -> implies (eval_cumul c) (eval_clause cl).
Proof.
  intros; apply check_cumul_ttonly_valid.
  destruct H; rewrite dset_check_cumul_tt_eq with (cl := cl) in H0.
  assumption. assumption.
Qed.

Definition CumulTTDSet : DomDBCheck :=
  mkDomDBCheck (cumul) (eval_cumul) (dset_check_cumul_tt) (dset_check_cumul_tt_valid).

Definition CumulTTDCheck : Constraint :=
  (CheckOfDomDBCheck (DomboundedDBCheck CumulTTDSet)). 

Definition check_cumul_tt_dbnd (c : cumul) (ds : domset) (cl : clause) :=
  (CumulTTDCheck).(check) (ds, c) cl.