(* Implementation of cumulative checkers using
 * cached domains. *)
Require Import ZArith.
Require Import Bool.
Require Import bounds.
Require Import prim.
Require Import domset.
Require Import cumulative.

Definition dset_compulsoryb (t : task) (time : Z) (ds : domset) :=
  match fst (dom_from_domset ds t.(svar)) with
  | (Unbounded, Unbounded) => false
  | (Unbounded, Bounded _) => false
  | (Bounded _, Unbounded) => false
  | (Bounded lb, Bounded ub) =>
    Z_ltb time (lb + (Z_of_nat t.(duration))) && Z_leb ub time
  end.
    
Theorem dset_compulsoryb_eq : forall (t : task) (time : Z) (cl : clause) (dset: domset),
  is_negcl_domset_db dset cl ->
    dset_compulsoryb t time dset = negcl_compulsoryb t time cl.
Proof.
  unfold is_negcl_domset_db, dset_compulsoryb, negcl_compulsoryb; intros.
  assert (db_from_negclause (svar t) cl = fst (dom_from_domset dset (svar t))).
    apply H.
  repeat (rewrite H0). tauto.
Qed.
 Fixpoint dset_compulsory_usage' (ts : list task) (time : Z) (dset : domset) :=
  match ts with
  | nil => O
  | cons t ts' =>
    if dset_compulsoryb t time dset then
      plus t.(resource) (dset_compulsory_usage' ts' time dset)
    else
      dset_compulsory_usage' ts' time dset
  end.

Definition dset_compulsory_usage (c : cumul) (time : Z) (dset : domset) :=
  dset_compulsory_usage' c.(tasks) time dset.

Theorem dset_compulsory_usage'_eq : forall (ts : list task) (time : Z) (cl : clause) (dset : domset),
  is_negcl_domset_db dset cl ->
    (dset_compulsory_usage' ts time dset = negcl_compulsory_usage' ts time cl).
Proof.
  intros.
  induction ts; unfold dset_compulsory_usage', negcl_compulsory_usage';
    fold dset_compulsory_usage'; fold negcl_compulsory_usage'.
    trivial.

    apply dset_compulsoryb_eq with (t := a) (time := time) in H.
    rewrite H, IHts; congruence.
Qed.

Theorem dset_compulsory_usage_eq : forall (c : cumul) (time : Z) (cl : clause) (dset : domset),
  is_negcl_domset_db dset cl ->
    (dset_compulsory_usage c time dset = negcl_compulsory_usage c time cl).
Proof.
  unfold dset_compulsory_usage, negcl_compulsory_usage; intros.
  apply dset_compulsory_usage'_eq with (ts := (tasks c)) (time := time) in H; now apply H.
Qed.

Definition dset_check_cumul_moment (c : cumul) (dset : domset) (t : Z) :=
  negb (Compare_dec.leb (dset_compulsory_usage c t dset) c.(limit)).

Theorem dset_check_cumul_moment_eq : forall (c : cumul) (cl : clause) (dset : domset) (t : Z),
  is_negcl_domset_db dset cl ->
  dset_check_cumul_moment c dset t = check_cumul_moment c cl t.
Proof.
  intros c cl dset t; intro.
  unfold dset_check_cumul_moment, check_cumul_moment.
  apply dset_compulsory_usage_eq with (c := c) (time := t) in H.
  now rewrite H.
Qed.

(* Check the beginning of the (possibly empty) compulsory region for t. *)
Definition dset_check_cumul_tt_start (c : cumul) (dset : domset) (t : task) :=
  match fst (dom_from_domset dset t.(svar)) with
  | (Bounded lb, Bounded ub) =>
      Z_ltb ub (lb + (Z_of_nat t.(duration))) && dset_check_cumul_moment c dset ub
  | _ => false
  end.
Theorem dset_check_cumul_tt_start_eq : forall (c : cumul) (cl : clause) (dset : domset) (t : task),
  is_negcl_domset_db dset cl ->
  dset_check_cumul_tt_start c dset t = check_cumul_tt_start c cl t.
Proof.
  intros c cl dset t H.
  assert (H' := H); unfold is_negcl_domset_db in H'.
  assert (db_from_negclause (svar t) cl = fst (dom_from_domset dset (svar t))) as Heq.
    apply H'.
  unfold dset_check_cumul_tt_start, check_cumul_tt_start.
  rewrite Heq.
  destruct (fst (dom_from_domset dset (svar t))); destruct b, b0; simpl; try discriminate; try tauto.
  now rewrite dset_check_cumul_moment_eq with (t := z0) (c := c) (cl := cl).
Qed.    
 
Fixpoint dset_check_cumul_timetable (c : cumul) (dset : domset) (ts : list task) :=
  match ts with
  | nil => false
  | cons t ts' =>
    dset_check_cumul_tt_start c dset t || dset_check_cumul_timetable c dset ts'
  end.

Theorem dset_check_cumul_timetable_eq : forall (c : cumul) (cl : clause) (dset : domset) (ts : list task),
  is_negcl_domset_db dset cl ->
    dset_check_cumul_timetable c dset ts = check_cumul_timetable c cl ts.
Proof.
  intros; induction ts;
    unfold dset_check_cumul_timetable, check_cumul_timetable; fold dset_check_cumul_timetable; fold check_cumul_timetable;
      try tauto.
    assert (H' := H). apply dset_check_cumul_tt_start_eq with (c := c) (t := a) in H'.
    now rewrite H', IHts.
Qed.

Definition dset_check_cumul_tt (c : cumul) (cl : clause) :=
  dset_check_cumul_timetable c (negcl_domset cl) c.(tasks).
Theorem dset_check_cumul_tt_eq : forall (c : cumul) (cl : clause),
  dset_check_cumul_tt c cl = check_cumul_ttonly c cl.
Proof.
  unfold dset_check_cumul_tt, check_cumul_ttonly; intros.
  assert (is_negcl_domset_db (negcl_domset cl) cl).
    apply dom_from_domset_db.
  apply dset_check_cumul_timetable_eq with (c := c) (ts := tasks c) in H.
  now rewrite H.
Qed.

Theorem dset_check_cumul_tt_valid : forall (c : cumul) (cl : clause),
  dset_check_cumul_tt c cl = true -> implies (eval_cumul c) (eval_clause cl).
Proof.
  intros c cl; rewrite dset_check_cumul_tt_eq; apply check_cumul_ttonly_valid.
Qed.

Definition CumulTTDSet : Constraint :=
  mkConstraint (cumul) (eval_cumul) (dset_check_cumul_tt) (dset_check_cumul_tt_valid).
Definition check_cumul_tt_dbnd (c : cumul) (bs : list (ivar*Z*Z)) (cl : clause) := 
  (BoundedConstraint CumulTTDSet).(check) (bs, c) cl.