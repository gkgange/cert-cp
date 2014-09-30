Require Import ZArith.
Require Import Bool.
Require Import bounds.
Require Import prim.
Require Import Program.
Require Import Program.Wf.

Local Open Scope nat_scope.

(* Really should add some stuff regarding
 * non-negative variables. *)
Record task : Type := mkTask {
  duration : nat ;
  resource : nat ;
  svar : ivar 
}.

Record vartask : Type := mkVarTask {
  vt_dur: ivar ;
  vt_res : ivar ;
  vt_svar : ivar
}.

Record cumul : Type := mkCumul {
  tasks : list task ;
  limit : nat
}.

Definition eval_start (t : task) (theta : asg) :=
  eval_ivar t.(svar) theta.
Definition eval_end (t : task) (theta : asg) :=
  Zplus (eval_ivar t.(svar) theta) (Z_of_nat t.(duration)).

Definition task_at_time (t : task) (time : nat) (theta : asg) : nat :=
  let tstart := eval_start t theta in
  let tend := eval_end t theta in
  let ztime := Z_of_nat time in
  if Z_leb tstart ztime && Z_ltb ztime tend then
    t.(resource)
  else
    0%nat.

Fixpoint eval_usage (ts : list task) (time : nat) (theta : asg) : nat :=
  match ts with
  | nil => 0%nat
  | cons t ts' =>
      plus (task_at_time t time theta) (eval_usage ts' time theta)
  end.

Definition eval_cumul (c : cumul) (theta : asg) :=
  forall (time : nat), le (eval_usage c.(tasks) time theta) c.(limit).

Fixpoint span_usage (ts : list task) (start : nat) (sz : nat) (theta : asg) :=
  match sz with
  | O => 0%nat
  | S sz' =>
     plus (eval_usage ts (start+sz-1) theta) (span_usage ts start sz' theta)
  end.

Theorem  span_usage_lim :
  forall (c : cumul) (start : nat) (sz : nat) (theta : asg),
    eval_cumul c theta ->
      le (span_usage c.(tasks) start sz theta) (c.(limit) * sz).
Proof.
  unfold eval_cumul; intros.
  induction sz.
    unfold span_usage. omega.

    unfold span_usage; fold span_usage.
    assert (le (eval_usage (tasks c) (start + (S sz) - 1) theta) c.(limit)).
    apply H.
    rewrite <- mult_n_Sm.
    rewrite plus_comm.
    apply plus_le_compat.
    apply IHsz.
    exact H0.
Qed.

Theorem span_usage_split : forall (t : task) (ts : list task) (start sz : nat) (theta : asg),
  span_usage (cons t ts) start sz theta =
    plus (span_usage (cons t nil) start sz theta) (span_usage ts start sz theta).
Proof.
  intros. induction sz.
    unfold span_usage; omega.

    unfold span_usage ; fold span_usage.
    assert (forall (i j k l : nat), plus (plus (plus i k)  j) l = (plus (plus i j)  (plus k l))).
      intros. omega.
    rewrite <- H.
    unfold eval_usage at 1; fold eval_usage. unfold eval_usage at 2.
    rewrite IHsz. omega.
Qed.
    
Fixpoint task_usage (t : task) (start : nat) (sz : nat) (theta : asg) :=
  match sz with
  | O => 0%nat
  | S sz' =>
    plus (task_at_time t (start+sz-1) theta) (task_usage t start sz' theta)
  end.
Theorem task_usage_eq_span : forall (t : task) (start sz : nat) (theta : asg),
  task_usage t start sz theta = span_usage (cons t nil) start sz theta.
Proof.
  intros; induction sz.
    unfold task_usage, span_usage; trivial.

    unfold task_usage, span_usage. fold task_usage; fold span_usage.
    rewrite <- IHsz. unfold eval_usage. omega.
Qed.
Theorem task_in_span : forall (t : task) (time : nat) (theta : asg),
  Zle (eval_start t theta) (Z_of_nat time)
    /\ Zlt (Z_of_nat time) (eval_end t theta) ->
      task_at_time t time theta = t.(resource).
Proof.
  intros; destruct H as [Hs He].
  unfold task_at_time.
  assert (Z_leb (eval_start t theta) (Z_of_nat time)
    && Z_ltb (Z_of_nat time) (eval_end t theta) = true) as Ht.
    apply andb_true_iff; rewrite Z_leb_iff_le; rewrite Z_ltb_iff_lt.
    omega.
  destruct andb.
    trivial.
    discriminate.
Qed.
Theorem task_usage_monotone_r : forall (t : task) (start sz sz' : nat) (theta : asg),
  le sz sz' -> le (task_usage t start sz theta) (task_usage t start sz' theta).
Proof.
  intros.
  induction sz'.
    assert (sz = 0%nat) as Hsz0. omega.
    rewrite Hsz0; trivial.
    
    assert (sz = (S sz') \/ sz < S sz'). omega.
    destruct H0 as [Heq | Hlt].
      rewrite Heq. omega.

      unfold task_usage at 2;  fold task_usage.
      assert (le O (task_at_time t (start + S sz' - 1) theta)). omega.
      assert (forall (i j k : nat), i <= k -> i <= j + k). intros; omega. 
      apply H1. apply IHsz'. apply lt_n_Sm_le. exact Hlt.
Qed.
(*
Theorem task_duration_usage : forall (t : task) (start sz : nat) (theta : asg),
  (Z_ge (Z_of_nat start) (eval_ivar t.(svar) theta) /\
    (Z_of_nat (start + sz)) = (Zplus (eval_ivar t.(svar) theta) (Z_of_nat t.(duration)))) ->
      task_usage t start sz theta = sz*t.(resource).
Proof.
  intros; induction sz.
    unfold task_usage; trivial.

    unfold task_usage; fold task_usage.
*)

Fixpoint span_usage_transp (ts : list task) (start : nat) (sz : nat) (theta : asg) :=
  match ts with
  | nil => 0%nat
  | cons t ts' => plus (task_usage t start sz theta) (span_usage_transp ts' start sz theta)
  end.

Theorem span_usage_eq_transp : forall (ts : list task) (start sz : nat) (theta : asg),
  span_usage ts start sz theta = span_usage_transp ts start sz theta.
Proof.
  intros; induction ts.
    induction sz.
        unfold span_usage, span_usage_transp; trivial.

        unfold span_usage; fold span_usage.
        rewrite IHsz.
        unfold span_usage_transp.
        unfold eval_usage. omega.

    unfold span_usage_transp; fold span_usage_transp.
    rewrite <- IHts.
    rewrite span_usage_split.
    rewrite <- task_usage_eq_span.
    trivial.
Qed.

Definition task_bracketed (t : task) (start sz : nat) (theta : asg) :=
  Zle (Z_of_nat start) (eval_ivar t.(svar) theta)
    /\ Zlt (eval_end t theta) (Z_of_nat (start + sz)).

(*
Theorem task_cover_usage :
    forall (c : cumul) (t : task) (start sz : nat) (theta : asg),
  eval_cumul c theta ->
    Zle (eval_start t theta) (Z_of_nat start)
    /\ Zlt (Z_of_nat (plus start sz)) (eval_end t theta) ->
      task_usage t start sz theta = mult sz t.(resource).
Proof.
  intros; destruct H0 as [Hl Hu]; induction sz.
    unfold task_usage; omega.
    
    unfold task_usage; fold task_usage. 
    unfold task_at_time.

Theorem task_bracket_usage :
    forall (c : cumul) (t : task) (start : nat) (sz : nat) (theta : asg),
  eval_cumul c theta ->
    task_bracketed t start sz theta -> task_usage t start sz theta = mult t.(duration) t.(resource).
Proof.
  unfold task_bracketed, eval_start, eval_end; intros.
  destruct H0 as [Hl Hu].
  
  induction sz.
    unfold task_usage.
    assert (le (duration t) 0).
    apply (plus_le_reg_l (duration t) (0) (start)).
    apply inj_le_iff.
*)

(* Check whether the ~cl -> [| s[t] >= lb |] /\ [| s[t]+d[t] < ub |]. *)

(*
Fixpoint span_area (ts : list task) (cl : clause) (lb ub : Z) :=
  match ts with
  | nil => 0%Z
  | cons t ts' =>
     if containedb t cl lb ub = true then 
       t.(resource)*t.(duration) + (span_area ts' cl lb ub)
     else
       span_area ts' cl lb ub
  end.
*)

Definition check_cumul (c : cumul) (cl : clause) : bool := false.

Theorem check_cumul_valid : forall (c : cumul) (cl : clause),
  check_cumul c cl = true -> implies (eval_cumul c) (eval_clause cl).
Proof.
  unfold check_cumul. intros. discriminate.
Qed.

Definition CumulConstraint (C : Constraint) : Constraint :=
  mkConstraint (cumul) (eval_cumul) (check_cumul) (check_cumul_valid).
