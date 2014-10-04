Require Import ZArith.
Require Import Bool.
Require Import bounds.
Require Import prim.
Require Import Program.
Require Import Recdef.
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

Definition task_at_time (t : task) (time : Z) (theta : asg) : nat :=
  let tstart := eval_start t theta in
  let tend := eval_end t theta in
  if Z_leb tstart time && Z_ltb time tend then
    t.(resource)
  else
    0%nat.

Fixpoint eval_usage (ts : list task) (time : Z) (theta : asg) : nat :=
  match ts with
  | nil => 0%nat
  | cons t ts' =>
      plus (task_at_time t time theta) (eval_usage ts' time theta)
  end.

Definition eval_cumul (c : cumul) (theta : asg) :=
  forall (time : Z), le (eval_usage c.(tasks) time theta) c.(limit).

Fixpoint span_usage (ts : list task) (start : Z) (sz : nat) (theta : asg) :=
  match sz with
  | O => 0%nat
  | S sz' =>
     plus (eval_usage ts (start+(Z_of_nat sz)-1) theta) (span_usage ts start sz' theta)
  end.

Theorem  span_usage_lim :
  forall (c : cumul) (start : Z) (sz : nat) (theta : asg),
    eval_cumul c theta ->
      le (span_usage c.(tasks) start sz theta) (c.(limit) * sz).
Proof.
  unfold eval_cumul; intros.
  induction sz.
    unfold span_usage. omega.

    unfold span_usage; fold span_usage.
    assert (le (eval_usage (tasks c) (start + (Z_of_nat (S sz)) - 1) theta) c.(limit)).
    apply H.
    rewrite <- mult_n_Sm.
    rewrite plus_comm.
    apply plus_le_compat.
    apply IHsz.
    exact H0.
Qed.

Definition span_usageZ (ts : list task) (lb ub : Z) (theta : asg) :=
  if Z_le_dec lb ub then
    span_usage ts lb (Zabs_nat (Zminus ub lb)) theta 
  else O.

Theorem span_usageZ_lim :
  forall (c : cumul) (lb ub : Z) (theta : asg),
    Zle lb ub /\ eval_cumul c theta ->
      le (span_usageZ c.(tasks) lb ub theta) (c.(limit)*(Zabs_nat (Zminus ub lb))).
Proof.
  intros.
    unfold span_usageZ.
    destruct H as [Hlu Heval].
    destruct (Z_le_dec lb ub).
    apply span_usage_lim.
    exact Heval.
    omega.
Qed.

Theorem span_usage_split : forall (t : task) (ts : list task) (start : Z) (sz : nat) (theta : asg),
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
 
Fixpoint task_usage (t : task) (start : Z) (sz : nat) (theta : asg) :=
  match sz with
  | O => 0%nat
  | S sz' =>
    plus (task_at_time t (start+(Z_of_nat sz)-1) theta) (task_usage t start sz' theta)
  end.
Theorem task_usage_eq_span : forall (t : task) (start : Z) (sz : nat) (theta : asg),
  task_usage t start sz theta = span_usage (cons t nil) start sz theta.
Proof.
  intros; induction sz.
    unfold task_usage, span_usage; trivial.

    unfold task_usage, span_usage. fold task_usage; fold span_usage.
    rewrite <- IHsz. unfold eval_usage. omega.
Qed.
Definition in_span (t : task) (time : Z) (theta : asg) :=
  Zle (eval_start t theta) time /\ Zlt time (eval_end t theta).

Theorem task_in_span : forall (t : task) (time : Z) (theta : asg),
  in_span t time theta ->
      task_at_time t time theta = t.(resource).
Proof.
  intros; destruct H as [Hs He].
  unfold in_span, task_at_time.
  assert (Z_leb (eval_start t theta) time
    && Z_ltb time (eval_end t theta) = true) as Ht.
    apply andb_true_iff; rewrite Z_leb_iff_le; rewrite Z_ltb_iff_lt.
    omega.
  destruct andb.
    trivial.
    discriminate.
Qed.
Theorem task_duration_usage : forall (t : task) (sz : nat) (theta : asg),
  sz <= t.(duration) ->
    task_usage t (eval_start t theta) sz theta = t.(resource)*sz.
Proof.
  intros; induction sz.
    unfold task_usage; omega.

    unfold task_usage; fold task_usage.
    assert (in_span t (Zminus (Zplus (eval_start t theta) (Z_of_nat (S sz))) 1) theta).
      unfold in_span, eval_start, eval_end.
      assert (Zlt (Z_of_nat sz) (Z_of_nat t.(duration))).
        omega.
      rewrite inj_S;  omega.
    rewrite task_in_span.
    rewrite IHsz.
    rewrite mult_succ_r; rewrite plus_comm; trivial.
    omega.
    exact H0.
Qed.

Theorem task_usage_split :
  forall (t : task) (lb : Z) (sz sz' : nat) (theta : asg),
  task_usage t lb sz theta +
    task_usage t (Zplus lb (Z_of_nat sz)) sz' theta
  = task_usage t lb (sz + sz') theta.
Proof.
  intros. induction sz'.
  unfold task_usage at 2 3. fold task_usage.
  repeat (rewrite <- plus_n_O); trivial.

  rewrite <- plus_n_Sm.
  unfold task_usage; fold task_usage.
  repeat (rewrite inj_S). repeat (rewrite inj_plus).
  repeat (rewrite <- Zplus_succ_r).
  repeat (rewrite <- Zplus_assoc). omega.
Qed.

Definition task_usageZ (t : task) (lb ub : Z) (theta : asg) :=
  if Z_le_dec lb ub then
    task_usage t lb (Zabs_nat (Zminus ub lb)) theta
  else
    O.

Theorem task_usageZ_eq :
  forall (t : task) (lb : Z) (sz : nat) (theta : asg),
    task_usage t lb sz theta = 
    task_usageZ t lb (Zplus lb (Z_of_nat sz)) theta.
Proof.
  intros. unfold task_usageZ.
  assert (Zle lb (lb + Z_of_nat sz)). omega.
  destruct (Z_le_dec lb (Zplus lb (Z_of_nat sz))).
  rewrite Zminus_plus.
  rewrite Zabs_nat_Z_of_nat. trivial.
  tauto.
Qed.

Theorem task_usageZ_split :
  forall (t : task) (lb mid ub : Z) (theta : asg),
    Zle lb mid /\ Zle mid ub ->
    task_usageZ t lb mid theta + task_usageZ t mid ub theta
      = task_usageZ t lb ub theta.
Proof.
  intros.
    assert (mid = (Zplus lb (Z_of_nat (Zabs_nat (Zminus mid lb))))).
    rewrite inj_Zabs_nat;
    rewrite Zabs_eq. omega. omega.
    assert (ub = (Zplus mid (Z_of_nat (Zabs_nat (Zminus ub mid))))).
    rewrite inj_Zabs_nat; rewrite Zabs_eq. omega. omega.
    assert (ub = (Zplus lb (Z_of_nat (Zabs_nat (Zminus ub lb))))).
    rewrite inj_Zabs_nat; rewrite Zabs_eq. omega. omega.
  rewrite H2 at 2; rewrite H1, H0.
  repeat (rewrite <- task_usageZ_eq).
  repeat (rewrite inj_Zabs_nat).
  repeat (rewrite Zabs_eq).
  repeat (rewrite Zplus_minus).
  rewrite H0 at 2.
  assert (Zabs_nat (ub - lb) = (Zabs_nat (mid - lb)) + (Zabs_nat (ub - mid))).
  omega.
  rewrite H3.
  apply task_usage_split.
  omega.
  omega.
Qed.
  
Definition task_bracketed (t : task) (lb ub : Z) (theta : asg) :=
  Zle lb (eval_start t theta)
    /\ Zle (eval_end t theta) ub.

Theorem task_bracketed_usageZ :
  forall (t : task) (lb ub : Z) (theta : asg),
    task_bracketed t lb ub theta ->
      mult t.(resource) t.(duration) <= task_usageZ t lb ub theta.
Proof.
  unfold task_bracketed; intros.
  destruct H as [Hs He].
  unfold eval_end in He.
  rewrite <- task_usageZ_split with (mid := (eval_start t theta)).
  rewrite plus_comm.
  apply le_plus_trans.
  rewrite <- task_usageZ_split with (mid := (eval_end t theta)).
  apply le_plus_trans.
  unfold eval_end.
  assert (eval_ivar (svar t) theta = eval_start t theta) as Hstart.
    unfold eval_start; trivial.
  rewrite Hstart.
  rewrite <- task_usageZ_eq.
  rewrite task_duration_usage.
  omega.
  omega.
  unfold eval_start, eval_end.
  omega.
  unfold eval_start in *.
  omega.
Qed.
  
Fixpoint span_usage_transp (ts : list task) (start : Z) (sz : nat) (theta : asg) :=
  match ts with
  | nil => 0%nat
  | cons t ts' => plus (task_usage t start sz theta) (span_usage_transp ts' start sz theta)
  end.

Theorem span_usage_eq_transp : forall (ts : list task) (start : Z) (sz : nat) (theta : asg),
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

(* Check whether the ~cl -> [| s[t] >= lb |] /\ [| s[t]+d[t] <= ub |]. *)
Definition negcl_bracketed (t : task) (lb ub : Z) (cl : clause) :=
  db_contained (db_from_negclause t.(svar) cl)
    lb (Zminus ub (Z_of_nat t.(duration))).

Definition negcl_bracketedb (t : task) (lb ub : Z) (cl : clause) :=
  db_containedb (db_from_negclause t.(svar) cl)
    lb (Zminus ub (Z_of_nat t.(duration))).

Theorem negcl_bracketed_valid :
  forall (t : task) (lb ub : Z) (cl : clause) (theta : asg),
    ~ eval_clause cl theta ->
        negcl_bracketed t lb ub cl -> task_bracketed t lb ub theta.
Proof.
  unfold negcl_bracketed, task_bracketed; intros.
  unfold eval_start, eval_end.
  apply db_contained_impl_inbounds with
    (k := eval_ivar t.(svar) theta) in H0.
  split.
    omega.

    rewrite Zle_plus_swap.
    destruct H0 as [_ Hub];
    exact Hub.

    apply db_from_negclause_valid; exact H.
Qed.
Theorem negcl_bracketedb_iff : forall (t : task) (lb ub : Z) (cl : clause),
  negcl_bracketedb t lb ub cl = true <-> negcl_bracketed t lb ub cl.
Proof.
  unfold negcl_bracketed, negcl_bracketedb; intros.
  rewrite db_containedb_iff_contained. tauto.
Qed.
  
Fixpoint negcl_usage (ts : list task) (cl : clause) (lb ub : Z) :=
  match ts with
  | nil => O
  | cons t ts' =>
    if negcl_bracketedb t lb ub cl then
      mult t.(resource) t.(duration) + (negcl_usage ts' cl lb ub)
    else
      negcl_usage ts' cl lb ub
  end.
  
Theorem negcl_usage_le_span_usage :
  forall (ts : list task) (cl : clause) (lb ub : Z) (theta : asg),
    ~ eval_clause cl theta /\ Zle lb ub ->
        negcl_usage ts cl lb ub <= span_usageZ ts lb ub theta.
Proof.
  intros.
  unfold span_usageZ.
  destruct H as [H Hlt].
  destruct Z_le_dec.
  (* assert (Zle 0 (ub - lb)). omega. *)
  rewrite span_usage_eq_transp.
  induction ts.
    unfold negcl_usage, span_usage_transp; omega.

    unfold negcl_usage, span_usage_transp;
      fold negcl_usage; fold span_usage_transp.
    assert (negcl_bracketedb a lb ub cl = true <-> negcl_bracketed a lb ub cl) as Hbrak_iff.
      apply negcl_bracketedb_iff.
    destruct negcl_bracketedb.
      assert (negcl_bracketed a lb ub cl) as Hbrak. rewrite <- Hbrak_iff; trivial.
    clear Hbrak_iff.
    apply plus_le_compat.
    assert (task_bracketed a lb ub theta).
      apply negcl_bracketed_valid with (cl := cl).
      exact H. exact Hbrak.
    rewrite task_usageZ_eq.
    rewrite inj_Zabs_nat.
    rewrite Zabs_eq.
    rewrite Zplus_minus.
    apply task_bracketed_usageZ. exact H0. omega.
    exact IHts.
    rewrite plus_comm; apply le_plus_trans.
    exact IHts.
    omega.
Qed.

(*
Definition check_cumul (c : cumul) (cl : clause) : bool := false.
*)
Definition check_cumul_pair (c : cumul) (tx ty : task) (cl : clause) :=
  match fst (db_from_negclause tx.(svar) cl) with
  | Unbounded => false
  | Bounded lb =>
    match snd (db_from_negclause ty.(svar) cl) with
    | Unbounded => false
    | Bounded ub_y =>
      let ub := (Zplus ub_y (Z_of_nat (S ty.(duration)))) in
      (* Clause is trivial. *)
      (Z_leb lb ub) &&
        (Compare_dec.leb
          (S (mult c.(limit) (Zabs_nat (ub - lb))))
          (negcl_usage c.(tasks) cl lb ub))
    end
  end.
Theorem check_cumul_pair_true_impl_negcl :
  forall (c : cumul) (tx ty : task) (cl : clause) (theta : asg),
    check_cumul_pair c tx ty cl = true ->
      ~ eval_clause cl theta -> ~ eval_cumul c theta.
Proof.
  unfold check_cumul_pair.
  intros c tx ty cl theta.
  assert (eval_cumul c theta \/ ~ eval_cumul c theta).
    tauto.
  generalize (fst (db_from_negclause (svar tx) cl)).
  generalize (snd (db_from_negclause (svar ty) cl)).
  intros b b0; destruct b, b0.
    intros; discriminate. 
    intros; discriminate.
    intros; discriminate.
    (* generalize (Zplus z (Z_of_nat (duration ty))); intro. *)
    generalize (Zplus z (Z_of_nat (S (duration ty)))); intro.
    rewrite andb_true_iff.
    rewrite Z_leb_iff_le.
    rewrite Compare_dec.leb_iff.
    intro H'. destruct H' as [Hlu Hlim].
    assert (limit c * (Zabs_nat (z1 - z0)) <= negcl_usage (tasks c) cl z0 z1) as Hlim'.
      omega.
    intro Hnotcl.
    destruct H.
      assert (Hbound := H).
      assert (span_usageZ (tasks c) z0 z1 theta <= (limit c)*(Zabs_nat (Zminus z1 z0))).
        apply span_usageZ_lim.
        split.
          exact Hlu.
          exact H.
      assert (negcl_usage (tasks c) cl z0 z1 <= span_usageZ (tasks c) z0 z1 theta).
        apply negcl_usage_le_span_usage.
        split.
          exact Hnotcl.
          exact Hlu.
      omega.
      exact H.
Qed.

Theorem check_cumul_pair_valid :
  forall (c : cumul) (tx ty : task) (cl : clause) (theta : asg),
    check_cumul_pair c tx ty cl = true ->
      eval_cumul c theta -> eval_clause cl theta.
Proof.
  intros.
  assert (eval_clause cl theta \/ ~ eval_clause cl theta).
    tauto.
  destruct H1.
    exact H1.
    apply check_cumul_pair_true_impl_negcl with
      (theta := theta) in H.
    tauto.

    exact H1.
Qed.

Fixpoint check_cumul_pairs
  (c : cumul) (tx : task) (tail : list task) (cl : clause) :=
  match tail with
  | nil => false
  | cons ty tail' =>
      (check_cumul_pair c tx ty cl) || (check_cumul_pairs c tx tail' cl)
  end.
Theorem check_cumul_pairs_valid :
  forall (c : cumul) (tx : task) (tail : list task)
    (cl : clause) (theta : asg),
    check_cumul_pairs c tx tail cl = true ->
      eval_cumul c theta -> eval_clause cl theta.
Proof.
  intros; induction tail.
    unfold check_cumul_pairs in H.
    discriminate.

    unfold check_cumul_pairs in H; fold check_cumul_pairs in H.
    apply orb_true_iff in H.
    destruct H.
      apply check_cumul_pair_valid with (theta := theta) in H.
      exact H.
      exact H0.

      apply IHtail in H.
      exact H.
Qed.
    
Fixpoint check_cumul_rec (c : cumul) (tail : list task) (cl : clause) :=
  match tail with
  | nil => false
  | cons t tail' =>
      (check_cumul_pairs c t c.(tasks) cl) || (check_cumul_rec c tail' cl)
  end.
Theorem check_cumul_rec_valid :
  forall (c : cumul) (tail : list task) (cl : clause) (theta : asg),
    check_cumul_rec c tail cl = true ->
      eval_cumul c theta -> eval_clause cl theta.
Proof.
  intros; induction tail.
    unfold check_cumul_rec in H; discriminate.
    unfold check_cumul_rec in H; fold check_cumul_rec in H.
    apply orb_true_iff in H.
    destruct H.
      apply check_cumul_pairs_valid with (theta := theta) in H.
      exact H. exact H0.

      apply IHtail in H. exact H.
Qed.

  
Definition check_cumul (c : cumul) (cl : clause) :=
  check_cumul_rec c c.(tasks) cl.

Theorem check_cumul_valid : forall (c : cumul) (cl : clause),
  check_cumul c cl = true -> implies (eval_cumul c) (eval_clause cl).
Proof.
  unfold implies, check_cumul. intros.
  apply check_cumul_rec_valid with (c := c) (tail := tasks c).
  exact H. exact H0.
Qed.

Definition CumulConstraint (C : Constraint) : Constraint :=
  mkConstraint (cumul) (eval_cumul) (check_cumul) (check_cumul_valid).
