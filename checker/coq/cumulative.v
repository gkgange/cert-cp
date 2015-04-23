Require Import ZArith.
Require Import Bool.
Require Import bounds.
Require Import prim.
Require Import sol.
Require Import domset.

Require Import Psatz.


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
    lia.
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
    unfold eval_usage.
    lia.
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
      lia.
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
    assert (mid = (Zplus lb (Z_of_nat (Zabs_nat (Zminus mid lb))))). lia.
    assert (ub = (Zplus mid (Z_of_nat (Zabs_nat (Zminus ub mid))))). lia.
    assert (ub = (Zplus lb (Z_of_nat (Zabs_nat (Zminus ub lb))))). lia.
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

(* ~cl -> task t covers time. *)
Definition negcl_compulsory (t : task) (time : Z) (cl : clause) :=
  match db_from_negclause t.(svar) cl with
  | (Unbounded, Unbounded) => False
  | (Unbounded, Bounded _) => False
  | (Bounded _, Unbounded) => False
  | (Bounded lb, Bounded ub) =>
    Zlt time (lb + (Z_of_nat t.(duration))) /\ Zle ub time
  end.

(* ~cl -> task t covers time. *)
Definition negcl_compulsoryb (t : task) (time : Z) (cl : clause) :=
  match db_from_negclause t.(svar) cl with
  | (Unbounded, Unbounded) => false
  | (Unbounded, Bounded _) => false
  | (Bounded _, Unbounded) => false
  | (Bounded lb, Bounded ub) =>
    Z_ltb time (lb + (Z_of_nat t.(duration))) && Z_leb ub time
  end.

Theorem negcl_compulsoryb_true_iff : forall (t : task) (time : Z) (cl : clause),
  negcl_compulsoryb t time cl = true <-> negcl_compulsory t time cl.
Proof.
  unfold negcl_compulsoryb, negcl_compulsory.
  intros.
  destruct db_from_negclause;
  destruct b, b0; simpl; split; try discriminate; try tauto.
  rewrite andb_true_iff;
    rewrite Z_ltb_iff_lt; rewrite Z_leb_iff_le; tauto.
  rewrite andb_true_iff;
    rewrite Z_ltb_iff_lt; rewrite Z_leb_iff_le; tauto.
Qed. 

(*
Theorem satdb_negcl_domset : forall (cl : clause) (ds : domset) (x : ivar) (k : Z),
  is_negcl_domset_db ds cl ->
    (sat_dbound (fst (dom_from_domset ds x)) k <-> sat_dbound (db_from_negclause x cl) k).
Proof.
  intros cl ds x k. intro; unfold is_negcl_domset_db in H.
  rewrite H. tauto.
Qed.
*)

Theorem negcl_compulsory_valid : forall (t : task) (time : Z) (cl : clause) (theta: asg),
  negcl_compulsory t time cl /\ ~ eval_clause cl theta ->
    Zle (eval_start t theta) time /\ Zlt time (eval_end t theta).
Proof.
  unfold negcl_compulsory; intros.
  destruct H as [Hb Hcl].
  assert (sat_dbound (db_from_negclause (svar t) cl) (eval_ivar t.(svar) theta)).
  apply db_from_negclause_valid; exact Hcl.
  unfold sat_dbound, sat_lb, sat_ub in H.
  destruct db_from_negclause; simpl in *.
  destruct b, b0; simpl in *.
    tauto.
    tauto.
    tauto.
    destruct Hb; unfold eval_start, eval_end; omega.
Qed.

Theorem negcl_compulsory_task_usage : forall (t : task) (time : Z) (cl : clause) (theta : asg),
  negcl_compulsory t time cl /\ ~ eval_clause cl theta ->
    task_at_time t time theta = t.(resource).
Proof.
  intros; destruct H as [Hb Hcl]; apply task_in_span.
  unfold in_span. Hint Resolve negcl_compulsory_valid. eauto.
Qed.
  
Fixpoint negcl_compulsory_usage' (ts : list task) (time : Z) (cl : clause) :=
  match ts with
  | nil => O
  | cons t ts' =>
    if negcl_compulsoryb t time cl then
      plus t.(resource) (negcl_compulsory_usage' ts' time cl)
    else
      negcl_compulsory_usage' ts' time cl
  end.

Definition negcl_compulsory_usage (c : cumul) (time : Z) (cl : clause) :=
  negcl_compulsory_usage' c.(tasks) time cl.

    
Theorem negcl_compulsory_usage_bound :
  forall (ts : list task) (time : Z) (cl : clause) (theta : asg),
    ~ eval_clause cl theta -> 
      (negcl_compulsory_usage' ts time cl) <= (eval_usage ts time theta).
Proof.
  intros; induction ts.
    unfold negcl_compulsory_usage', eval_usage; omega.
    unfold negcl_compulsory_usage', eval_usage;
      fold negcl_compulsory_usage'; fold eval_usage.
    assert (negcl_compulsoryb a time cl = true <-> negcl_compulsory a time cl).
      apply negcl_compulsoryb_true_iff.
    destruct negcl_compulsoryb.
      assert (negcl_compulsory a time cl). tauto.
      apply plus_le_compat.
        rewrite negcl_compulsory_task_usage with (cl := cl). clear H0; omega.
        tauto.
      exact IHts.
      rewrite plus_comm; apply le_plus_trans; exact IHts.
Qed.
  
Definition check_cumul_moment (c : cumul) (cl : clause) (t : Z) :=
  negb (Compare_dec.leb (negcl_compulsory_usage c t cl) c.(limit)).

Theorem check_cumul_moment_valid : forall (c : cumul) (cl : clause) (t : Z) (theta : asg),
  check_cumul_moment c cl t = true -> eval_cumul c theta -> eval_clause cl theta.
Proof.
  intros c cl t theta.
  assert (eval_clause cl theta \/ ~ eval_clause cl theta). tauto.
  destruct H.
    tauto.
  unfold check_cumul_moment. rewrite negb_true_iff.
  intros. apply leb_iff_conv in H0.
  unfold eval_cumul in H1. 
  assert (negcl_compulsory_usage c t cl <= (eval_usage (tasks c) t theta)).
    apply negcl_compulsory_usage_bound; exact H.
  assert (eval_usage (tasks c) t theta <= limit c).
    apply H1.
  assert False.
    omega.
  tauto.
Qed.

(* Check the beginning of the (possibly empty) compulsory region for t. *)
Definition check_cumul_tt_start (c : cumul) (cl : clause) (t : task) :=
  match db_from_negclause t.(svar) cl with
  | (Bounded lb, Bounded ub) =>
      Z_ltb ub (lb + (Z_of_nat t.(duration))) && check_cumul_moment c cl ub
  | _ => false
  end.
Theorem check_cumul_tt_start_valid : forall (c : cumul) (cl : clause) (t : task) (theta : asg),
  check_cumul_tt_start c cl t = true -> eval_cumul c theta -> eval_clause cl theta.
Proof.
  unfold check_cumul_tt_start. intros c cl t theta; generalize (db_from_negclause (svar t) cl).
  intro p; destruct p. destruct b, b0.
    intros; discriminate.
    intros; discriminate.
    intros; discriminate.
    rewrite andb_true_iff.
    intros; destruct H as [_ H].
    apply check_cumul_moment_valid with (c := c) (t := z0).
    exact H. exact H0.
Qed.
  
Fixpoint check_cumul_timetable (c : cumul) (cl : clause) (ts : list task) :=
  match ts with
  | nil => false
  | cons t ts' =>
    check_cumul_tt_start c cl t || check_cumul_timetable c cl ts'
  end.
Theorem check_cumul_timetable_valid : forall (c : cumul) (cl : clause) (ts : list task) (theta : asg),
  check_cumul_timetable c cl ts = true ->
    eval_cumul c theta -> eval_clause cl theta.
Proof.
  intros c cl ts theta; induction ts.
    unfold check_cumul_timetable, eval_cumul. intros; discriminate.

    unfold check_cumul_timetable; fold check_cumul_timetable.
    rewrite orb_true_iff; intros. destruct H.
    apply check_cumul_tt_start_valid with (c := c) (t := a).
    exact H.
    exact H0.

    apply IHts.
      exact H.
      exact H0.
Qed.

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
  
Definition check_cumul_e (c : cumul) (cl : clause) :=
  check_cumul_rec c c.(tasks) cl.

Theorem check_cumul_e_valid : forall (c : cumul) (cl : clause),
  check_cumul_e c cl = true -> implies (eval_cumul c) (eval_clause cl).
Proof.
  unfold implies, check_cumul_e. intros.
  apply check_cumul_rec_valid with (c := c) (tail := tasks c).
  exact H. exact H0.
Qed.

Definition check_cumul_tt (c : cumul) (cl : clause) :=
  (* check_cumul c cl || check_cumul_timetable c cl c.(tasks). *)
  check_cumul_timetable c cl c.(tasks) || check_cumul_e c cl.
Theorem check_cumul_tt_valid : forall (c : cumul) (cl : clause),
  check_cumul_tt c cl = true -> implies (eval_cumul c) (eval_clause cl).
Proof.
  unfold check_cumul_tt; intros c cl; rewrite orb_true_iff.
  intro. destruct H.

    unfold implies. intros.
    apply check_cumul_timetable_valid with (c := c) (ts := tasks c).
    exact H. exact H0.

    apply check_cumul_e_valid; exact H.
Qed.
  
Definition check_cumul_ttonly (c : cumul) (cl : clause) :=
  check_cumul_timetable c cl c.(tasks).
Theorem check_cumul_ttonly_valid : forall (c : cumul) (cl : clause),
  check_cumul_ttonly c cl = true -> implies (eval_cumul c) (eval_clause cl).
Proof.
  unfold check_cumul_ttonly, implies; intros.
  apply check_cumul_timetable_valid with (c := c) (ts := tasks c).
  assumption. assumption.
Qed.
(*
Definition CumulConstraint (C : Constraint) : Constraint :=
  mkConstraint (cumul) (eval_cumul) (check_cumul) (check_cumul_valid).
  *)
Definition CumulConstraint : Constraint :=
  mkConstraint (cumul) (eval_cumul).
Definition CumulBnd := BoundedConstraint CumulConstraint.
  
Definition CumulCheck := mkChecker
  CumulConstraint (check_cumul_tt) (check_cumul_tt_valid).
Definition CumulBndCheck := BoundedChecker CumulConstraint CumulCheck.
Definition check_cumul_bnd (c : cumul) (bs : list (ivar*Z*Z)) (cl : clause) := 
  (check CumulBnd CumulBndCheck) (bs, c) cl.

Definition CumulTTCheck := mkChecker
  CumulConstraint (check_cumul_ttonly) (check_cumul_ttonly_valid).
Definition CumulBndTTCheck := BoundedChecker CumulConstraint CumulTTCheck.

Definition check_cumul_tt_bnd (c : cumul) (bs : list (ivar*Z*Z)) (cl : clause) := 
  (check CumulBnd CumulBndTTCheck) (bs, c) cl.

Fixpoint min_start (ts : list task) (theta : asg) :=
  match ts with
  | nil => 0%Z
  | cons t ts' => Z.min (eval_start t theta) (min_start ts' theta)
  end.

Theorem min_start_empty : forall (ts : list task) (theta : asg) (time : Z),
  Zlt time (min_start ts theta) -> eval_usage ts time theta = 0.
Proof.
  intros ts theta time; induction ts; unfold min_start, eval_usage; fold min_start; fold eval_usage; intros; try trivial.
  assert (Zlt time (eval_start a theta)).
  assert (Zle (Z.min (eval_start a theta) (min_start ts theta)) (eval_start a theta)).
  apply Z.min_le_iff; left; apply Zle_refl.
  omega.
  rewrite IHts.
  unfold task_at_time.
  remember (Z_leb (eval_start a theta) time) as ple.
  destruct ple.
  apply eq_sym in Heqple; rewrite Z_leb_iff_le in Heqple.
  clear IHts; omega.
  rewrite andb_false_l; omega.
  assert (Zle (Z.min (eval_start a theta) (min_start ts theta)) (min_start ts theta)).
  apply Z.min_le_iff; right; apply Zle_refl.
  omega.
Qed.

Fixpoint max_end (ts : list task) (theta : asg) :=
  match ts with
  | nil => 0%Z
  | cons t ts' => Z.max (eval_end t theta) (max_end ts' theta)
  end.
 Theorem max_end_empty : forall (ts : list task) (theta : asg) (time : Z),
  Zlt (max_end ts theta) time -> eval_usage ts time theta = 0.
Proof.
  intros ts theta time; induction ts; unfold max_end, eval_usage; fold max_end; fold eval_usage; intros; try trivial.
  assert (Zlt (eval_end a theta) time).
  assert (Zle (eval_end a theta) (Z.max (eval_end a theta) (max_end ts theta))).
  apply Z.max_le_iff; left; apply Zle_refl.
  omega.
  rewrite IHts.
  unfold task_at_time.
  remember (Z_ltb time (eval_end a theta)) as ple.
  destruct ple.
  apply eq_sym in Heqple; rewrite Z_ltb_iff_lt in Heqple.
  clear IHts; omega.
  rewrite andb_false_r; omega.
  assert (Zle (max_end ts theta) (Z.max (eval_end a theta) (max_end ts theta))).
  apply Z.max_le_iff; right; apply Zle_refl.
  omega.
Qed.

Fixpoint span_max (ts : list task) (start : Z) (sz : nat) (theta : asg) :=
  match sz with
  | O => 0%nat
  | S sz' =>
     max (eval_usage ts (start+(Zpred (Z_of_nat sz))) theta) (span_max ts start sz' theta)
  end.

Theorem span_max_ub_nat : forall (ts : list task) (start : Z) (sz : nat) (k : nat) (theta : asg),
  lt k sz ->
    (eval_usage ts (Zplus start (Z_of_nat k)) theta) <= span_max ts start sz theta.
Proof.
  intros.
  induction sz.
  now apply lt_n_0 in H.
  remember (Zplus start (Z_of_nat k)) as tk.
  unfold span_max, eval_usage; fold span_max; fold eval_usage.
  rewrite Nat2Z.inj_succ.
  rewrite <- Zpred_succ.
  assert (lt k sz \/ k = sz). omega.
  destruct H0; fold span_max.

    
    apply IHsz in H0.
    assert (le (span_max ts start sz theta) (max (eval_usage ts (Zplus start (Z_of_nat sz)) theta) (span_max ts start sz theta))).
    apply Max.le_max_r.
    omega.

    rewrite Heqtk; rewrite H0.
    apply Max.le_max_l.
Qed.

Theorem span_max_ub_range : forall (ts : list task) (lb ub k : Z) (theta : asg),
  Zle lb k /\ Zle k ub ->
    le (eval_usage ts k theta) (span_max ts lb (S (Zabs_nat (Zminus ub lb))) theta).
Proof.
  intros.
  remember (S (Z.abs_nat (Zminus ub lb))) as sz.
  remember (Z.abs_nat (Zminus k lb)) as kshift.
  assert (k = Zplus lb (Z_of_nat kshift)).
  rewrite Heqkshift.
  rewrite Zabs2Nat.id_abs.
  rewrite Z.abs_eq; omega.
  rewrite H0; apply span_max_ub_nat.
  rewrite Heqkshift.
  rewrite Heqsz.
  rewrite <- Zabs2Nat.inj_succ.
  apply Zabs_nat_lt.
  omega.
  omega.
Qed.
  
Definition check_cumul_sol (c : cumul) (theta : asg) :=
  let start := min_start (tasks c) theta in
  let last := max_end (tasks c) theta in
  Compare_dec.leb (span_max (tasks c) start (S (Zabs_nat (Zminus last start))) theta) (limit c).
Theorem check_cumul_sol_valid : forall (c : cumul) (theta : asg),
  check_cumul_sol c theta = true -> eval_cumul c theta.
Proof.
  intros c theta; destruct c;
    unfold eval_cumul; simpl; intros.
  unfold check_cumul_sol in H; simpl tasks in *; simpl limit in *.
  assert (Hlow := min_start_empty tasks0 theta time).
  assert (Hhigh := max_end_empty tasks0 theta time).
  remember (min_start tasks0 theta) as lb.
  remember (max_end tasks0 theta) as ub.
  assert (Hrange := span_max_ub_range tasks0 lb ub time theta).
  assert (Zlt time lb \/ Zle lb time).
    omega.
  destruct H0.
    omega.

    assert (Zlt ub time \/ Zle time ub).
      omega.
    destruct H1; try omega.
    assert (Zle lb time /\ Zle time ub) as Hr.
      omega.
    apply Hrange in Hr.
    rewrite leb_iff in H.
    omega.
Qed.    

Definition CumulSolCheck := mkSolCheck CumulConstraint check_cumul_sol check_cumul_sol_valid.
