Require Import ZArith.
Require Import Bool.
Require Import assign.
Require Import domain.
Require Import range.
Require Import range_properties.
Require Import constraint.
Require Import Psatz.
Require Import ZArith.Zwf.
Require ZArith.Wf_Z.
Require Recdef.

Local Open Scope nat_scope.

(* Really should add some stuff regarding
 * non-negative variables. *)
Record task : Type := mkTask {
  duration : iterm ;
  resource : iterm ;
  svar : iterm 
}.

Record cumul : Type := mkCumul {
  tasks : list task ;
  limit : iterm
}.

Definition eval_start (t : task) (theta : valuation) :=
  eval_iterm t.(svar) theta.
Definition eval_end (t : task) (theta : valuation) :=
  Z.add (eval_iterm t.(svar) theta) (eval_iterm t.(duration) theta).

Definition task_at_time (t : task) (time : Z) (theta : valuation) : Z :=
  let tstart := eval_start t theta in
  let tend := eval_end t theta in
  if Z.leb tstart time && Z.ltb time tend then
    eval_iterm t.(resource) theta
  else
    0%Z.

Fixpoint eval_usage (ts : list task) (time : Z) (theta : valuation) : Z :=
  match ts with
  | nil => 0%Z
  | cons t ts' =>
      Z.add (task_at_time t time theta) (eval_usage ts' time theta)
  end.

Definition eval_cumul (c : cumul) (theta : valuation) :=
  forall (time : Z), Z.le (eval_usage c.(tasks) time theta) (eval_iterm c.(limit) theta).

Function span_usage (ts : list task) (start : Z) (sz : Z) (theta : valuation) { wf (Zwf 0) sz }  :=
  if Z.leb sz 0 then
    0%Z
  else
    let sz' := Z.pred sz in
    Z.add (eval_usage ts (start+sz') theta) (span_usage ts start sz' theta).
  intros.
  unfold Zwf; rewrite Z.leb_gt in teq; split; omega.
  apply Zwf_well_founded.
Defined.

Lemma span_usage_neg : forall ts start sz theta,
                         Z.le sz 0 -> span_usage ts start sz theta = 0%Z.
Proof.
  intros ts start sz theta Hsz; rewrite span_usage_equation.
  ifelim; try trivial.
  rewrite Z.leb_gt in H0; omega.
Qed.

Lemma span_usage_1 :
  forall ts theta k,
    (forall t, Z.le (eval_usage ts t theta) k) ->
    forall start sz,
     Z.le 0 sz ->
     Z.le (span_usage ts start sz theta) (Z.mul k sz).
Proof.
  intros ts theta k He start.
  apply natlike_ind.
  rewrite span_usage_equation; simpl; omega.

  intros x Hlt Husage.
  rewrite span_usage_equation.
  eqelim (Z.leb (Z.succ x) 0).
  rewrite Z.leb_le in H0; omega.
  rewrite Z.mul_succ_r.
  rewrite Z.add_comm.
  apply Z.add_le_mono.
  now rewrite Z.pred_succ.
  apply He.
Qed.

Theorem  span_usage_lim :
  forall (c : cumul) (start : Z) (sz : Z) (theta : valuation),
    eval_cumul c theta ->
    Z.le 0 sz ->
      Z.le (span_usage c.(tasks) start sz theta) ((eval_iterm c.(limit) theta) * sz).
Proof.
  intros c start sz theta.
  unfold eval_cumul; intro He.
  apply span_usage_1.
  exact He.
Qed.

Definition span_usageZ (ts : list task) (lb ub : Z) (theta : valuation) :=
  if Z.leb lb ub then
    span_usage ts lb (Z.sub ub lb) theta 
  else 0%Z.

Theorem span_usageZ_lim :
  forall (c : cumul) (lb ub : Z) (theta : valuation),
    Zle lb ub -> eval_cumul c theta ->
      Z.le (span_usageZ c.(tasks) lb ub theta) (Z.mul (eval_iterm c.(limit) theta) (Z.sub ub lb)).
Proof.
  intros.
    unfold span_usageZ.
    rewrite <- Z.leb_le in H; rewrite H.
    rewrite Z.leb_le in H.
    apply span_usage_lim; try assumption.
    omega.
Qed.

Lemma span_usage_nil : forall start sz theta, span_usage nil start sz theta = 0%Z.
Proof.
  intros.
  destruct (Z_le_dec 0 sz) as [Hl | Hg].
  generalize sz Hl; apply natlike_ind.

  + rewrite span_usage_equation.
    trivial.
  + intros x Hx Hind.
    rewrite span_usage_equation.
    eqelim (Z.leb (Z.succ x) 0); try trivial.
    rewrite Z.pred_succ.
    rewrite Hind.
    unfold eval_usage; trivial.
  + apply span_usage_neg; rewrite Z.nle_gt in Hg; omega.
Qed.

Lemma eval_usage_1 :
  forall t ts k theta, eval_usage (cons t ts) k theta = Z.add (eval_usage (cons t nil) k theta) (eval_usage ts k theta).
Proof.
  intros t ts k theta; generalize t; induction ts.  
  unfold eval_usage; intros; omega.
  intro t'. unfold eval_usage; fold eval_usage.
  specialize (IHts t'); unfold eval_usage in IHts; fold eval_usage in IHts.
  omega.
Qed.

Theorem span_usage_split : forall (t : task) (ts : list task) (start : Z) (sz : Z) (theta : valuation),
  Z.le 0 sz ->
  span_usage (cons t ts) start sz theta =
    Z.add (span_usage (cons t nil) start sz theta) (span_usage ts start sz theta).
Proof.
  intros. generalize sz H; apply natlike_ind.
    repeat (rewrite span_usage_neg; try omega).

    intros x Hle Hind.
    rewrite span_usage_equation; rewrite Z.pred_succ.
    symmetry; rewrite span_usage_equation; rewrite Z.add_comm; rewrite span_usage_equation; rewrite Z.pred_succ.
    eqelim (Z.leb (Z.succ x) 0).
      rewrite Z.leb_le in H1; omega.

    assert (H' := eval_usage_1 t ts (Z.add start x) theta).
    rewrite H'.
    omega.
Qed.
 
Function task_usage (t : task) (start : Z) (sz : Z) (theta : valuation) { wf (Zwf 0) sz } :=
  if Z.leb sz 0 then
    0%Z
  else
    let sz' := Z.pred sz in
    Z.add (task_at_time t (Z.add start sz') theta) (task_usage t start sz' theta).
  intros _ _ sz _ Hsz.
  rewrite Z.leb_gt in Hsz; unfold Zwf; intuition.
  apply Zwf_well_founded.
Defined.

Lemma task_usage_neg : forall t start sz theta,
                         Z.le sz 0 -> task_usage t start sz theta = 0%Z.
Proof.
  intros; rewrite task_usage_equation.
  ifelim; try trivial.
  rewrite Z.leb_gt in H1; omega.
Qed.

Theorem task_usage_eq_span : forall (t : task) (start : Z) (sz : Z) (theta : valuation),
  task_usage t start sz theta = span_usage (cons t nil) start sz theta.
Proof.
  intros t start sz theta.
  destruct (Z_le_dec 0 sz) as [Hl | Hg].
  generalize sz Hl; apply natlike_ind.
  rewrite task_usage_equation, span_usage_equation; trivial.

  intros x Hx Hind.
  rewrite task_usage_equation, span_usage_equation.
  eqelim (Z.leb (Z.succ x) 0); try trivial.

  rewrite Z.pred_succ; rewrite <- Hind.
  unfold eval_usage; omega.

  rewrite task_usage_neg, span_usage_neg; omega.
Qed.

Definition in_span (t : task) (time : Z) (theta : valuation) :=
  Zle (eval_start t theta) time /\ Zlt time (eval_end t theta).

Theorem task_in_span : forall (t : task) (time : Z) (theta : valuation),
  in_span t time theta ->
      task_at_time t time theta = (eval_iterm t.(resource) theta).
Proof.
  intros; destruct H as [Hs He].
  unfold in_span, task_at_time.
  assert (Z.leb (eval_start t theta) time
    && Z.ltb time (eval_end t theta) = true) as Ht.
    apply andb_true_iff; rewrite Z.leb_le; rewrite Z.ltb_lt.
    omega.
  destruct andb.
    trivial.
    discriminate.
Qed.

Theorem task_duration_usage : forall (t : task) (sz : Z) (theta : valuation),
  Z.le 0 sz ->
  Z.le sz (eval_iterm t.(duration) theta) ->
    task_usage t (eval_start t theta) sz theta = Z.mul (eval_iterm t.(resource) theta) sz.
Proof.
  intros t sz theta Hl.
    apply natlike_ind with (P := fun x => (Z.le x (eval_iterm (duration t) theta) ->
                                           (task_usage t (eval_start t theta) x theta) =
                                          (Z.mul (eval_iterm (resource t) theta) x))).
    intros.
    rewrite task_usage_equation; simpl.
    now rewrite <- Zmult_0_r_reverse.

    intros x Hx Hind Hle.
    specialize (Hind (Zle_succ_le _ _ Hle)).
    rewrite task_usage_equation; rewrite Z.pred_succ.
    eqelim (Z.leb (Z.succ x) 0); trivial.
    apply Z.leb_le in H0; omega.

    rewrite Hind.
    rewrite Z.mul_succ_r.
    rewrite Z.add_comm.
    apply Zplus_eq_compat; try trivial.
    unfold task_at_time, eval_start, eval_end.
    ifelim; tsimpl; intuition; omega.
    exact Hl.
Qed.

Theorem task_usage_split :
  forall (t : task) (lb : Z) (sz sz' : Z) (theta : valuation),
  Z.le 0 sz -> Z.le 0 sz' ->
  Z.add (task_usage t lb sz theta)
    (task_usage t (Z.add lb sz) sz' theta)
  = task_usage t lb (Z.add sz sz') theta.
Proof.
  intros t lb sz sz' theta Hsz Hsz'; generalize sz' Hsz'.
  apply natlike_ind.
  rewrite <- Zplus_0_r_reverse.
  rewrite Z.add_comm; rewrite task_usage_neg; omega.
  (*
  rewrite task_usage_neg at 2; try omega.
  rewrite Zplus_0_l.
  rewrite <- Zplus_0_l.
  trivial.
*)

  intros x Hx Hind.
  rewrite Z.add_comm; rewrite task_usage_equation; symmetry; rewrite task_usage_equation; rewrite Z.pred_succ; ifelim;
(*   rewrite task_usage_equation; symmetry; rewrite task_usage_equation; rewrite Z.pred_succ; ifelim; *)
    try (trivial || (rewrite Z.leb_le in H1 || rewrite Z.leb_le in H0) ; omega).
  assert (Z.add lb (Z.pred (Z.add sz (Z.succ x))) = Z.add (Z.add lb sz) x) as Hp1.
    omega.
  rewrite Hp1.
  assert (Z.add (Z.add (task_at_time t (Z.add (Z.add lb sz) x) theta) (task_usage t (Z.add lb sz) x theta))
                (task_usage t lb sz theta) =
          Z.add (Z.add (task_usage t lb sz theta) (task_usage t (Z.add lb sz) x theta))
                (task_at_time t (Z.add (Z.add lb sz) x) theta)) as Hp2.
    omega.
  rewrite Hp2.
  rewrite Hind.
  symmetry; rewrite Z.add_comm; apply Zplus_eq_compat; try trivial.
  f_equal; omega.
Qed.

Definition task_usageZ (t : task) (lb ub : Z) (theta : valuation) :=
  if Z.leb lb ub then
    task_usage t lb (Z.sub ub lb) theta
  else
    0%Z.

Theorem task_usageZ_eq :
  forall (t : task) (lb : Z) (sz : Z) (theta : valuation),
    task_usage t lb sz theta = 
    task_usageZ t lb (Z.add lb sz) theta.
Proof.
  intros. unfold task_usageZ.
  destruct (Z_le_dec 0 sz).
  ifelim; tsimpl.
  f_equal; omega.

  ifelim; tsimpl.
  rewrite Z.nle_gt in n.
  apply task_usage_neg; omega.
Qed.

Lemma task_usageZ_nonneg :
  forall t lb ub theta,
    Z.le 0 (eval_iterm t.(resource) theta) -> Z.le 0 (task_usageZ t lb ub theta).
Proof.
  intros t lb ub theta Hn.
  unfold task_usageZ; ifelim; tsimpl.
  remember (Z.sub ub lb) as sz.
  assert (Z.le 0 sz). omega.
  generalize sz H; apply natlike_ind.
  rewrite task_usage_equation; tsimpl.
  intros x Hx Hind; rewrite task_usage_equation; ifelim; tsimpl.
  rewrite Z.pred_succ.
  unfold task_at_time; tsimpl.
Qed.

Theorem task_usageZ_split :
  forall (t : task) (lb mid ub : Z) (theta : valuation),
    Zle lb mid -> Zle mid ub ->
    Z.add (task_usageZ t lb mid theta) (task_usageZ t mid ub theta)
      = task_usageZ t lb ub theta.
Proof.
  intros.
  unfold task_usageZ; ifelim; tsimpl; try omega.
  assert (Z.sub ub lb = (Z.add (Z.sub mid lb) (Z.sub ub mid))) as Hsplit. omega.
  remember (Z.sub mid lb) as sz.
  remember (Z.sub ub mid) as sz'.
  assert (mid = Z.add lb sz) as Hm. omega.
  rewrite Hm.
  rewrite Hsplit.
  apply task_usage_split; try omega.
Qed.  
     
Definition task_bracketed (t : task) (lb ub : Z) (theta : valuation) :=
  Zle lb (eval_start t theta)
    /\ Zle (eval_end t theta) ub.

Lemma Zle_plus_trans_r : forall x y z, Z.le 0 z -> Z.le x y -> Z.le x (Z.add y z). 
Proof. intros; omega. Qed.
Lemma Zle_plus_trans_l : forall x y z, Z.le 0 z -> Z.le x y -> Z.le x (Z.add z y).
Proof. intros; omega. Qed.

Theorem task_bracketed_usageZ :
  forall (t : task) (lb ub : Z) (theta : valuation),
    Z.le 0 (eval_iterm t.(resource) theta) ->
    Z.le 0 (eval_iterm t.(duration) theta) ->
    task_bracketed t lb ub theta ->
      Z.le (Z.mul (eval_iterm t.(resource) theta) (eval_iterm t.(duration) theta)) (task_usageZ t lb ub theta).
Proof.
  unfold task_bracketed; intros t lb ub theta Hr Hd H.
  destruct H as [Hs He].
  rewrite <- task_usageZ_split with (mid := (eval_start t theta)).
  apply Zle_plus_trans_l.
  apply task_usageZ_nonneg; assumption.
  rewrite <- task_usageZ_split with (mid := eval_end t theta).
  apply Zle_plus_trans_r.
  apply task_usageZ_nonneg; assumption.
  unfold task_usageZ.
  ifelim; try (tsimpl; omega).
  rewrite task_duration_usage.
  apply Z.mul_le_mono_nonneg_l; try assumption.
  unfold eval_end, eval_start; simpl; omega.
  tsimpl.
  rewrite Z.leb_le in H0; unfold eval_end, eval_start; tsimpl.
  rewrite Z.leb_gt in H0; unfold eval_end, eval_start in H0; tsimpl.
  unfold eval_start, eval_end; omega.
  assumption.
  assumption.
  unfold eval_start, eval_end in *; omega.
Qed.
  
Fixpoint span_usage_transp (ts : list task) (start : Z) (sz : Z) (theta : valuation) :=
  match ts with
  | nil => 0%Z
  | cons t ts' => Z.add (task_usage t start sz theta) (span_usage_transp ts' start sz theta)
  end.

Theorem span_usage_eq_transp : forall (ts : list task) (start : Z) (sz : Z) (theta : valuation),
  span_usage ts start sz theta = span_usage_transp ts start sz theta.
Proof.
  intros; generalize sz; clear sz; induction ts; intro sz.
    destruct (Z_le_dec 0 sz) as [Hl | Hg]; try (tsimpl ; trivial).
    generalize sz Hl; apply natlike_ind.
    + unfold span_usage_transp; rewrite span_usage_equation; tsimpl.
    + intros x Hx Hind.
      rewrite span_usage_equation; tsimpl; rewrite Z.pred_succ.
      assumption.
    + unfold span_usage_transp; rewrite span_usage_equation; tsimpl.
    + destruct (Z_le_dec 0 sz) as [Hl | Hg]; try tsimpl.
      generalize sz Hl; apply natlike_ind.
      rewrite span_usage_equation; unfold span_usage_transp; fold span_usage_transp; tsimpl.
      rewrite <- IHts.
      rewrite task_usage_neg, span_usage_neg; try (tsimpl || omega).

      intros x Hx Hind.
      rewrite span_usage_equation; unfold span_usage_transp; fold span_usage_transp; tsimpl; rewrite Z.pred_succ.
      rewrite <- IHts.
      symmetry; rewrite Zplus_comm; rewrite span_usage_equation; tsimpl; rewrite Z.pred_succ.
      rewrite task_usage_equation; tsimpl; rewrite Z.pred_succ.
      rewrite Hind.
      rewrite IHts.
      omega.

      rewrite Z.nle_gt in Hg.
      rewrite span_usage_equation; unfold span_usage_transp; fold span_usage_transp; tsimpl.
      rewrite task_usage_neg; try tsimpl; rewrite <- IHts; rewrite span_usage_neg; try (tsimpl || omega).
Qed.

Definition dom_lb d :=
  match range_of_dom d with
    | (Bounded l, _) => Some l
    | (_, _) => None
  end.
Lemma dom_lb_ok : forall d k, dom_lb d = Some k -> forall k', sat_dom d k' -> Z.le k k'.
Proof.
  intros d k Hd k'; destruct d as [db h]; destruct db as [l u].
  unfold sat_dom, sat_dbound, sat_lb; unfold dom_lb in Hd; destruct l; tsimpl.
Qed.

Definition term_lb t ds := dom_lb (term_dom ds t).
Lemma term_lb_ok : forall t ds k, term_lb t ds = Some k -> forall theta, eval_domset ds theta -> Z.le k (eval_iterm t theta).
Proof.
  intros t ds k Ht theta Hds.
  apply dom_lb_ok with (d := (term_dom ds t)); tsimpl.
  apply term_dom_valid; tsimpl.
Qed.

Definition dom_ub d :=
  match range_of_dom d with
    | (_, Bounded u) => Some u
    | (_, _) => None
  end.
Lemma dom_ub_ok : forall d k, dom_ub d = Some k -> forall k', sat_dom d k' -> Z.le k' k.
Proof.
  intros d k Hd k'; destruct d as [db h]; destruct db as [l u].
  unfold sat_dom, sat_dbound, sat_ub; unfold dom_ub in Hd; destruct u; tsimpl.
Qed.

Definition term_ub t ds := dom_ub (term_dom ds t).
Lemma term_ub_ok : forall t ds k, term_ub t ds = Some k -> forall theta, eval_domset ds theta -> Z.le (eval_iterm t theta) k.
Proof.
  intros t ds k Ht theta Hds.
  apply dom_ub_ok with (d := (term_dom ds t)); tsimpl.
  apply term_dom_valid; tsimpl.
Qed.

(* Latest start time of a task *)
Definition task_lst (t : task) (ds : domset) := term_ub t.(svar) ds.
Lemma task_lst_spec :
  forall t ds theta k, task_lst t ds = Some k ->
         eval_domset ds theta -> Z.le (eval_start t theta) k.
Proof.
  intros t ds theta k; unfold task_lst.
  intros Hub Hds; apply term_ub_ok with (ds := ds); assumption.
Qed.

Definition task_eet (t : task) (ds : domset) :=
  match term_lb t.(svar) ds, term_lb t.(duration) ds with
    | Some s, Some d => Some (Z.add s d)
    | _, _ => None
  end.
Lemma task_eet_spec :
  forall t ds theta k, task_eet t ds = Some k ->
                       eval_domset ds theta -> Z.le k (eval_end t theta).
  
Proof.
  intros t ds theta k; unfold task_eet, eval_end; intros He Hds.
  eqelim (term_lb (svar t) ds); eqelim (term_lb (duration t) ds); tsimpl.
  apply Zplus_le_compat; apply term_lb_ok with (ds := ds); assumption.
Qed.

(*
  (* Check whether the ~cl -> [| s[t] >= lb |] /\ [| s[t]+d[t] <= ub |]. *)
Definition domset_bracketed (t : task) (lb ub : Z) (ds : domset) :=
  match term_lb t.(svar) ds, task_eet t ds with
    | Some s, Some e => Z.le lb s /\ Z.le e ub
    | _, _ => False
  end.

  (*
  db_contained (fst (term_dom ds t.(svar)))
    lb (Zminus ub (Z_of_nat t.(duration))).
  *)

Definition domset_bracketedb (t : task) (lb ub : Z) (ds : domset) :=
  match task_lst t ds, task_eet t ds with
    | Some s, Some e => andb (Z.leb lb s) (Z.leb e ub)
    | _, _ => false
  end.
                
  (*
  db_containedb (fst (var_dom ds t.(svar)))
    lb (Zminus ub (Z_of_nat t.(duration))).
*)

Theorem domset_bracketed_valid :
  forall (t : task) (lb ub : Z) (ds : domset) (theta : valuation),
    eval_domset ds theta ->
        domset_bracketed t lb ub ds -> task_bracketed t lb ub theta.
Proof.
  unfold domset_bracketed, task_bracketed; intros.
  eqelim (task_lst t ds); eqelim (task_eet t ds); tsimpl.
  apply Z.le_trans with (m := z); try assumption.
  apply task_lst_spec.
  unfold eval_start, eval_end.
  apply db_contained_impl_inbounds with
    (k := eval_ivar t.(svar) theta) in H0.
  split.
    omega.

    rewrite Zle_plus_swap.
    destruct H0 as [_ Hub];
    exact Hub.

    apply eval_domset_vardom with (x := (svar t)) in H; unfold eval_dom, sat_dom in H; tauto.
Qed.
Theorem domset_bracketedb_iff : forall (t : task) (lb ub : Z) (ds : domset),
  domset_bracketedb t lb ub ds = true <-> domset_bracketed t lb ub ds.
Proof.
  unfold domset_bracketed, domset_bracketedb; intros.
  rewrite db_containedb_iff_contained. tauto.
Qed.
  
Fixpoint domset_usage (ts : list task) (ds : domset) (lb ub : Z) :=
  match ts with
  | nil => O
  | cons t ts' =>
    if domset_bracketedb t lb ub ds then
      mult t.(resource) t.(duration) + (domset_usage ts' ds lb ub)
    else
      domset_usage ts' ds lb ub
  end.
  
Theorem domset_usage_le_span_usage :
  forall (ts : list task) (ds : domset) (lb ub : Z) (theta : valuation),
    eval_domset ds theta -> Z.le lb ub ->
        domset_usage ts ds lb ub <= span_usageZ ts lb ub theta.
Proof.
  intros.
  unfold span_usageZ.
  destruct Z_le_dec.
  (* assert (Zle 0 (ub - lb)). omega. *)
  rewrite span_usage_eq_transp.
  induction ts.
    unfold domset_usage, span_usage_transp; omega.

    unfold domset_usage, span_usage_transp;
      fold domset_usage; fold span_usage_transp.
    assert (domset_bracketedb a lb ub ds = true <-> domset_bracketed a lb ub ds) as Hbrak_iff.
      apply domset_bracketedb_iff.
    destruct domset_bracketedb.
      assert (domset_bracketed a lb ub ds) as Hbrak. rewrite <- Hbrak_iff; trivial.
    clear Hbrak_iff.
    apply plus_le_compat.
    assert (task_bracketed a lb ub theta).
      apply domset_bracketed_valid with (ds := ds).
      exact H. exact Hbrak.
    rewrite task_usageZ_eq.
    rewrite inj_Zabs_nat.
    rewrite Zabs_eq.
    rewrite Zplus_minus.
    apply task_bracketed_usageZ. exact H1. omega.
    exact IHts.
    rewrite plus_comm; apply le_plus_trans.
    exact IHts.
    omega.
Qed.
*)

(* ~cl -> task t covers time. *)
Definition domset_compulsory (t : task) (time : Z) (ds : domset) :=
  match task_lst t ds, task_eet t ds with
  | Some s, Some e => Z.le s time /\ Z.lt time e
  | _, _ => False
(*
  | (Unbounded, Bounded _) => False
  | (Bounded _, Unbounded) => False
  | (Bounded lb, Bounded ub) =>
    Zlt time (lb + (Z_of_nat t.(duration))) /\ Zle ub time
*)
  end.

(* ~cl -> task t covers time. *)
(*
Definition domset_compulsoryb (t : task) (time : Z) (ds : domset) :=
  match (fst (var_dom ds t.(svar))) with
  | (Unbounded, Unbounded) => false
  | (Unbounded, Bounded _) => false
  | (Bounded _, Unbounded) => false
  | (Bounded lb, Bounded ub) =>
    Z.ltb time (lb + (Z_of_nat t.(duration))) && Z.leb ub time
  end.
*)
Definition domset_compulsoryb (t : task) (time : Z) (ds : domset) :=
  match task_lst t ds, task_eet t ds with
      | Some s, Some e => andb (Z.leb s time) (Z.ltb time e)
      | _, _ => false
  end.
    
Theorem domset_compulsoryb_true_iff : forall (t : task) (time : Z) (ds : domset),
  domset_compulsoryb t time ds = true <-> domset_compulsory t time ds.
Proof.
  unfold domset_compulsoryb, domset_compulsory; intros t time ds; eqelim (task_lst t ds); eqelim (task_eet t ds); tsimpl.
Qed.

(*
Theorem satdb_domset_domset : forall (ds : domset) (ds : domset) (x : ivar) (k : Z),
  is_domset_domset_db ds cl ->
    (sat_dbound (fst (dom_from_domset ds x)) k <-> sat_dbound (db_from_dom x cl) k).
Proof.
  intros cl ds x k. intro; unfold is_domset_domset_db in H.
  rewrite H. tauto.
Qed.
*)

(*
Lemma db_from_dom_valid : forall ds x theta,
   eval_domset ds theta -> sat_dbound (fst (var_dom ds x)) (eval_ivar x theta).
Proof. intros; apply eval_domset_vardom with (x := x) in H; unfold eval_dom, sat_dom in H; tauto. Qed.
*)

Theorem domset_compulsory_valid : forall (t : task) (time : Z) (ds : domset) (theta: valuation),
  domset_compulsory t time ds -> eval_domset ds theta ->
    Zle (eval_start t theta) time /\ Zlt time (eval_end t theta).
Proof.
  unfold domset_compulsory; intros t time ds theta Hb Hcl;
    eqelim (task_lst t ds); eqelim (task_eet t ds); tsimpl.
  apply Z.le_trans with (m := z); [apply task_lst_spec with (ds := ds) | assumption]; assumption.
  apply Z.lt_le_trans with (m := z0).
    assumption.
    apply task_eet_spec with (ds := ds); assumption.
Qed.

Theorem domset_compulsory_task_usage : forall (t : task) (time : Z) (ds : domset) (k : Z) (theta : valuation),
  domset_compulsory t time ds -> eval_domset ds theta ->
  term_lb t.(resource) ds = Some k -> Z.le k (task_at_time t time theta).
Proof.
  intros t time ds k theta Hb Hds Hlb.
  apply Z.le_trans with (m := (eval_iterm (resource t) theta)).
  apply term_lb_ok with (ds := ds); assumption.
  unfold task_at_time; tsimpl.
  apply domset_compulsory_valid with (theta := theta) in Hb.
  intuition; omega.
  assumption.
Qed.
  
Fixpoint domset_compulsory_usage' (ts : list task) (time : Z) (ds : domset) (acc : Z) :=
  match ts with
  | nil => Some acc
  | cons t ts' =>
    if domset_compulsoryb t time ds then
      match term_lb t.(resource) ds with
        | Some r => domset_compulsory_usage' ts' time ds (Z.add acc r)
        | None => None
      end
    else
      domset_compulsory_usage' ts' time ds acc
  end.

Definition resource_nonneg ts ds := forall theta, eval_domset ds theta -> forall t, List.In t ts -> Z.le 0 (eval_iterm t.(resource) theta).

Fixpoint resource_nonnegb ts ds :=
  match ts with
    | nil => true
    | cons t ts' =>
      match term_lb t.(resource) ds with
        | Some k => if Z.leb 0 k then resource_nonnegb ts' ds else false
        | None => false
      end
  end.
Lemma resource_nonneg_tl : forall a ts ds, resource_nonneg (cons a ts) ds -> resource_nonneg ts ds.
Proof.
  intros a ts ds; unfold resource_nonneg; intros; tsimpl.
  apply H; tsimpl.
  apply List.in_cons; assumption.
Qed.

Lemma resource_nonnegb_1 : forall ts ds, resource_nonnegb ts ds = true -> resource_nonneg ts ds.
Proof.
  intros ts ds; induction ts.

  unfold resource_nonnegb, resource_nonneg;  intros.
  now apply List.in_nil in H1.

  unfold resource_nonnegb, resource_nonneg; fold resource_nonnegb.
  eqelim (term_lb (resource a) ds); tsimpl.
  destruct H2.

  rewrite H2 in *; clear H2.
  apply Z.le_trans with (m := z); try assumption.
  apply term_lb_ok with (ds := ds); assumption.
  
  specialize IHts; unfold resource_nonneg in IHts.
  apply IHts; assumption.
Qed.

Lemma domset_compulsory_usage_1 :
  forall ts time ds theta acc k,
    resource_nonnegb ts ds = true ->
    domset_compulsory_usage' ts time ds acc = Some k ->
    eval_domset ds theta -> Z.le k (Z.add acc (eval_usage ts time theta)).
Proof.
  intros ts time ds theta acc k Hn.
  apply resource_nonnegb_1 in Hn.
  generalize acc k; clear acc k; induction ts; intros acc k.
  unfold domset_compulsory_usage', eval_usage; tsimpl.

  unfold domset_compulsory_usage', eval_usage; fold domset_compulsory_usage'; fold eval_usage.
  ifelim; eqelim (term_lb (resource a) ds); tsimpl.
  specialize (IHts (resource_nonneg_tl _ _ _ Hn) _ _ H H2).
  apply domset_compulsoryb_true_iff in H0.
  assert (Hu := domset_compulsory_task_usage a time ds z theta H0 H2 H1).
  omega.

  specialize (IHts (resource_nonneg_tl _ _ _ Hn) _ _ H H2).
  unfold resource_nonneg in Hn.
  specialize (Hn theta H2 a (List.in_eq a ts)).

  unfold task_at_time; ifelim; tsimpl.

  specialize (IHts (resource_nonneg_tl _ _ _ Hn) _ _ H H2).
  unfold resource_nonneg in Hn.
  specialize (Hn theta H2 a (List.in_eq a ts)).
  unfold task_at_time; ifelim; tsimpl.
Qed.
  

Theorem domset_compulsory_usage_bound :
  forall (ts : list task) (time : Z) (ds : domset) (k : Z)  (theta : valuation),
    resource_nonnegb ts ds = true ->
    domset_compulsory_usage' ts time ds 0%Z = Some k ->
    eval_domset ds theta -> 
      Z.le k (eval_usage ts time theta).
Proof.
  intros ts time ds k theta Hnn Heq Hds.
  rewrite Zplus_0_r_reverse, Z.add_comm.
  apply domset_compulsory_usage_1 with (ds := ds); assumption.
Qed.
  
Definition check_cumul_moment (c : cumul) (ds : domset) (t : Z) :=
  if resource_nonnegb c.(tasks) ds then
    match domset_compulsory_usage' c.(tasks) t ds 0%Z, term_ub c.(limit) ds with
      | Some k, Some c => Z.ltb c k
      | _, _ => false
    end
  else false.


Definition CumulConstraint : Constraint :=
  mkConstraint (cumul) (eval_cumul).

Theorem check_cumul_moment_valid : forall (c : cumul) (ds : domset) (t : Z) (theta : valuation),
  check_cumul_moment c ds t = true -> eval_domset ds theta -> eval_cumul c theta -> False.
Proof.
  intros c ds t theta.
  unfold check_cumul_moment.
  eqelim (resource_nonnegb (tasks c) ds); tsimpl.
  eqelim (domset_compulsory_usage' (tasks c) t ds 0); tsimpl.
  eqelim (term_ub (limit c) ds); tsimpl.
  apply domset_compulsory_usage_bound with (theta := theta) in H4; try assumption.
  apply term_ub_ok with (theta := theta) in H5; try assumption.
  unfold eval_cumul in H2.
  specialize (H2 t).
  omega.
Qed.

(* Check the beginning of the (possibly empty) compulsory region for t. *)
Definition check_cumul_tt_start (c : cumul) (ds : domset) (t : task) :=
  match task_lst t ds, task_eet t ds with
  | Some s, Some e =>
      Z.ltb s e && check_cumul_moment c ds s
  | _, _ => false
  end.
Theorem check_cumul_tt_start_valid : forall (c : cumul) (ds : domset) (t : task) (theta : valuation),
  check_cumul_tt_start c ds t = true -> eval_domset ds theta -> eval_cumul c theta -> False.
Proof.
  unfold check_cumul_tt_start. intros c ds t theta; eqelim (task_lst t ds); eqelim (task_eet t ds); tsimpl.
  apply (check_cumul_moment_valid _ _ _ _ H4 H2 H3).
Qed.
  
Fixpoint check_cumul_timetable (c : cumul) (ds : domset) (ts : list task) :=
  match ts with
  | nil => false
  | cons t ts' =>
    check_cumul_tt_start c ds t || check_cumul_timetable c ds ts'
  end.
Theorem check_cumul_timetable_valid : forall (c : cumul) (ds : domset) (ts : list task) (theta : valuation),
  check_cumul_timetable c ds ts = true ->
    eval_domset ds theta -> eval_cumul c theta -> False.
Proof.
  intros c ds ts theta; induction ts.
    unfold check_cumul_timetable, eval_cumul. intros; discriminate.

    unfold check_cumul_timetable; fold check_cumul_timetable.
    rewrite orb_true_iff; intros. destruct H.
    now apply check_cumul_tt_start_valid with (c := c) (t := a) (theta := theta) in H.

    apply IHts.
      exact H.
      exact H0.
      exact H1.
Qed.

(*
Definition check_cumul_pair (c : cumul) (tx ty : task) (ds : domset) :=
  let (lb, ub) := fst (var_dom ds tx.(svar)) in
  match lb with
  | Unbounded => false
  | Bounded lb =>
    match ub with
    | Unbounded => false
    | Bounded ub_y =>
      let ub := (Zplus ub_y (Z_of_nat (S ty.(duration)))) in
      (* Clause is trivial. *)
      (Z.leb lb ub) &&
        (Compare_dec.leb
          (S (mult c.(limit) (Zabs_nat (ub - lb))))
          (domset_usage c.(tasks) ds lb ub))
    end
  end.

Theorem check_cumul_pair_valid :
  forall (c : cumul) (tx ty : task) (ds : domset) (theta : valuation),
    check_cumul_pair c tx ty ds = true ->
      eval_domset ds theta -> eval_cumul c theta -> False.
Proof.
  unfold check_cumul_pair.
  intros c tx ty ds theta.
  (*
  assert (eval_cumul c theta \/ ~ eval_cumul c theta).
    tauto.
*)
  generalize (fst (var_dom ds (svar tx))); destruct d; destruct b, b0;
    try (intros; discriminate).
    (* generalize (Zplus z (Z_of_nat (duration ty))); intro. *)
    generalize (Zplus z0 (Z_of_nat (S (duration ty)))); intro.
    rewrite andb_true_iff.
    rewrite Z.leb_le.
    rewrite Compare_dec.leb_iff.
    intro H'. destruct H' as [Hlu Hlim].
    assert (limit c * (Zabs_nat (z1 - z)) <= domset_usage (tasks c) ds z z1) as Hlim'.
      omega.
    intros Hnotcl H.
      assert (span_usageZ (tasks c) z z1 theta <= (limit c)*(Zabs_nat (Zminus z1 z))).
        apply span_usageZ_lim.
        split.
          exact Hlu.
          exact H.
      assert (domset_usage (tasks c) ds z z1 <= span_usageZ (tasks c) z z1 theta).
        apply domset_usage_le_span_usage.
        assumption.
        omega.
        omega.
Qed.

Fixpoint check_cumul_pairs
  (c : cumul) (tx : task) (tail : list task) (ds : domset) :=
  match tail with
  | nil => false
  | cons ty tail' =>
      (check_cumul_pair c tx ty ds) || (check_cumul_pairs c tx tail' ds)
  end.
Theorem check_cumul_pairs_valid :
  forall (c : cumul) (tx : task) (tail : list task)
    (ds : domset) (theta : valuation),
    check_cumul_pairs c tx tail ds = true ->
      eval_domset ds theta -> eval_cumul c theta -> False.
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

      assumption.
      tauto.
Qed.
    
Fixpoint check_cumul_rec (c : cumul) (tail : list task) (ds : domset) :=
  match tail with
  | nil => false
  | cons t tail' =>
      (check_cumul_pairs c t c.(tasks) ds) || (check_cumul_rec c tail' ds)
  end.
Theorem check_cumul_rec_valid :
  forall (c : cumul) (tail : list task) (ds : domset) (theta : valuation),
    check_cumul_rec c tail ds = true ->
      eval_domset ds theta -> eval_cumul c theta -> False.
Proof.
  intros; induction tail.
    unfold check_cumul_rec in H; discriminate.
    unfold check_cumul_rec in H; fold check_cumul_rec in H.
    apply orb_true_iff in H.
    destruct H.
      apply check_cumul_pairs_valid with (theta := theta) in H.
      exact H. exact H0.
      tauto.
      tauto.
Qed.
  
Definition check_cumul_e (c : cumul) (ds : domset) :=
  check_cumul_rec c c.(tasks) ds.

Theorem check_cumul_e_valid : forall (c : cumul) (ds : domset),
  check_cumul_e c ds = true -> cst_is_unsat CumulConstraint c ds.
Proof.
  unfold cst_is_unsat, CumulConstraint, eval, check_cumul_e. intros.
  apply check_cumul_rec_valid with (c := c) (tail := tasks c) (theta := theta) in H; tauto.
Qed.

Definition check_cumul_tt (c : cumul) (ds : domset) :=
  (* check_cumul c cl || check_cumul_timetable c cl c.(tasks). *)
  check_cumul_timetable c ds c.(tasks) || check_cumul_e c ds.
Theorem check_cumul_tt_valid : forall (c : cumul) (ds : domset),
  check_cumul_tt c ds = true -> cst_is_unsat CumulConstraint c ds.
Proof.
  unfold check_cumul_tt; intros c ds; rewrite orb_true_iff.
  intro. destruct H.

    unfold cst_is_unsat, CumulConstraint, eval, check_cumul_timetable. intros.
    now apply check_cumul_timetable_valid with (c := c) (ts := tasks c) (theta := theta) in H.

    now apply check_cumul_e_valid.
Qed.
*)
  
Definition check_cumul_ttonly (c : cumul) (ds : domset) :=
  check_cumul_timetable c ds c.(tasks).
Theorem check_cumul_ttonly_valid : forall (c : cumul) (ds : domset),
  check_cumul_ttonly c ds = true -> cst_is_unsat CumulConstraint c ds.
Proof.
  unfold check_cumul_ttonly, cst_is_unsat, CumulConstraint; intros.
  now apply check_cumul_timetable_valid with (c := c) (ts := tasks c) (theta := theta) in H.
Qed.
(*
Definition CumulConstraint (C : Constraint) : Constraint :=
  mkConstraint (cumul) (eval_cumul) (check_cumul) (check_cumul_valid).
  *)
(*
Definition CumulCheck := mkUnsatChecker
  CumulConstraint (check_cumul_tt) (check_cumul_tt_valid).
*)

Definition CumulCheck := mkUnsatChecker
  CumulConstraint (check_cumul_ttonly) (check_cumul_ttonly_valid).

Fixpoint min_start (ts : list task) (theta : valuation) :=
  match ts with
  | nil => 0%Z
  | cons t ts' => Z.min (eval_start t theta) (min_start ts' theta)
  end.

Theorem min_start_empty : forall (ts : list task) (theta : valuation) (time : Z),
  Zlt time (min_start ts theta) -> eval_usage ts time theta = 0%Z.
Proof.
  intros ts theta time; induction ts; unfold min_start, eval_usage; fold min_start; fold eval_usage; intros; try trivial.
  assert (Zlt time (eval_start a theta)).
  assert (Zle (Z.min (eval_start a theta) (min_start ts theta)) (eval_start a theta)).
  apply Z.min_le_iff; left; apply Zle_refl.
  omega.
  rewrite IHts.
  unfold task_at_time.
  remember (Z.leb (eval_start a theta) time) as ple.
  destruct ple.
  apply eq_sym in Heqple; rewrite Z.leb_le in Heqple.
  clear IHts; omega.
  rewrite andb_false_l; omega.
  assert (Zle (Z.min (eval_start a theta) (min_start ts theta)) (min_start ts theta)).
  apply Z.min_le_iff; right; apply Zle_refl.
  omega.
Qed.

Fixpoint max_end (ts : list task) (theta : valuation) :=
  match ts with
  | nil => 0%Z
  | cons t ts' => Z.max (eval_end t theta) (max_end ts' theta)
  end.
 Theorem max_end_empty : forall (ts : list task) (theta : valuation) (time : Z),
  Zlt (max_end ts theta) time -> eval_usage ts time theta = 0%Z.
Proof.
  intros ts theta time; induction ts; unfold max_end, eval_usage; fold max_end; fold eval_usage; intros; try trivial.
  assert (Zlt (eval_end a theta) time).
  assert (Zle (eval_end a theta) (Z.max (eval_end a theta) (max_end ts theta))).
  apply Z.max_le_iff; left; apply Zle_refl.
  omega.
  rewrite IHts.
  unfold task_at_time.
  remember (Z.ltb time (eval_end a theta)) as ple.
  destruct ple.
  apply eq_sym in Heqple; rewrite Z.ltb_lt in Heqple.
  clear IHts; omega.
  rewrite andb_false_r; omega.
  assert (Zle (max_end ts theta) (Z.max (eval_end a theta) (max_end ts theta))).
  apply Z.max_le_iff; right; apply Zle_refl.
  omega.
Qed.

Function span_max (ts : list task) (start : Z) (sz : Z) (theta : valuation) { wf (Zwf 0) sz } :=
  if Z.leb sz 0 then
    0%Z
  else
    let sz' := Z.pred sz in
    Z.max (eval_usage ts (Z.add start sz') theta) (span_max ts start sz' theta).
  intros _ _ sz _ Hg.
  unfold Zwf; tsimpl; omega.
  apply Zwf_well_founded.
Qed.

Theorem span_max_ubZ : forall (ts : list task) (start : Z) (sz : Z) (k : Z) (theta : valuation),
  Z.le 0 k ->
  Z.lt k sz ->
    Z.le (eval_usage ts (Z.add start k) theta) (span_max ts start sz theta).
Proof.
  intros ts start sz k theta Hk Hlt.
  apply (natlike_ind (fun sz' => Z.lt k sz' -> Z.le (eval_usage ts (Z.add start k) theta) (span_max ts start sz' theta))) with (x := sz).
  intro; omega.

  intros x Hx Hind.
  intro Hks.
  rewrite span_max_equation; ifelim; tsimpl.
  destruct (Z_lt_dec k x) as [Hl | Hg]; tsimpl.
  specialize (Hind Hl).
  rewrite Z.pred_succ.
  rewrite <- Z.le_max_r; assumption.

  rewrite <- Z.le_max_l.
  rewrite Z.pred_succ.
  apply Z_eq_le; f_equal.
  omega.
  omega.
  assumption.
Qed.

Theorem span_max_ub_range : forall (ts : list task) (lb ub k : Z) (theta : valuation),
  Zle lb k -> Zle k ub ->
    Z.le (eval_usage ts k theta) (span_max ts lb (Z.succ (Z.sub ub lb)) theta).
Proof.
  intros.
  remember (Z.succ (Z.sub ub lb)) as sz.
  remember (Z.sub k lb) as kshift.
  assert (k = Zplus lb kshift).
  rewrite Heqkshift.
  omega.
  rewrite H1; apply span_max_ubZ.
  rewrite Heqkshift.
  omega.
  omega.
Qed.
  
Definition check_cumul_sol (c : cumul) (theta : valuation) :=
  let start := min_start (tasks c) theta in
  let last := max_end (tasks c) theta in
  andb (Z.leb 0 (eval_iterm c.(limit) theta))
  (Z.leb (span_max (tasks c) start (Z.succ (Z.sub last start)) theta) (eval_iterm c.(limit) theta)).
Theorem check_cumul_sol_valid : forall (c : cumul) (theta : valuation),
  check_cumul_sol c theta = true -> eval_cumul c theta.
Proof.
  intros c theta; destruct c;
    unfold eval_cumul; simpl; intros.
  unfold check_cumul_sol in H; simpl tasks in *; simpl limit in *.
  tsimpl.

  destruct (Z_lt_dec time (min_start tasks0 theta)) as [Hlow | Hmid].
  apply min_start_empty in Hlow; omega.

  rewrite Z.nlt_ge in Hmid.
  destruct (Z_le_dec time (max_end tasks0 theta)) as [Hmid' | Hhi]; tsimpl.

  remember (Z.sub (max_end tasks0 theta) (min_start tasks0 theta)) as sz.
  apply Z.le_trans with (m := span_max tasks0 (min_start tasks0 theta) (Z.succ sz) theta); try assumption.

  rewrite Heqsz; apply span_max_ub_range; try assumption.
  apply Z.nle_gt in Hhi.
  rewrite max_end_empty; try (assumption || omega).
Qed.

Definition CumulSolCheck := mkSolChecker CumulConstraint check_cumul_sol check_cumul_sol_valid.