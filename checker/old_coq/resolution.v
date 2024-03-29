Require Import prim.
Require Import ZArith.
Require Lists.List.
Require Import domain.
Require Import domset.

(* Actually, we can get away with doing deduplication in a preprocess;
 * soundness doesn't rely on preserving the proof semantics, just the
 * _existence_ of a correct proof. *)
Fixpoint dedup (cl : clause) := 
  match cl with
  | nil => nil
  | cons l cl' =>
      if List.existsb (lit_eqb l) cl'
      then
        (dedup cl')
      else
        cons l (dedup cl')
  end.

Definition lit_unsatb (ds : domset) (l : lit) :=
  match lit_ivar l with
  | None => false
  | Some x => dom_unsatb (dom_meet (dom_from_domset ds x) (dom_from_lit x l))
  end.

Theorem lit_unsatb_valid : forall ds l theta, lit_unsatb ds l = true ->
  eval_domset ds theta -> ~ eval_lit l theta.
Proof.
  intros ds l theta; unfold lit_unsatb.
  remember (lit_ivar l) as z; destruct z.
  rewrite dom_unsatb_unsat.
  intros; intro.
  set (k := (eval_ivar i theta)).
  assert (sat_dom (dom_from_domset ds i) k).
    unfold dom_from_domset.
    remember (map.ZMaps.find i ds) as f.
    destruct f; symmetry in Heqf.
    rewrite eval_domset_alt in H0.
    apply map.ZMaps.find_2 in Heqf.
    apply H0 in Heqf.
    now unfold eval_dom in Heqf.

    apply dom_unconstrained_is_uncon.
  
  apply (dom_from_lit_valid i) in H1.
  assert (sat_dom (dom_meet (dom_from_domset ds i) (dom_from_lit i l)) k).
  rewrite dom_meet_iff; split; [ assumption | assumption ].
  now apply H in H3.
  congruence.
Qed.

Fixpoint clauses_size (cs : list clause) :=
  match cs with
  | nil => O
  | cons cl cs' => (List.length cl) + (clauses_size cs')
  end.
    
Fixpoint clause_unsatb ds cl :=
  match cl with
  | nil => true
  | cons l cl' => andb (lit_unsatb ds l) (clause_unsatb ds cl')
  end.

Theorem clause_unsatb_valid : forall ds cl theta,
  clause_unsatb ds cl = true -> eval_domset ds theta -> ~ eval_clause cl theta.
Proof.
  induction cl.
    intros; tauto.

  unfold clause_unsatb; fold clause_unsatb;
  unfold eval_clause; fold eval_clause;
  intros.
  intro.
  rewrite Bool.andb_true_iff in H; destruct H as [Hl Hc].
  destruct H1.
    now apply (lit_unsatb_valid ds  a theta) in Hl.
    now apply IHcl in H.
Qed.

Fixpoint simplify_clause ds cl :=
  match cl with
  | nil => nil
  | cons l cl' =>
    let tl := simplify_clause ds cl' in
    if lit_unsatb ds l then
      tl
    else
      cons l tl
  end.

Lemma simplify_clause_valid : forall ds cl theta,
  eval_domset ds theta -> eval_clause cl theta -> eval_clause (simplify_clause ds cl) theta.
Proof.
  induction cl; unfold eval_clause; intros; [contradiction | fold eval_clause in *].
  unfold simplify_clause; fold simplify_clause.
  remember (lit_unsatb ds a) as ul; symmetry in Hequl; destruct ul.  
  apply lit_unsatb_valid with (theta := theta) in Hequl; try assumption.
  destruct H0 as [Ha | Hcl]; [contradiction | ].
  apply IHcl; assumption.

  unfold eval_clause; fold eval_clause.
  destruct H0 as [Ha | Hcl]; [left ; assumption | right].
  apply  IHcl; try assumption.
Qed.

Lemma simplify_clause_mono : forall ds cl,
  (List.length (simplify_clause ds cl)) <= (List.length cl).
Proof.
  intros.
  assert (forall (a : lit) x, length (a :: x) = S (length x)).
    intros; unfold length; omega.
  induction cl; unfold simplify_clause; fold simplify_clause.

    unfold length; omega.
    destruct (lit_unsatb ds a).
    rewrite H; omega.
    repeat (rewrite H); omega.
Qed.
                                    
Definition dom_tighten ds l :=
  match lit_ivar l with
  | None => Some ds
  | Some x =>
    let d := dom_meet (dom_from_domset ds x) (dom_from_lit x l) in
    if dom_unsatb d then
      None
    else
      Some (map.ZMaps.add x d ds)
  end.

Definition map2_option (A B : Type) (f : A -> B -> option A) (ox : option A) (y : B) :=
  match ox with
  | None => None
  | Some x => f x y
  end.

Theorem dom_tighten_valid_1 : forall ds ds' l theta,
  dom_tighten ds l = Some ds' ->
    eval_domset ds theta -> eval_lit l theta -> eval_domset ds' theta.
Proof.
  unfold dom_tighten.
  intros; destruct (lit_ivar l); try congruence.
  destruct (dom_unsatb (dom_meet (dom_from_domset ds i) (dom_from_lit i l))); try congruence.
    inversion H.
    rewrite eval_domset_alt; intros; simpl.

    apply map.ZMapProperties.F.add_mapsto_iff in H2.
    destruct H2 as [Hmap | Hmap] ; destruct Hmap as [Hx Hd].

    rewrite <- Hd, Hx; apply eval_dom_meet; split.
   
    apply dom_from_domset_valid.
    apply H0.
    now apply dom_from_lit_valid.
    
    rewrite eval_domset_alt in H0.
    now apply H0.

    inversion H; now rewrite <- H3.
Qed.

Theorem dom_tighten_valid_2 : forall ds l theta,
  dom_tighten ds l = None ->
    eval_domset ds theta -> ~ eval_lit l theta.
Proof.
  unfold dom_tighten.
  intros ds l theta; destruct (lit_ivar l); try congruence.
  remember (dom_unsatb (dom_meet (dom_from_domset ds i) (dom_from_lit i l))) as u;
      destruct u; simpl.

    symmetry in Hequ; rewrite dom_unsatb_unsat in Hequ.
    intros; intro.
    assert (sat_dom (dom_meet (dom_from_domset ds i) (dom_from_lit i l)) (eval_ivar i theta)).
    apply dom_meet_iff; split; [now apply dom_from_domset_valid | now apply dom_from_lit_valid].
    now apply Hequ in H2. 

    congruence.
Qed.

Fixpoint prop_clause (ds : domset) (cl : clause) :=
  match cl with
  | nil => None
  | cons l cl' =>
    if lit_unsatb ds l then
      prop_clause ds cl'
    else
      if clause_unsatb ds cl' then
        dom_tighten ds l
      else
        Some ds
  end.

Lemma prop_clause_valid_1 : forall (ds ds' : domset) (cl : clause) (theta : asg),
    (prop_clause ds cl) = Some ds' -> eval_domset ds theta -> eval_clause cl theta -> eval_domset ds' theta.
Proof.
  intros ds ds' cl theta; unfold prop_clause; induction cl; simpl;
  intros; inversion H.
  fold prop_clause in *.
  remember (lit_unsatb ds a) as ul; destruct ul; try congruence.
  destruct H1 as [Ha | Hcl].
    symmetry in Hequl; now apply lit_unsatb_valid with (theta := theta) in Hequl.

    apply IHcl in H3; try assumption.

    remember (clause_unsatb ds cl) as uc; destruct uc; try congruence.
      destruct H1 as [Ha | Hcl].

      apply dom_tighten_valid_1 with (theta := theta) in H3; assumption.
      symmetry in Hequc; apply clause_unsatb_valid with (theta := theta) in Hequc;
        [contradiction|assumption].
      
      inversion H3; now rewrite <- H4.
Qed.

Lemma prop_clause_valid_2 : forall (ds : domset) (cl : clause) (theta : asg),
    (prop_clause ds cl) = None -> eval_domset ds theta -> ~ eval_clause cl theta.
Proof.
  unfold prop_clause; intros; induction cl.
    now unfold eval_clause.

    fold prop_clause in *.
    unfold eval_clause; fold eval_clause; intro.

    remember (lit_unsatb ds a) as ua; remember (clause_unsatb ds cl) as uc.
    destruct ua; symmetry in Hequa.
    destruct H1.
      now apply lit_unsatb_valid with (theta := theta) in Hequa.

      now apply IHcl in H.

    destruct uc; symmetry in Hequc.
      destruct H1 as [Ha | Hcl];
      [now apply dom_tighten_valid_2 with (theta := theta) in H |
       now apply clause_unsatb_valid with (theta := theta) in Hequc].
    congruence.
Qed.

Fixpoint unit_prop_step (ds : domset) (cs : list clause) :=
  match cs with
  | nil => Some ds
  | cons cl cs' =>
    match unit_prop_step ds cs' with
    | None => None
    | Some ds' => prop_clause ds' cl
    end
  end.

Lemma unit_prop_step_1 : forall (cs : list clause) (theta : asg),
  eval_clauses cs theta -> forall ds, eval_domset ds theta ->
    forall ds', unit_prop_step ds cs = Some ds' -> eval_domset ds' theta.
Proof.
  induction cs;
  unfold unit_prop_step; intros; simpl in *; fold unit_prop_step in *.
    inversion H1; now rewrite <- H3.

  remember (unit_prop_step ds cs) as uds; destruct uds; try congruence.
  destruct H as [Ha Hcs].
  symmetry in Hequds.
  apply prop_clause_valid_1 with (ds := d) (cl := a); try assumption.
  apply IHcs with (ds := ds); try assumption.
Qed.

Lemma unit_prop_step_2 : forall (cs : list clause) (theta : asg),
  eval_clauses cs theta -> forall ds, unit_prop_step ds cs = None -> eval_domset ds theta -> False.
Proof.
  induction cs; unfold eval_clauses; simpl; intros; fold eval_clauses in *.
    discriminate.

    destruct H as [Ha Hcs].
    
    remember (unit_prop_step ds cs) as uds; destruct uds; try congruence; symmetry in Hequds.

    apply unit_prop_step_1 with (theta := theta) in Hequds; try assumption.
    apply (prop_clause_valid_2 d a theta); try assumption.

    apply IHcs with (theta := theta) (ds := ds); try assumption.
Qed.

Fixpoint unit_prop_rep (ds : domset) (k : nat) (cs : list clause) :=
  match k with
  | O => Some ds
  | (S k') =>
    match unit_prop_step ds cs with
    | None => None
    | Some ds' => unit_prop_rep ds' k' cs
    end
  end.
Lemma unit_prop_rep_1 : forall (cs : list clause) (ks : nat) (theta : asg),
  eval_clauses cs theta -> forall ds, eval_domset ds theta ->
    forall ds', unit_prop_rep ds ks cs = Some ds' -> eval_domset ds' theta.
Proof.
  intros cs ks theta; induction ks; unfold unit_prop_rep in *; fold unit_prop_rep in *; intros.
    inversion H1. rewrite <-H3; assumption.

    remember (unit_prop_step ds cs) as u; symmetry in Hequ; destruct u; simpl in *.
    apply IHks with (ds := d) (ds' := ds'); try assumption.
    now apply unit_prop_step_1 with (cs := cs) (ds := ds).

    discriminate.
Qed.

Lemma unit_prop_rep_2 : forall (cs : list clause) (ks : nat) (theta : asg),
  eval_clauses cs theta -> forall ds, unit_prop_rep ds ks cs = None -> eval_domset ds theta -> False.
Proof.
  intros cs ks theta; induction ks.  

  unfold unit_prop_rep; congruence.

  unfold unit_prop_rep in *; fold unit_prop_rep in *.
  intros.
  remember (unit_prop_step ds cs) as s; symmetry in Heqs; destruct s; simpl in *.
  apply IHks with (ds := d); try assumption.
  apply unit_prop_step_1 with (cs := cs) (ds := ds); try assumption.
  apply unit_prop_step_2 with (theta := theta) (cs := cs) (ds := ds); try assumption.
Qed.

Definition unit_prop (ds : domset) (cs : list clause) := unit_prop_rep ds (List.length cs) cs.
Lemma unit_prop_valid_1 : forall (cs : list clause) (theta : asg),
  eval_clauses cs theta -> forall ds, eval_domset ds theta ->
    forall ds', unit_prop ds cs = Some ds' -> eval_domset ds' theta.
Proof.
  unfold unit_prop; intros; apply unit_prop_rep_1 with (theta := theta) (cs := cs) (ks := (List.length cs)) (ds := ds); assumption.
Qed.

Lemma unit_prop_valid_2 : forall (cs : list clause) (theta : asg),
  eval_clauses cs theta -> forall ds, unit_prop ds cs = None -> eval_domset ds theta -> False.
Proof.
  unfold unit_prop; intros. apply unit_prop_rep_2 with (theta := theta) (cs := cs) (ks := (List.length cs)) (ds := ds); assumption.
Qed.
(*
Fixpoint unit_prop (ds : domset) (cs : list clause) :=
  match cs with
  | nil => Some ds
  | cons cl cs' =>
    match unit_prop ds cs' with
    | None => None
    | Some ds' =>
      match prop_clause ds' cl with
      | None => None
      | Some ds'' =>
        unit_prop ds'' cs' 
      end
    end
  end.

Lemma unit_prop_valid_1 : forall (cs : list clause) (theta : asg),
  eval_clauses cs theta -> forall ds, eval_domset ds theta ->
    forall ds', unit_prop ds cs = Some ds' -> eval_domset ds' theta.
Proof.
  induction cs;
  unfold unit_prop; intros; simpl in *; fold unit_prop in *.
    inversion H1; now rewrite <- H3.

  (*
  remember (prop_clause ds a) as pds; destruct pds; try congruence.
  remember (unit_prop t cs) as u; destruct u; try congruence.
  destruct H as [Ha Hcs].
  apply prop_clause_valid_1 with (ds := d) (cl := a); try assumption.
  symmetry in Hequ, Heqpds.
  apply IHcs with (ds := t); try assumption.
  apply prop_clause_valid_1 with (ds := ds) (cl := a); assumption.
  *)
  remember (unit_prop ds cs) as uds; destruct uds; try congruence.
  remember (prop_clause d a) as pds; destruct pds; try congruence.
  destruct H as [Ha Hcs].
  symmetry in Hequds, Heqpds.
  apply IHcs with (ds := t); try assumption.
  apply prop_clause_valid_1 with (ds := d) (cl := a); try assumption.
  apply IHcs with (ds := ds); assumption.
Qed.

Lemma unit_prop_valid_2 : forall (cs : list clause) (theta : asg),
  eval_clauses cs theta -> forall ds, unit_prop ds cs = None -> eval_domset ds theta -> False.
Proof.
  induction cs; unfold eval_clauses; simpl; intros; fold eval_clauses in *.
    discriminate.

    destruct H as [Ha Hcs].
    (*
    remember (prop_clause ds a) as pa; destruct pa; try congruence; symmetry in Heqpa.
    remember (unit_prop t cs) as ut; destruct ut; try congruence; symmetry in Hequt.
    assert (eval_domset d theta).
      apply unit_prop_valid_1 with (ds := t) (ds' := d) (cs := cs); try assumption.
      apply prop_clause_valid_1 with (ds := ds) (cl := a); try assumption.
    assert (Hp := prop_clause_valid_2 d a theta).
    tauto.
   *)
    remember (unit_prop ds cs) as uds; destruct uds; try congruence; symmetry in Hequds.
    remember (prop_clause d a) as pa; destruct pa; try congruence; symmetry in Heqpa.

    apply IHcs with (theta := theta) (ds := t); try assumption.
    assert (eval_domset d theta).
      apply unit_prop_valid_1 with (ds := ds) (ds' := d) (cs := cs); try assumption.
    apply (prop_clause_valid_1 d t a); assumption.

    apply (prop_clause_valid_2 d a theta); try assumption.
      apply unit_prop_valid_1 with (ds := ds) (ds' := d) (cs := cs); try assumption.

    apply IHcs with (theta := theta) (ds := ds); try assumption.
Qed.
*)

(*
Definition resolvable (cl : clause) (ants : list clause) := false.

Theorem resolvable_valid : forall cl ants,
  resolvable cl ants = true -> forall theta, eval_clauses ants theta -> eval_clause cl theta.
Proof.
  unfold resolvable; intros; congruence.
Qed.
*)

Fixpoint unit_prop_simpl (ds : domset)  (ants acc : list clause) (iter : bool) :=
  match ants with
  | nil => Some (ds, acc, iter)
  | cons c cs =>
    let c_simpl := simplify_clause ds c in
    match c_simpl with
    | nil => None
    | cons l nil =>
      match dom_tighten ds l with
      | None => None
      | Some ds' => unit_prop_simpl ds' cs acc true
      end
    | _ => unit_prop_simpl ds cs (cons c_simpl acc) iter
    end
  end.

(*
Lemma unit_prop_simpl_1 : forall theta ds ants acc iter,
  eval_domset ds theta -> eval_clauses ants theta -> eval_clauses acc theta ->
    forall ds' acc' iter', unit_prop_simpl ds ants acc iter = Some (ds', acc', iter') -> eval_domset ds' theta.
Proof.
  intros theta ds ants acc iter.
  induction ants; simpl in *; intros; try congruence.
 
  inversion H2; rewrite <- H4; assumption.

  destruct H0 as [Ha Hants].
  remember (simplify_clause ds a) as c_simpl.
  induction c_simpl; try congruence.
    congruence.
    symmetry in Heqc_simpl.
    destruct c_simpl; simpl in *; try congruence.
*)

Definition resolvable (cl : clause) (ants : list clause) :=
  let ds := negcl_domset cl in
  match unit_prop ds ants with
  | None => true
  | Some _ => false
  end.

Theorem resolvable_valid : forall cl ants,
  resolvable cl ants = true -> forall theta, eval_clauses ants theta -> eval_clause cl theta.
Proof.
  unfold resolvable; intros.
  remember (unit_prop (negcl_domset cl) ants) as u; symmetry in Hequ; destruct u;
    simpl in *; try congruence.
  clear H.
  remember (negcl_domset cl) as ds.
  assert (eval_domset ds theta -> False).
  apply unit_prop_valid_2 with (cs := ants); try assumption.
  apply evalclause_contra; intros.
  apply H.
  rewrite Heqds.
  now apply eval_negcl_domset.
Qed.

(* *)
