Require Import assign.
Require Import ZArith.
Require Lists.List.
Require Import domain.
Require Import lit.
Require Import clause_domain.

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

(*
Definition lit_unsatb (ds : domset) (l : lit) :=
  match lit_ivar l with
  | None => false
  | Some x => dom_unsatb (dom_meet (var_dom ds x) (dom_from_lit x l))
  end.

Theorem lit_unsatb_valid : forall ds l theta, lit_unsatb ds l = true ->
  eval_domset ds theta -> ~ eval_lit l theta.
Proof.
  intros ds l theta; unfold lit_unsatb.
  remember (lit_ivar l) as z; destruct z.
  rewrite dom_unsatb_unsat.
  intros; intro.
  set (k := (eval_ivar i theta)).
  assert (sat_dom (var_dom ds i) k).
    unfold var_dom.
    remember (map.ZMaps.find i ds) as f.
    destruct f; symmetry in Heqf.
    rewrite eval_domset_alt in H0.
    apply map.ZMaps.find_2 in Heqf.
    apply H0 in Heqf.
    now unfold eval_dom in Heqf.

    apply dom_unconstrained_is_uncon.
  
  apply (dom_from_lit_valid i) in H1.
  assert (sat_dom (dom_meet (var_dom ds i) (dom_from_lit i l)) k).
  rewrite dom_meet_iff; split; [ assumption | assumption ].
  now apply H in H3.
  congruence.
Qed.
*)

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
  clause_unsatb ds cl = true -> eval_domset ds theta -> eval_clause cl theta -> False.
Proof.
  induction cl.
    intros; tauto.

  unfold clause_unsatb; fold clause_unsatb;
  unfold eval_clause; fold eval_clause;
  intros.
  rewrite Bool.andb_true_iff in H; destruct H as [Hl Hc].
  apply lit_unsatb_unsat in Hl; unfold lit_unsatb in Hl.
  specialize (Hl theta); specialize (IHcl theta).
  tauto.
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
  apply lit_unsatb_unsat in Hequl; specialize (Hequl theta).
  destruct H0 as [Ha | Hcl]; [tauto | ].
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

(*
Definition dom_tighten ds l :=
  match lit_ivar l with
  | None => Some ds
  | Some x =>
    let d := dom_meet (var_dom ds x) (dom_from_lit x l) in
    if dom_unsatb d then
      None
    else
      Some (map.ZMaps.add x d ds)
  end.
*)

Definition map2_option (A B : Type) (f : A -> B -> option A) (ox : option A) (y : B) :=
  match ox with
  | None => None
  | Some x => f x y
  end.

(*
Theorem dom_tighten_valid_1 : forall ds ds' l theta,
  dom_tighten ds l = Some ds' ->
    eval_domset ds theta -> eval_lit l theta -> eval_domset ds' theta.
Proof.
  unfold dom_tighten.
  intros; destruct (lit_ivar l); try congruence.
  destruct (dom_unsatb (dom_meet (var_dom ds i) (dom_from_lit i l))); try congruence.
    inversion H.
    rewrite eval_domset_alt; intros; simpl.

    apply map.ZMapProperties.F.add_mapsto_iff in H2.
    destruct H2 as [Hmap | Hmap] ; destruct Hmap as [Hx Hd].

    rewrite <- Hd, Hx; apply eval_dom_meet; split.
   
    apply var_dom_valid.
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
  remember (dom_unsatb (dom_meet (var_dom ds i) (dom_from_lit i l))) as u;
      destruct u; simpl.

    symmetry in Hequ; rewrite dom_unsatb_unsat in Hequ.
    intros; intro.
    assert (sat_dom (dom_meet (var_dom ds i) (dom_from_lit i l)) (eval_ivar i theta)).
    apply dom_meet_iff; split; [now apply var_dom_valid | now apply dom_from_lit_valid].
    now apply Hequ in H2. 

    congruence.
Qed.
*)

Fixpoint prop_clause (ds : domset) (cl : clause) :=
  match cl with
  | nil => None
  | cons l cl' =>
    if lit_unsatb ds l then
      prop_clause ds cl'
    else
      if clause_unsatb ds cl' then
        domset_with_lit ds l
      else
        ds
  end.

Lemma prop_clause_valid : forall (ds : domset) (cl : clause) (theta : valuation),
    eval_domset ds theta -> eval_clause cl theta -> eval_domset (prop_clause ds cl) theta.                            
Proof.
  intros ds cl theta; induction cl.

  unfold prop_clause; tsimpl.

  unfold prop_clause, eval_clause; fold prop_clause; fold eval_clause.
  ifelim; tsimpl.

  destruct H1; [apply lit_unsatb_unsat in H0; specialize (H0 theta); tauto | tauto].
  destruct H2; [ apply domset_with_lit_iff | apply clause_unsatb_valid with (theta := theta) in H1]; tauto.
Qed.

Inductive prop_result :=
| Unit : domset -> prop_result
| Simp : clause -> prop_result
| Conflict : prop_result.

Fixpoint clause_unsat_simp ds cl :=
  match cl with
    | nil => None
    | cons l cl' =>
      if lit_unsatb ds l then
        clause_unsat_simp ds cl'
      else
        Some (cons l cl')
  end.

Lemma clause_unsat_simp1 :
  forall ds cl, clause_unsat_simp ds cl = None ->
                forall theta, eval_domset ds theta -> ~ eval_clause cl theta.
Proof.
  intros ds cl.                             
  unfold clause_unsat_simp; induction cl; fold clause_unsat_simp in *.
  intros; unfold eval_clause; intuition.

  eqelim (lit_unsatb ds a).
  apply lit_unsatb_unsat in H0.
  intros.
  unfold eval_clause; fold eval_clause; intro.
  destruct H2.
  now apply H0 in H2.
  now apply IHcl in H2.
  congruence.
Qed.  
Lemma clause_unsat_simp2 :
  forall ds cl cl', clause_unsat_simp ds cl = Some cl' ->
                    forall theta, eval_domset ds theta -> eval_clause cl theta -> eval_clause cl' theta.
Proof.
  intros ds cl.  
  induction cl.
  unfold clause_unsat_simp; unfold eval_clause; intuition.

  unfold clause_unsat_simp, eval_clause; fold clause_unsat_simp; fold eval_clause.
  intro cl'.
  eqelim (lit_unsatb ds a).
  + apply lit_unsatb_unsat in H0.
    intros.
    destruct H2.
      now apply H0 in H2.
      apply (IHcl cl'); try assumption.
  + intros. inversion H. rewrite <- H4 in *.
    unfold eval_clause; fold eval_clause.
    destruct H2; intuition.
Qed.
    
Fixpoint prop_clause_simp (ds : domset) (cl : clause) : prop_result :=
  match cl with
  | nil => Conflict
  | cons l cl' =>
    if lit_unsatb ds l then
      prop_clause_simp ds cl'
    else
      match clause_unsat_simp ds cl' with
          | None => Unit (domset_with_lit ds l)
          | Some cl'' => Simp (cons l cl'')
      end
  end.
Lemma prop_clause_Confl :
  forall ds cl, prop_clause_simp ds cl = Conflict ->
                forall theta, eval_domset ds theta -> ~ eval_clause cl theta.
Proof.
  intros ds; induction cl; unfold prop_clause_simp; fold prop_clause_simp.
  + unfold eval_clause; intuition.
  + eqelim (lit_unsatb ds a); intuition.
    apply H1 with (theta := theta); try assumption.
    unfold eval_clause in H3; fold eval_clause in H3; intuition.
    apply lit_unsatb_unsat in H0; now apply H0 in H4.
    eqelim (clause_unsat_simp ds cl); congruence.
Qed.

Lemma prop_clause_Unit :
  forall ds cl ds', prop_clause_simp ds cl = Unit ds' ->
                    forall theta, eval_domset ds theta -> eval_clause cl theta -> eval_domset ds' theta.
Proof.
  intros ds cl; induction cl; unfold prop_clause_simp; fold prop_clause_simp.
  + congruence.
  + eqelim (lit_unsatb ds a); try apply lit_unsatb_unsat in H0.
    - intros ds' Hp theta He; specialize (IHcl ds' Hp theta He).
      unfold eval_clause; fold eval_clause.
      intro H'; destruct H' as [H' | H'].
      now apply H0 in H'.
      intuition.
    - intro ds'; eqelim (clause_unsat_simp ds cl).
      congruence.
      intros Hds' theta Heds.
      inversion Hds'.
      apply clause_unsat_simp1 with (theta := theta) in H1.
      intro Hcl; unfold eval_clause in Hcl; fold eval_clause in Hcl.
      rewrite domset_with_lit_iff.
      split; [exact Heds | trivial].
      destruct Hcl; intuition.
      assumption.
Qed.

Lemma prop_clause_Simp :
  forall ds cl cl', prop_clause_simp ds cl = Simp cl' ->
                    forall theta, eval_domset ds theta -> eval_clause cl theta -> eval_clause cl' theta.
Proof.
  intros ds cl; induction cl.
  unfold eval_clause; intuition.

  unfold prop_clause_simp; fold prop_clause_simp; eqelim (lit_unsatb ds a).
  + intros cl' Hcl' theta Heds Hecl'; specialize (IHcl cl' Hcl' theta Heds).
    unfold eval_clause in Hecl'; fold eval_clause in Hecl'.
    destruct Hecl' as [H' | H'].
    apply lit_unsatb_unsat in H0; now apply H0 in H'.
    intuition.
  + intros cl'; eqelim (clause_unsat_simp ds cl); try congruence.
    intros Hs theta Heds Hec; inversion Hs.
    unfold eval_clause; fold eval_clause.
    unfold eval_clause in Hec; fold eval_clause in Hec.
    destruct Hec; [now left | right].
    apply clause_unsat_simp2 with (theta := theta) (ds := ds) (cl := cl); try intuition.
Qed.

Fixpoint unit_prop_simp_step ds cs :=
  match cs with
    | nil => Some (ds, nil)
    | cons cl cs' =>
      match prop_clause_simp ds cl with
        | Conflict => None
        | Unit ds' => unit_prop_simp_step ds' cs'
        | Simp cl' =>
          match unit_prop_simp_step ds cs' with
            | None => None
            | Some (ds', cs'') => Some (ds', cons cl' cs'')
          end
      end
  end.
Lemma unit_prop_simp_step1 :
  forall ds cs, unit_prop_simp_step ds cs = None ->
                forall theta, eval_domset ds theta -> ~ eval_clauses cs theta.
Proof.
  intros ds cs; generalize ds; clear ds; induction cs; intro ds.
  unfold unit_prop_simp_step; fold unit_prop_simp_step; congruence.
  unfold unit_prop_simp_step; fold unit_prop_simp_step.
  eqelim (prop_clause_simp ds a).
  + intros; unfold eval_clauses; fold eval_clauses; intro.
    specialize (IHcs d H theta).
    apply prop_clause_Unit with (theta := theta) in H0; try intuition.
  + eqelim (unit_prop_simp_step ds cs).
    intro; simpl.
    destruct p in H; congruence.

    intros _ theta Heds.
    specialize (IHcs ds H1 theta Heds).
    simpl; intuition.
  + intros _ theta Heds; simpl.
    apply prop_clause_Confl with (theta := theta) in H0; intuition.
Qed.

Lemma unit_prop_simp_step2a :
  forall ds cs ds' cs', unit_prop_simp_step ds cs = Some (ds', cs') ->
                        forall theta, eval_domset ds theta -> eval_clauses cs theta -> eval_domset ds' theta.
Proof.
  intros ds cs; generalize ds; clear ds; induction cs; intro ds.
  unfold unit_prop_simp_step; congruence.

  unfold unit_prop_simp_step; fold unit_prop_simp_step.
  eqelim (prop_clause_simp ds a); simpl; intros ds' cs' Hup theta Heds Heacs.
  + specialize (IHcs d ds' cs' Hup theta).
    apply prop_clause_Unit with (theta := theta) in H0; intuition.
  + eqelim (unit_prop_simp_step ds cs).
    destruct p; inversion Hup; simpl in *.
    apply prop_clause_Simp with (theta := theta) in H0; try tauto.
    destruct Heacs as [Hea Hecs]; specialize (IHcs ds d l H1 theta Heds Hecs).
    congruence.
    congruence.
  + congruence.
Qed.

 Lemma unit_prop_simp_step2b :
  forall ds cs ds' cs', unit_prop_simp_step ds cs = Some (ds', cs') ->
                        forall theta, eval_domset ds theta -> eval_clauses cs theta -> eval_clauses cs' theta.
Proof.
  intros ds cs; generalize ds; clear ds; induction cs; intro ds.
  unfold unit_prop_simp_step; congruence.

  unfold unit_prop_simp_step; fold unit_prop_simp_step.
  eqelim (prop_clause_simp ds a); simpl; intros ds' cs' Hup theta Heds Heacs.
  + specialize (IHcs d ds' cs' Hup theta).
    apply prop_clause_Unit with (theta := theta) in H0; intuition.
  + eqelim (unit_prop_simp_step ds cs).
    destruct p; inversion Hup; simpl in *.
    apply prop_clause_Simp with (theta := theta) in H0; try tauto.
    destruct Heacs as [Hea Hecs]; specialize (IHcs ds d l H1 theta Heds Hecs).
    intuition.
    intuition.
    congruence.
 + congruence.
Qed.
 
Fixpoint unit_prop_step (ds : domset) (cs : list clause) :=
  match cs with
  | nil => ds
  | cons cl cs' =>
    match unit_prop_step ds cs' with
    | None => None
    | Some ds' => prop_clause (Some ds') cl
    end
  end.

Lemma unit_prop_step_valid : forall (cs : list clause) (theta : valuation),
  eval_clauses cs theta -> forall ds, eval_domset ds theta ->
    eval_domset (unit_prop_step ds cs) theta.
Proof.
  induction cs;
  unfold unit_prop_step; intros; simpl in *; fold unit_prop_step in *.
    exact H0.

  eqelim (unit_prop_step ds cs).
  apply prop_clause_valid; try tauto; rewrite <- H2.
    apply IHcs; tauto.

  rewrite <- H2; apply IHcs; tauto.
Qed.

Fixpoint unit_prop_rep (ds : domset) (k : nat) (cs : list clause) :=
  match k with
  | O => ds
  | (S k') =>
    match unit_prop_step ds cs with
    | None => None
    | Some ds' => unit_prop_rep (Some ds') k' cs
    end
  end.
Lemma unit_prop_rep_1 : forall (cs : list clause) (ks : nat) (theta : valuation),
  eval_clauses cs theta -> forall ds, eval_domset ds theta -> eval_domset (unit_prop_rep ds ks cs) theta.
Proof.
  intros cs ks theta; induction ks; unfold unit_prop_rep in *; fold unit_prop_rep in *; intros.
    exact H0.

  eqelim (unit_prop_step ds cs); rewrite <- H2.
    apply IHks; try tauto.
    apply unit_prop_step_valid; try tauto.

    apply unit_prop_step_valid; try tauto.
Qed.

Fixpoint unit_prop_simp_rep (ds : domset) (k : nat) (cs : list clause) :=
  match k with
    | O => ds
    | (S k') =>
      match unit_prop_simp_step ds cs with
        | None => None
        | Some (ds', cs') => unit_prop_simp_rep ds' k' cs'
      end
  end.
Lemma unit_prop_srep_1 : forall (cs : list clause) (ks : nat) (theta : valuation),
  eval_clauses cs theta -> forall ds, eval_domset ds theta -> eval_domset (unit_prop_simp_rep ds ks cs) theta.
Proof.
  intros cs ks theta; generalize cs; clear cs; induction ks; intros cs Hecs ds Heds.

  unfold unit_prop_simp_rep; intuition.

  unfold unit_prop_simp_rep; fold unit_prop_simp_rep.
  eqelim (unit_prop_simp_step ds cs).
  destruct p.
  + apply IHks.
    apply unit_prop_simp_step2b with (theta := theta) in H0; intuition.
    apply unit_prop_simp_step2a with (theta := theta) in H0; intuition.
  + apply unit_prop_simp_step1 with (theta := theta) in H0; intuition.
Qed.

(*
Definition unit_prop (ds : domset) (cs : list clause) := unit_prop_rep ds (List.length cs) cs.
Lemma unit_prop_valid : forall (cs : list clause) (theta : valuation),
  eval_clauses cs theta -> forall ds, eval_domset ds theta ->
    eval_domset (unit_prop ds cs) theta.
Proof.
  unfold unit_prop; intros; apply unit_prop_rep_1 with (theta := theta) (cs := cs) (ks := (List.length cs)) (ds := ds); assumption.
Qed.
*)

Definition unit_prop (ds : domset) (cs : list clause) := unit_prop_simp_rep ds (List.length cs) cs.
Lemma unit_prop_valid : forall (cs : list clause) (theta : valuation),
  eval_clauses cs theta -> forall ds, eval_domset ds theta ->
    eval_domset (unit_prop ds cs) theta.
Proof.
  unfold unit_prop; intros; apply unit_prop_srep_1 with (theta := theta) (cs := cs) (ks := (List.length cs)) (ds := ds); assumption.
Qed.

(*
Definition resolvable (cl : clause) (ants : list clause) := false.

Theorem resolvable_valid : forall cl ants,
  resolvable cl ants = true -> forall theta, eval_clauses ants theta -> eval_clause cl theta.
Proof.
  unfold resolvable; intros; congruence.
Qed.
*)

(*
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
*)

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
  let ds := domset_of_prod (negclause cl) in
  match unit_prop ds ants with
  | None => true
  | Some _ => false
  end.

Definition resolvable_under (ds : domset) (cl : clause) (ants : list clause) :=
  let ds := domset_with_prod ds (negclause cl) in
  match unit_prop ds ants with
  | None => true
  | Some _ => false
  end.

Theorem resolvable_valid : forall cl ants,
  resolvable cl ants = true -> forall theta, eval_clauses ants theta -> eval_clause cl theta.
Proof.
  unfold resolvable; intros.
  eqelim (unit_prop (domset_of_prod (negclause cl)) ants); [congruence | trivial].
  clear H.
  apply eval_clause_notprod.
  intro.
  apply domset_of_prod_iff in H.
  apply unit_prop_valid with (cs := ants) in H.
    now rewrite H2 in H.
    assumption.
Qed.

Theorem resolvable_under_valid : forall ds cl ants,
  resolvable_under ds cl ants = true -> forall theta, eval_domset ds theta -> eval_clauses ants theta -> eval_clause cl theta.
Proof.
  unfold resolvable_under; intros.
  eqelim (unit_prop (domset_with_prod ds (negclause cl)) ants); [congruence | trivial].
  clear H.
  apply eval_clause_notprod.
  intro.
  assert (eval_domset (domset_with_prod ds (negclause cl)) theta).
    apply domset_with_prod_iff; tauto.
  apply unit_prop_valid with (cs := ants) in H2.
    now rewrite H3 in H2.
    assumption.
Qed.
