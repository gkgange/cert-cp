(* Model representation *)
Require Import ZArith.
Require Import assign.
Require Import domain.
Require Import constraint.
Require linear.
Require element.
Require cumulative.
Require arith.
Require lit.
Require clause_domain.

(* Model bound *)
Definition model_bound := (ivar * (val * val))%type.

(* Closed set of constraints. *)
Inductive cst :=
  | Tauto
  | Lin : linear.LinearCon.(T) -> cst
  | LinNE : linear.LinearNE.(T) -> cst
  | Elem : element.ElemConstraint.(T) -> cst  
  | Cumul : cumulative.CumulConstraint.(T) -> cst  
  | Clause : clause_domain.ClauseCst.(T) -> cst
  | Arith : arith.ArithConstraint.(T) -> cst
  | ArithNE : arith.ArithNE.(T) -> cst
  | Conj : cst -> cst -> cst
  | Disj : cst -> cst -> cst
  | Half : lit.lit -> cst -> cst.

Definition make_linear xs k := Lin (xs, k).
Definition make_lin_ne xs k := LinNE (xs, k).
Definition make_element x y ks := Elem (element.Element x y ks).
Definition make_cumul (c : cumulative.cumul) := Cumul c.                                  
Definition make_clause (cl : lit.clause) := Clause cl.
Definition make_conj x y := Conj x y.
Definition make_disj x y := Disj x y.
Definition make_arith_eq id expr := Arith (id, expr).
Definition make_arith_ne id expr := ArithNE (id, expr).
Definition make_half r cons := Half r cons.

Definition cst_id := Z.
Definition csts := list (cst_id * cst).

Fixpoint eval_cst c (theta : valuation) := match c with
  | Tauto => True
  | Lin x => linear.LinearCon.(eval) x theta
  | LinNE x => linear.LinearNE.(eval) x theta
  | Elem x => element.ElemConstraint.(eval) x theta
  | Cumul x => cumulative.CumulConstraint.(eval) x theta
  | Clause x => clause_domain.ClauseCst.(eval) x theta
  | Arith x => arith.ArithConstraint.(eval) x theta
  | ArithNE x => arith.ArithNE.(eval) x theta
  | Conj x y => (eval_cst x theta) /\ (eval_cst y theta)
  | Disj x y => (eval_cst x theta) \/ (eval_cst y theta)
  | Half r c => (lit.eval_lit r theta) -> (eval_cst c theta)
  end.

Fixpoint check_cst_unsat c (ds : domset) := match c with
  | Tauto =>
    match ds with
      | None => true
      | _ => false
    end
  | Lin x => check_unsat linear.LinearCon linear.CheckLinearUnsat x ds
  | LinNE x => check_unsat linear.LinearNE linear.CheckLinearNeqUnsat x ds
  | Elem x => check_unsat element.ElemConstraint element.ElemCheckUnsat x ds
  | Cumul x => check_unsat cumulative.CumulConstraint cumulative.CumulCheck x ds
  | Clause x => check_unsat clause_domain.ClauseCst clause_domain.ClauseCheckUnsat x ds
  | Arith x => check_unsat arith.ArithConstraint arith.ArithCheck x ds
  | ArithNE x => check_unsat arith.ArithNE arith.ArithNECheck x ds
  | Conj x y => orb (check_cst_unsat x ds) (check_cst_unsat y ds)
  | Disj x y => andb (check_cst_unsat x ds) (check_cst_unsat y ds)
  | Half r c => andb (lit.lit_unsatb ds (lit.neglit r)) (check_cst_unsat c ds)
  end.

Lemma check_cst_unsat_valid : forall c ds,
  check_cst_unsat c ds = true -> forall theta, eval_domset ds theta -> eval_cst c theta -> False.                                
Proof.
  unfold check_cst_unsat, eval_cst; intros; induction c;
  try (destruct ds; tsimpl);
  try (apply check_unsat_valid in H; unfold cst_is_unsat in H; specialize (H theta); tauto).
  (* Remaining cases: conj, half *)
  apply Bool.orb_true_iff in H ; destruct H as [H | H]; [apply IHc1 | apply IHc2]; intuition.
  (* Now, half *)
  apply lit.lit_unsatb_unsat in H.
  apply lit.lit_valid_neglit in H.
  unfold lit.lit_valid in H; specialize (H theta H0).
  specialize (H1 H).
  now specialize (IHc H2 H1).
Qed.

Fixpoint eval_csts (cs : csts) (theta : valuation) := 
  match cs with
  | nil => True
  | cons c cs' => (eval_cst (snd c) theta) /\ (eval_csts cs' theta)
  end.

Fixpoint check_cst_sol c (sol : valuation) := match c with
  | Tauto => true
  | Lin x => check_sol linear.LinearCon linear.LinearSolCheck x sol
  | LinNE x => check_sol linear.LinearNE linear.LinearNESolCheck x sol
  | Elem x => check_sol element.ElemConstraint element.ElementSolCheck x sol
  | Cumul x => check_sol cumulative.CumulConstraint cumulative.CumulSolCheck x sol
  | Clause x => check_sol clause_domain.ClauseCst clause_domain.ClauseSolCheck x sol
  | Arith x => check_sol arith.ArithConstraint arith.ArithSolCheck x sol
  | ArithNE x => check_sol arith.ArithNE arith.ArithNESolCheck x sol
  | Conj x y => andb (check_cst_sol x sol) (check_cst_sol y sol)
  | Disj x y => orb (check_cst_sol x sol) (check_cst_sol y sol)
  | Half r c => orb (negb (lit.evalb_lit r sol)) (check_cst_sol c sol)
  end.

Lemma check_cst_sol_valid : forall c sol, check_cst_sol c sol = true -> eval_cst c sol.
Proof.
  intros c sol; unfold check_cst_sol, eval_cst; induction c; try (trivial || apply check_sol_valid). 
  + rewrite Bool.andb_true_iff; intuition.
  + rewrite Bool.orb_true_iff; intuition.
  + rewrite Bool.orb_true_iff; intuition.
    rewrite Bool.negb_true_iff in H1.
    rewrite <- lit.evalb_lit_iff in H0; congruence.
Qed.

Fixpoint check_csts_sol (cs : csts) sol := match cs with
  | nil => true
  | cons (_, c) cs' => andb (check_cst_sol c sol) (check_csts_sol cs' sol)
  end.
Lemma check_csts_sol_valid : forall cs sol, check_csts_sol cs sol = true -> eval_csts cs sol.
Proof.
  intros cs sol; induction cs.

  tsimpl.

  unfold check_csts_sol, eval_csts; fold check_csts_sol; fold eval_csts.
  destruct a; tsimpl.
  now apply check_cst_sol_valid.
Qed.
  
Definition eval_bound (b : model_bound) (theta : valuation) :=
  match b with
  | (x, (lb, ub)) => Zle lb (theta x) /\ Zle (theta x) ub
  end.
Definition evalb_bound (b : model_bound) (theta : valuation) :=
  match b with
  | (x, (lb, ub)) => andb (Z.leb lb (theta x)) (Z.leb (theta x) ub)
  end.

Lemma evalb_bound_iff : forall b theta, evalb_bound b theta = true <-> eval_bound b theta.
Proof.
  intros; unfold evalb_bound, eval_bound; destruct b; destruct p; tsimpl.
Qed.

Definition domset_with_bound (ds : domset) (b : model_bound) :=
  match b with
  | (x, (lb, ub)) => apply_vardom ds x (dom_range lb ub)
  end.
Lemma domset_with_bound_iff : forall ds b theta,
  eval_domset ds theta /\ eval_bound b theta <-> eval_domset (domset_with_bound ds b) theta.
Proof.
  intros; unfold domset_with_bound; destruct b; destruct p.
  split; intros.
    destruct H as [Hd Hb]; apply apply_vardom_1; [assumption | trivial].
    unfold eval_bound in Hb; now apply dom_range_spec.

    assert (Hp := H). apply apply_vardom_2l in H; apply apply_vardom_2r in Hp.
    split; [assumption | now apply dom_range_spec in Hp].
Qed.

Fixpoint domset_with_bounds (ds : domset) (bs : list model_bound) :=
  match bs with
  | nil => ds
  | cons b bs' =>
    match domset_with_bound ds b with
    | None => None
    | Some ds' => domset_with_bounds (Some ds') bs'
    end
  end.

Fixpoint eval_bounds bs theta :=
  match bs with
  | nil => True
  | cons b bs' => eval_bound b theta /\ eval_bounds bs' theta
  end.

Fixpoint evalb_bounds bs theta :=
  match bs with
  | nil => true
  | cons b bs' => andb (evalb_bound b theta) (evalb_bounds bs' theta)
  end.
Lemma evalb_bounds_iff : forall bs theta, evalb_bounds bs theta = true <-> eval_bounds bs theta.
Proof.
  intros; induction bs.
  tsimpl.

  tsimpl; [apply evalb_bound_iff ; assumption | apply evalb_bound_iff ; assumption ].
Qed.

Lemma domset_with_bounds_valid : forall bs ds theta,
  eval_domset ds theta -> eval_bounds bs theta -> eval_domset (domset_with_bounds ds bs) theta.                                   
Proof.
  intros bs; induction bs.

  tsimpl.
  unfold eval_bounds, domset_with_bounds; fold eval_bounds; fold domset_with_bounds.
  intros; destruct H0.
  assert (eval_domset (domset_with_bound ds a) theta).
    apply domset_with_bound_iff; tauto.
  eqelim (domset_with_bound ds a); intros.
    apply IHbs; try tauto.
    assumption.
Qed.

Definition domset_of_bounds bs := domset_with_bounds domset_empty bs.
Lemma domset_of_bounds_valid : forall bs theta, eval_bounds bs theta -> eval_domset (domset_of_bounds bs) theta.
Proof. unfold domset_of_bounds; intros; apply domset_with_bounds_valid; [apply eval_domset_empty | assumption]. Qed.

Definition model := (list model_bound * csts)%type.

Definition eval_model m theta :=
  match m with
  | (bs, cs) => eval_bounds bs theta /\ eval_csts cs theta
  end.

Definition model_unsat m := forall theta, ~ eval_model m theta.

Definition is_model_ub m obj sol := forall sol', eval_model m sol' -> (sol obj) <= (sol' obj).

Definition is_model_minimum m obj sol := eval_model m sol /\ is_model_ub m obj sol.

Definition check_model_sol m sol := andb (evalb_bounds (fst m) sol) (check_csts_sol (snd m) sol).
Lemma check_model_sol_valid : forall m sol, check_model_sol m sol = true -> eval_model m sol.
Proof.
  intros m sol; unfold check_model_sol; destruct m; tsimpl.
  now apply evalb_bounds_iff.
  now apply check_csts_sol_valid.
Qed.

