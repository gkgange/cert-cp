Require Import ZArith.
Require Import assign.
Require Import lit.
Require Import domain.
Require Import range.
Require Import constraint.
Require map.

Local Open Scope Z_scope.
Definition domset_with_lit (ds : domset) (l : lit) :=
  match ds with
  | None => None
  | Some s =>
    match l with
    | Pos CTrue => Some s
    | Neg CTrue => None
    | Pos (ILeq x k) => apply_vardom ds x (dom_le k)
    | Neg (ILeq x k) => apply_vardom ds x (dom_ge (Z.succ k))
    | Pos (IEq x k) => apply_vardom ds x (dom_const k)                                    
    | Neg (IEq x k) => apply_vardom ds x (dom_neq k)
    end
  end.

Lemma domset_with_lit_iff : forall ds l theta,
  eval_domset (domset_with_lit ds l) theta <-> eval_domset ds theta /\ eval_lit l theta.                     
Proof.
  intros; unfold domset_with_lit; split; intros;
  destruct ds; try contradiction.

  destruct l; destruct v;
    try match goal with
    | [ H : eval_domset (apply_vardom ?S ?X ?D) _ |- _ ] => 
      (let H2 := fresh in assert (H2 := H); apply apply_vardom_2l in H; apply apply_vardom_2r with (x := X) (d := D) in H2)
    end; split; dom_simpl; try assumption;
    unfold eval_dom, sat_dom, range.sat_dbound, eval_lit, eval_vprop in *; tsimpl.

  apply Z_le_le_eq; assumption.
  rewrite H0 in H1; assert (Hm := zset.mem_k_addk zset.empty z); contradiction.
  contradiction.

  destruct H as [He Hl].
  destruct l; destruct v; try apply apply_vardom_1; try assumption;
  unfold eval_lit, eval_vprop in *.

  now apply dom_le_spec.
  now apply dom_const_spec.
  apply dom_ge_spec; omega.
  now apply dom_neq_spec.
  tauto.
  destruct H; assumption.
Qed.

Fixpoint domset_with_prod (ds : domset) (ps : prod) :=
  match ps with
  | nil => ds
  | cons p ps' => domset_with_prod (domset_with_lit ds p) ps'
  end.

(*
Definition domset_with_prodP ps := forall ds theta,
  eval_domset (domset_with_prod ds ps) theta <-> eval_domset ds theta /\ eval_prod ps theta.
*)
                                     
Lemma domset_with_prod_iff : forall ps ds theta,
  eval_domset (domset_with_prod ds ps) theta <-> eval_domset ds theta /\ eval_prod ps theta.
Proof.
  intros ps; induction ps.

  intros ds theta; unfold domset_with_prod, eval_prod; tauto.

  unfold domset_with_prod, eval_prod; fold domset_with_prod; fold eval_prod.
  intros ds theta.
  rewrite IHps.
  rewrite domset_with_lit_iff.
  tauto.
Qed.

Definition domset_of_prod (ps : prod) := domset_with_prod domset_empty ps.
Lemma domset_of_prod_iff : forall ps theta, eval_domset (domset_of_prod ps) theta <-> eval_prod ps theta.
Proof.
  intros; unfold domset_of_prod; rewrite domset_with_prod_iff.
  split; intros H; [destruct H ; assumption | split ; [ apply eval_domset_empty | assumption] ].
Qed.

Definition ClauseCst := mkConstraint clause eval_clause.

Fixpoint check_clause_unsat cl ds :=
  match cl with
  | nil => true
  | cons l cl' =>
    if lit_unsatb ds l then check_clause_unsat cl' ds else false
  end.

Lemma check_clause_unsat_valid : forall cl ds, check_clause_unsat cl ds = true -> cst_is_unsat ClauseCst cl ds.
Proof.
  intros cl ds; unfold ClauseCst, cst_is_unsat, eval; induction cl.

  tsimpl. 

  unfold check_clause_unsat, eval_clause; fold check_clause_unsat; fold eval_clause; ifelim.
  apply lit_unsatb_unsat in H0; unfold lit_unsat in H0.
  tsimpl.
  destruct H2; [apply H0 with (theta := theta) | apply IHcl with (theta := theta) ]; tauto.
  congruence.
Qed.

Definition ClauseCheckUnsat := mkUnsatChecker ClauseCst check_clause_unsat check_clause_unsat_valid.

Lemma evalb_clause_sol : forall cl sol, evalb_clause cl sol = true -> eval_clause cl sol.
Proof. intros; apply evalb_clause_iff; exact H. Qed.
Definition ClauseSolCheck := mkSolChecker ClauseCst evalb_clause evalb_clause_sol.
(*
Lemma domset_with_prod_iff : forall ds p theta, 
  eval_domset (domset_with_prod ds p) theta <-> eval_domset ds theta /\ eval_prod p theta.
*)

(*
Lemma domain_of_prod_iff : forall theta conj,
  eval_prod conj theta <-> eval_domset (domset_of_prod conj) theta.
Proof. (* *) Qed.
*)
