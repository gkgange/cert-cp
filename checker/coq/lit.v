(* Formulation of literals *)
Require Import ZArith.
Require Import Bool.
Require Import assign.
Require Import domain.

(* Primitive propositions. *)
Inductive vprop : Type :=
  | ILeq : ivar -> Z -> vprop
  | IEq : ivar -> Z -> vprop
  | CTrue : vprop.
     
(* A literal is either a positive
 * or negative proposition. *)
Inductive lit : Type :=
  | Pos : vprop -> lit
  | Neg : vprop -> lit.

(* Evaluate a proposition under an assignment. *)
Definition eval_vprop
  (p : vprop) (theta : valuation) : Prop :=
  match p with
  | ILeq iv k => (theta iv) <= k
  | IEq iv k => (theta iv) = k
  | CTrue => True
  end.

(* Evaluate a proposition under an assignment. *)
Definition evalb_vprop
  (p : vprop) (theta : valuation) : bool :=
  match p with
  | ILeq iv k => Z.leb (theta iv) k
  | IEq iv k => Z.eqb (theta iv) k
  | CTrue => true
  end.

Definition vprop_eqb x y :=
  match x with
  | ILeq vx kx =>
    match y with
    | ILeq vy ky => ivar_eqb vx vy && Z.eqb kx ky
    | _ => false
    end
  | IEq vx kx =>
    match y with
    | IEq vy ky => ivar_eqb vx vy && Z.eqb kx ky
    | _ => false
    end
  | CTrue =>
    match y with
    | CTrue => true
    | _ => false
    end
  end.
 
Definition lit_eqb x y :=
  match x with
  | Pos vx =>
    match y with
    | Pos vy => vprop_eqb vx vy
    | _ => false
    end
  | Neg vx =>
    match y with
    | Neg vy => vprop_eqb vx vy
    | _ => false
    end
  end.
      
Theorem evalb_vprop_iff : forall p theta, evalb_vprop p theta = true <-> eval_vprop p theta.
Proof.
  intros; unfold evalb_vprop, eval_vprop; destruct p; tsimpl; now apply Z.eqb_eq.
Qed.

Definition sat_lit
  (l : lit) (x : ivar) (k : Z) :=
  match l with
  | Pos (ILeq x' k') => x <> x' \/ k <= k'
  | Neg (ILeq x' k') => x <> x' \/ k' < k
  | Pos (IEq x' k') => x <> x' \/ k = k'
  | Neg (IEq x' k') => x <> x' \/ k <> k'
  | _ => True
  end.
  
(* Evaluate a literal under an assignment. *)
Definition eval_lit
  (l : lit) (theta : valuation) : Prop :=
  match l with
  | Pos vp => eval_vprop vp theta
  | Neg vp => ~(eval_vprop vp theta)
  end.
Definition evalb_lit (l : lit) (theta : valuation) : bool :=
  match l with
  | Pos vp => evalb_vprop vp theta
  | Neg vp => negb (evalb_vprop vp theta)
  end.
Theorem evalb_lit_iff : forall l theta, evalb_lit l theta = true <-> eval_lit l theta.
Proof.
  unfold evalb_lit, eval_lit; intros; destruct l; simpl; rewrite <- evalb_vprop_iff;
  [tauto | now rewrite negb_true_iff, not_true_iff_false].
Qed.

Theorem lit_eqb_eval : forall (l l' : lit) (theta : valuation),
  lit_eqb l l' = true -> (eval_lit l theta <-> eval_lit l' theta).
Proof.
  unfold eval_lit, lit_eqb; destruct l, l'; destruct v, v0; tsimpl;
    repeat (
    try
    match goal with
    | [ H : ivar_eqb _ _ = true  |- _ ] => apply Z.eqb_eq in H
    | [ H : Z.eqb _ _ = true  |- _ ] => apply Z.eqb_eq in H
    end; tsimpl).
  rewrite H in H0; rewrite H2 in H0; omega.
  rewrite H in H1; rewrite H2 in H1; omega.
Qed.

Theorem dec_evallit : forall (l : lit) (theta : valuation),
  Decidable.decidable (eval_lit l theta).
Proof.
  intros.
  apply (eq_bool_dec (eval_lit l theta) (evalb_lit l theta)); apply evalb_lit_iff.
Qed.

Definition neglit (l : lit) : lit :=
  match l with
  | Neg vp => Pos vp
  | Pos vp => Neg vp
  end.

Theorem neglit_not_lit :
  forall (l : lit) (theta : valuation),
    (eval_lit (neglit l) theta) <-> ~(eval_lit l theta).
Proof.
  intros.
  unfold neglit; destruct l;
  unfold eval_lit; unfold eval_vprop; destruct v; tsimpl.
  rewrite <- Z.eqb_eq in H; rewrite <- Z.eqb_eq; apply not_false_is_true; intro.
  assert (Hb := eq_true_false_abs (Z.eqb (theta i) z)).
  tauto.
Qed.

Lemma lit_not_neglit :
  forall (l : lit) (theta : valuation),
    (eval_lit l theta) <-> ~(eval_lit (neglit l) theta).
Proof.
  intros.
  unfold neglit; destruct l;
  unfold eval_lit; unfold eval_vprop; destruct v; tsimpl.
  rewrite <- Z.eqb_eq in H; rewrite <- Z.eqb_eq; apply not_false_is_true; intro.
  assert (Hb := eq_true_false_abs (Z.eqb (theta i) z)).
  tauto.
Qed.
  
Definition clause : Type := list lit.
Definition prod : Type := list lit.

Fixpoint negclause (cl : clause) :=
  match cl with
  | nil => nil
  | cons c cl' => cons (neglit c) (negclause cl')
  end.
  
(* A clause is true iff some literal is true. *)
Fixpoint eval_clause
  (ls : clause) (theta : valuation) : Prop :=
  match ls with
  | nil => False
  | cons l ls' => (eval_lit l theta) \/ (eval_clause ls' theta)
  end.

(* Definition eval_clauses cs theta := List.fold_left (fun p cl => p /\ eval_clause cl theta) cs True. *)
Fixpoint eval_clauses cs theta :=
  match cs with
  | nil => True
  | cons c cs' => (eval_clause c theta) /\ (eval_clauses cs' theta)
  end.

Fixpoint evalb_clause
 (ls : clause) (theta : valuation) : bool :=
  match ls with
  | nil => false
  | cons l ls' => (evalb_lit l theta) || (evalb_clause ls' theta)
  end.
Theorem evalb_clause_iff : forall ls theta, evalb_clause ls theta = true <-> eval_clause ls theta.
Proof.
  intros; induction ls; unfold evalb_clause, eval_clause; simpl.
  split; intros; [discriminate| tauto].
  fold evalb_clause; fold eval_clause; simpl.
  now rewrite <- IHls, <- evalb_lit_iff, orb_true_iff.
Qed.

Fixpoint eval_prod (ps : prod) (theta : valuation) : Prop :=
  match ps with
  | nil => True
  | cons p ps' => (eval_lit p theta) /\ (eval_prod ps' theta)
  end.
Fixpoint evalb_prod (ps : prod) (theta : valuation) : bool :=
  match ps with
  | nil => true
  | cons p ps' => andb (evalb_lit p theta) (evalb_prod ps' theta)
  end.

Lemma evalb_prod_iff : forall theta ps, eval_prod ps theta <-> evalb_prod ps theta = true.
Proof.
  unfold eval_prod, evalb_prod; induction ps; fold eval_prod; fold evalb_prod.
  tauto.
  repeat (
    try
      match goal with
      | [H : evalb_lit _ _ = true |- _] => apply evalb_lit_iff in H
      | [ |- evalb_lit _ _ = true ] => apply evalb_lit_iff
      end ;
    tsimpl ).
Qed.

Lemma eval_clause_notprod : forall cl theta, eval_clause cl theta <-> ~ eval_prod (negclause cl) theta.
Proof.
  intros cl theta; induction cl.

  unfold eval_clause, negclause, eval_prod; tauto.

  unfold eval_clause, eval_prod, negclause; fold eval_clause; fold eval_prod; fold negclause.
  split; intros.

  intro; destruct H0 as [Hnl Hnp].
  destruct H; [ apply neglit_not_lit in Hnl; contradiction | now apply IHcl in H].

  rewrite IHcl; rewrite lit_not_neglit; apply Decidable.not_and in H.
    assumption. 
    apply (eq_bool_dec (eval_lit (neglit a) theta) (evalb_lit (neglit a) theta) (evalb_lit_iff (neglit a) theta)).
Qed.

Definition lit_valid ds l := forall theta, domain.eval_domset ds theta -> eval_lit l theta.
Definition lit_unsat ds l := forall theta, domain.eval_domset ds theta -> eval_lit l theta -> False.

Lemma lit_valid_neglit : forall ds l, lit_valid ds l <-> lit_unsat ds (neglit l).
Proof.
  unfold lit_valid, lit_unsat; intros.
  split; intros.

  rewrite neglit_not_lit in H1.
  specialize (H theta); tauto.

  specialize (H theta).
  assert (Decidable.decidable (eval_lit l theta)).
    apply (eq_bool_dec (eval_lit l theta) (evalb_lit l theta) (evalb_lit_iff l theta)).
  destruct H1; [assumption | trivial ; apply neglit_not_lit in H1 ; apply H in H0; [contradiction | trivial] ].
Qed.

Definition lit_unsatb ds l :=
  match l with
  | Pos (ILeq x k) => dom_unsatb (dom_meet (var_dom ds x) (dom_le k))
  | Pos (IEq x k) => dom_unsatb (dom_meet (var_dom ds x) (dom_const k))
  | Pos CTrue => false
  | Neg (ILeq x k) => dom_unsatb (dom_meet (var_dom ds x) (dom_ge (Z.succ k)))
  | Neg (IEq x k) => dom_unsatb (dom_meet (var_dom ds x) (dom_neq k))
  | Neg CTrue => true
  end.

(* Should extend this to iff *)
Lemma lit_unsatb_unsat : forall ds l, lit_unsatb ds l = true -> lit_unsat ds l.
Proof.
  intros ds l; unfold lit_unsat, lit_unsatb, eval_lit, eval_vprop;
  destruct l; destruct v; intros; try rewrite dom_unsatb_unsat in *;
    try (specialize (H (theta i)));
    try apply eval_domset_vardom with (x := i) in H0;
    try unfold eval_dom in H0; simpl in H0;
    try rewrite dom_meet_iff in H;
    try dom_spec; try tauto; try congruence; try omega;
    try (unfold dom_unsat; intros; intro).

  assert (Z.succ z <= theta i). omega. tauto.
Qed.
