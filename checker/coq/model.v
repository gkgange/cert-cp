Require Import ZArith.
Require Import prim.
Require Import linear.
Require Import element.
Require Import cumulative.
Require Import domset.
Require Import bounds.
Require Import sol.
Require Import arith.

Require Import linear_dset.
Require Import element_dset.
Require Import cumul_dset.

(* Closed set of constraints. *)
Inductive cst :=
  | Lin : LinearCon.(T) -> cst
  | Elem : ElemConstraint.(T) -> cst  
  | Cumul : CumulConstraint.(T) -> cst  
  | Clause : ClauseCon.(T) -> cst
  | Arith : ArithConstraint.(T) -> cst.

Definition make_linear xs k := Lin (xs, k).
Definition make_element x y ks := Elem (element.Element x y ks).
Definition make_cumul (c : cumul) := Cumul c.                                  

Definition cst_id := Z.
Definition csts := list (cst_id * cst).

Definition eval_cst c theta := match c with
  | Lin x => LinearCon.(eval) x theta
  | Elem x => ElemConstraint.(eval) x theta
  | Cumul x => CumulConstraint.(eval) x theta
  | Clause x => ClauseCon.(eval) x theta
  | Arith x => ArithConstraint.(eval) x theta
  end.

Definition eval_cst_bnd b c theta :=
  match c with
  | Lin x => eval LinearDSet (b, x) theta                                            
  | Elem x => eval ElemDbnd (b, x) theta                                            
  | Cumul x => eval CumulDomBnd (b, x) theta                                            
  | Clause x => eval (DomboundedConstraint ClauseCon) (b, x) theta
  | Arith x => eval ArithDbnd (b, x) theta
  end.

Fixpoint eval_csts (cs : csts) theta := 
  match cs with
  | nil => True
  | cons c cs' => (eval_cst (snd c) theta) /\ (eval_csts cs' theta)
  end.

Definition eval_csts_bnd b cs theta :=
  match cs with
  | nil => True
  | cons c cs' => (eval_cst_bnd b (snd c) theta) /\ (eval_csts cs' theta)
  end.

Definition model := ((list model_bound) * csts)%type.

Definition eval_model model theta :=
  (eval_bounds (fst model) theta) /\ (eval_csts (snd model) theta).

Definition model_unsat model := forall theta, ~ eval_model model theta.

Definition ModelConstraint : Constraint := 
  mkConstraint model eval_model.

Definition check_cst_sol (c : cst) (s : asg) :=
  match c with
  | Lin x => sol_check LinearCon LinearSolCheck x s
  | Elem x => sol_check ElemConstraint ElementSolCheck x s
  | Cumul x => sol_check CumulConstraint CumulSolCheck x s
  | Clause x => sol_check ClauseCon CheckClauseSol x s
  | Arith x => sol_check ArithConstraint ArithSolCheck x s
  end.

Definition check_cst (c : cst) (cl : clause) :=
  match c with
  | Lin x => check LinearCon CheckLinear x cl
  | Elem x => check ElemConstraint ElemCheck x cl
  | Cumul x => check CumulConstraint CumulCheck x cl
  | Clause x => check ClauseCon CheckClause x cl
  | Arith x => check ArithConstraint ArithCheck x cl
  end.

Definition check_cst_bnd b (c : cst) (cl : clause) :=
  match c with
  | Lin x => check LinearDSet LinearDBCheck (b, x) cl
  | Elem x => check ElemDbnd ElemDomCheck (b, x) cl
  | Cumul x => check CumulDomBnd CumulTTDCheck (b, x) cl
  | Arith x => check ArithDbnd ArithDomCheck (b, x) cl
  (* GKG: FIXME *)
  | Clause x => check ClauseCon CheckClause x cl
  end.

Theorem check_cst_valid : forall (c : cst) (cl : clause),
  check_cst c cl = true ->
    forall theta, eval_cst c theta -> eval_clause cl theta.
Proof.
  unfold eval_cst, check_cst; destruct c; simpl; intros;
    [apply (check_valid LinearCon CheckLinear t cl) |
     apply (check_valid ElemConstraint ElemCheck t cl) in H |
     apply (check_valid CumulConstraint CumulCheck t cl) in H |
     apply (check_valid ClauseCon CheckClause t cl) in H |
     apply (check_valid ArithConstraint ArithCheck t cl) in H ];
  unfold implies in H; try apply H; try apply H0.
Qed.

Theorem check_cst_bnd_valid : forall (b : domset) (c : cst) (cl : clause),
  check_cst_bnd b c cl = true ->
    forall theta, eval_domset b theta -> eval_cst c theta -> eval_clause cl theta.
Proof.
  unfold eval_cst, check_cst_bnd; destruct c; intros;
  [apply (check_valid LinearDSet LinearDBCheck (b, t) cl) |
   apply (check_valid ElemDbnd ElemDomCheck (b, t) cl) |
   apply (check_valid CumulDomBnd CumulTTDCheck (b, t) cl) |
   apply (check_valid ClauseCon CheckClause t cl) |
   apply (check_valid ArithDbnd ArithDomCheck (b, t) cl) ];
  try assumption; try (apply eval_dombounded_if; assumption).
Qed.

Definition is_model_ub (m : model) (o : ivar) (theta : asg) :=
  forall theta', eval_model m theta' -> (eval_ivar o theta) <= (eval_ivar o theta').

Definition is_model_minimum (m : model) (o : ivar) (theta : asg) :=
  eval_model m theta /\ is_model_ub m o theta.