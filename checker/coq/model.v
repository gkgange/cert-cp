Require Import ZArith.
Require Import prim.
Require Import linear.
Require Import element.
Require Import cumulative.
Require Import domset.
Require Import bounds.
Require Import sol.
Require Import arith.

(* Closed set of constraints. *)
Inductive cst :=
  | Lin : LinearCon.(T) -> cst
  | Elem : ElemConstraint.(T) -> cst  
  | Cumul : CumulConstraint.(T) -> cst  
  | Clause : ClauseCon.(T) -> cst
  | Arith : ArithConstraint.(T) -> cst.

Definition cst_id := Z.
Definition csts := list (cst_id * cst).

Definition eval_cst c theta := match c with
  | Lin x => LinearCon.(eval) x theta
  | Elem x => ElemConstraint.(eval) x theta
  | Cumul x => CumulConstraint.(eval) x theta
  | Clause x => ClauseCon.(eval) x theta
  | Arith x => ArithConstraint.(eval) x theta
  end.

Fixpoint eval_csts (cs : csts) theta := 
  match cs with
  | nil => True
  | cons c cs' => (eval_cst (snd c) theta) /\ (eval_csts cs' theta)
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
