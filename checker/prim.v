(* Definitions for primitive types. *)
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.
Require Import Coq.ZArith.BinInt.
Require Import Compare_dec.
Require Import Omega.
Require Import Logic.
Require Import Classical_Prop.
Require Import ClassicalFacts.
Require Import Decidable.

Open Scope Z_scope.

(* Variable types *)
Definition ivar : Type := nat.
Definition bvar : Type := nat.

(* Type of assignments.
 *  Not currently considering scope. *)
Definition asg : Type := ((ivar -> Z)*(bvar -> bool))%type.

(* Evaluating a variable under an assignment. *)
Definition eval_ivar (iv : ivar) (theta : asg) := (fst theta) iv.
Definition eval_bvar (bv : bvar) (theta : asg) := (snd theta) bv.

(* Primitive propositions. *)
Inductive vprop : Type :=
  | ILeq : ivar -> Z -> vprop
  | IEq : ivar -> Z -> vprop
  | BTrue : bvar -> vprop.

(* A literal is either a positive
 * or negative proposition. *)
Inductive lit : Type :=
  | Pos : vprop -> lit
  | Neg : vprop -> lit.

(* A convenience function, since the implementation
 * seems to be missing from this version. *)
Definition Z_leb (x y : Z) : bool :=
  if Z_le_dec x y then true else false.

Theorem Z_leb_iff_le : forall (x y : Z),
  Z_leb x y = true <-> x <= y.
Proof.
  unfold Z_leb. intros.
  split. intros.
  destruct Z_le_dec. tauto. discriminate.
  intros. destruct Z_le_dec. trivial. tauto.
Qed. 

Definition Z_ltb (x y : Z) : bool :=
  if Z_lt_dec x y then true else false.

Theorem Z_ltb_iff_lt : forall (x y : Z),
  Z_ltb x y = true <-> x < y.
Proof.
  unfold Z_ltb. intros.
  split. intros.
  destruct Z_lt_dec. tauto. discriminate.
  intros. destruct Z_lt_dec. trivial. tauto.
Qed.

Definition Z_eqb (x y : Z) : bool :=
  if Z_eq_dec x y then true else false.

Theorem Z_eqb_iff_eq : forall (x y : Z),
  Z_eqb x y = true <-> x = y.
Proof.
  unfold Z_eqb. intros.
  split. intros.
  destruct Z_eq_dec. tauto. discriminate.
  intros. destruct Z_eq_dec. trivial. tauto.
Qed.

(* Evaluate a proposition under an assignment. *)
Definition eval_vprop
  (p : vprop) (theta : asg) : Prop :=
  match p with
  | ILeq iv k => (eval_ivar iv theta) <= k
  | IEq iv k => (eval_ivar iv theta) = k
  | BTrue bv => (eval_bvar bv theta) = true
  end.

(* Evaluate a literal under an assignment. *)
Definition eval_lit
  (l : lit) (theta : asg) : Prop :=
  match l with
  | Pos vp => eval_vprop vp theta
  | Neg vp => ~(eval_vprop vp theta)
  end.

Theorem dec_evallit : forall (l : lit) (theta : asg),
  decidable (eval_lit l theta).
Proof.
  intros. unfold decidable.
  unfold eval_lit. destruct l.
  unfold eval_vprop. destruct v.
  omega. omega. tauto. tauto.
Qed.

Definition neglit (l : lit) : lit :=
  match l with
  | Neg vp => Pos vp
  | Pos vp => Neg vp
  end.

Theorem neglit_not_lit :
  forall (l : lit) (theta : asg),
    (eval_lit (neglit l) theta) <-> ~(eval_lit l theta).
Proof.
  intros.
  unfold neglit; destruct l.
  unfold eval_lit; unfold eval_vprop; destruct v.
  omega.
  omega.
  tauto.
  unfold eval_lit; unfold eval_vprop; destruct v.
  omega. omega. tauto.
Qed.

Definition clause : Type := list lit.
Definition prod : Type := list lit.

(* A clause is true iff some literal is true. *)
Fixpoint eval_clause
  (ls : clause) (theta : asg) : Prop :=
  match ls with
  | nil => False
  | cons l ls' => (eval_lit l theta) \/ (eval_clause ls' theta)
  end.

Theorem dec_evalclause : forall (ls : clause) (theta : asg),
  decidable (eval_clause ls theta).
Proof.
  intros.
  unfold decidable.
  unfold eval_clause.
  induction ls.
  tauto.
  tauto.
Qed.

Fixpoint neg_clause
  (ls : clause) : prod :=
  match ls with
  | nil => nil
  | cons l ls' => cons (neglit l) (neg_clause ls')
  end.

(* A product is true iff all literals are true. *)
Fixpoint eval_prod (ls : list lit) (theta : asg) : Prop :=
  match ls with
  | nil => True
  | cons l ls' => (eval_lit l theta) /\ (eval_clause ls' theta)
  end.

(* Check eval_prod. *)

Theorem dec_evalprod : forall (ls : clause) (theta : asg),
  decidable (eval_prod ls theta).
Proof.
  intros; unfold decidable; unfold eval_clause.
  induction ls. tauto. tauto.
Qed.

(* Relationships between constraints. *)
Definition implies (con_x : asg -> Prop) (con_y : asg -> Prop) : Prop :=
  forall (theta : asg), (con_x theta) -> (con_y theta).

Definition equiv (con_x : asg -> Prop) (con_y : asg -> Prop) : Prop :=
  forall (theta : asg), (con_x theta) <-> (con_y theta).

Definition lit_leq (x : lit) (y : lit) : Prop :=
  implies (eval_lit x) (eval_lit y).



Definition vprop_leqb (u : vprop) (v : vprop) :=
  match u with
  | ILeq x kx =>
    match v with
    | ILeq y ky => (beq_nat x y) && (Z_leb kx ky)
    | _ => false
    end
  | IEq x kx =>
    match v with
    | ILeq y ky => (beq_nat x y) && (Z_leb kx ky)
    | IEq y ky => (beq_nat x y) && (Z_eqb kx ky)
    | _ => false
    end
  | BTrue x =>
    match v with
    | BTrue y => beq_nat x y
    | _ => false
    end
  end.

Theorem vprop_leqb_valid : forall (u v : vprop),
  vprop_leqb u v = true -> implies (eval_vprop u) (eval_vprop v).
Proof.
  intros. unfold implies. intros.
  unfold vprop_leqb in H.
  unfold eval_vprop in H0. unfold eval_vprop. destruct u, v.
  assert (beq_nat i i0 = true /\ Z_leb z z0 = true).
  apply andb_true_iff; exact H. destruct H1.
  assert (i = i0). apply beq_nat_true; exact H1.
  assert (z <= z0). apply Z_leb_iff_le; exact H2.
  rewrite <- H3. omega.
  discriminate. discriminate.
  assert (beq_nat i i0 = true /\ Z_leb z z0 = true).
  apply andb_true_iff; exact H. destruct H1.
  assert (i = i0). apply beq_nat_true; exact H1.
  assert (z <= z0). apply Z_leb_iff_le; exact H2.
  rewrite <- H3. omega.
  assert (beq_nat i i0 = true /\ Z_eqb z z0 = true).
  apply andb_true_iff; exact H. destruct H1.
  assert (i = i0). apply beq_nat_true; exact H1.
  assert (z = z0). apply Z_eqb_iff_eq; exact H2.
  rewrite <- H3; rewrite <- H4; exact H0.
  discriminate. discriminate. discriminate.
  assert (b = b0). apply beq_nat_true; exact H.
  rewrite <- H1; exact H0.
Qed.

(* FIXME: extend this to handle x = k -> x > (k-1), etc. *)
Definition lit_leqb (x : lit) (y : lit) : bool :=
  match x with
  | Pos u =>
    match y with
    | Pos v => vprop_leqb u v
    | _ => false
    end
  | Neg u =>
    match y with 
    | Neg v => vprop_leqb v u
    | _ => false
    end
  end.

(* Gonna need to update this once I extend lit_leqb. *)
Theorem lit_leqb_valid : forall (x y : lit),
  lit_leqb x y = true -> lit_leq x y.
Proof.
  unfold lit_leqb; unfold lit_leq; unfold implies; unfold eval_lit; intros.
  destruct x, y.
  assert (vprop_leqb v v0 = true -> implies (eval_vprop v) (eval_vprop v0)).
  apply vprop_leqb_valid.
  unfold implies in H1.
  apply H1. exact H. exact H0.
  discriminate. discriminate.
  assert (vprop_leqb v0 v = true -> implies (eval_vprop v0) (eval_vprop v)).
  apply vprop_leqb_valid.
  unfold implies in H1.
  assert (eval_vprop v0 theta -> eval_vprop v theta).
  apply H1; exact H.
  tauto.
Qed.

Fixpoint lit_impl_clause (x : lit) (cl : clause) : bool :=
  match cl with
  | nil => false
  | cons l ls => lit_leqb x l || lit_impl_clause x ls
  end.

Theorem lit_impl_clause_valid : forall (x : lit) (cl : clause),
  lit_impl_clause x cl = true -> implies (eval_lit x) (eval_clause cl).
Proof.
  intros; unfold implies; intros.
  induction cl.
  unfold eval_clause; discriminate.
  unfold lit_impl_clause in H;
  fold lit_impl_clause in H.
  assert (lit_leqb x a = true \/ lit_impl_clause x cl = true).
  apply orb_true_iff; exact H.
  unfold eval_clause; fold eval_clause.
  destruct H1 as [H2 | H3].
  left. assert (lit_leq x a). apply lit_leqb_valid; exact H2.
  apply H1; exact H0.
  right. apply IHcl; exact H3.
Qed.

Fixpoint clause_impl (cl_x cl_y : clause) : bool :=
  match cl_x with
  | nil => true
  | cons l ls => lit_impl_clause l cl_y && clause_impl ls cl_y
  end.

Theorem clause_impl_clause_valid : forall (cl_x cl_y : clause),
  clause_impl cl_x cl_y = true -> implies (eval_clause cl_x) (eval_clause cl_y).
Proof.
  intros ; unfold implies; intros.
  induction cl_x.
  unfold eval_clause in H0; tauto.
  unfold eval_clause in *; fold eval_clause in *;
  unfold clause_impl in H; fold clause_impl in H.
  assert (lit_impl_clause a cl_y = true /\ clause_impl cl_x cl_y = true).
  apply andb_true_iff; exact H.
  destruct H1.
  assert ((eval_lit a theta) -> (eval_clause cl_y theta)).
  apply lit_impl_clause_valid; exact H1.
  assert (eval_clause cl_x theta -> eval_clause cl_y theta).
  apply IHcl_x; exact H2.
  destruct H0.
  apply H3; exact H0.
  apply H4; exact H0.
Qed.
