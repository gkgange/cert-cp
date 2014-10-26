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
Require Import List.

Open Scope Z_scope.

(* Some convenience Z-handling functions. *)
(*
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

Theorem Z_leb_false_iff_notle : forall (x y : Z),
  Z_leb x y = false <-> ~ x <= y.
Proof.
  unfold Z_leb. intros.
  destruct Z_le_dec.
  split. intro; discriminate.
  intro. assert False. omega. tauto.
  split. intro. exact n.
  intro. trivial.
Qed.
  *)

Definition Z_leb (x y : Z) : bool := Zle_bool x y.

Theorem Z_leb_iff_le : forall (x y : Z),
  Z_leb x y = true <-> x <= y.
Proof.
  unfold Z_leb; intros. symmetry; apply Zle_is_le_bool.
Qed.

Theorem Z_leb_false_iff_notle : forall (x y : Z),
  Z_leb x y = false <-> ~ x <= y.
Proof.
  intros.
  split; intro. intro.
    apply Z_leb_iff_le in H0. congruence.
    apply not_true_iff_false; intro.
    apply Z_leb_iff_le in H0; tauto.
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

(*
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
*)
Definition Z_eqb (x y : Z) : bool := Zeq_bool x y.
Theorem Z_eqb_iff_eq : forall (x y : Z),
  Z_eqb x y = true <-> x = y.
Proof.
  unfold Z_eqb; intros; symmetry.
  apply Zeq_is_eq_bool.
Qed.

(* Variable types *)
Definition ivar : Type := Z.
Definition bvar : Type := Z.

Definition ivar_eqb x x' := Z_eqb x x'.
Theorem ivar_eqb_iff_eq : forall (x x' : ivar),
  ivar_eqb x x' = true <-> x = x'.
Proof.
  unfold ivar_eqb. intros.
  apply Z_eqb_iff_eq.
Qed.

Definition bvar_eqb x x' := Z_eqb x x'.
Theorem bvar_eqb_iff_eq : forall (x x' : bvar),
  bvar_eqb x x' = true <-> x = x'.
Proof.
  unfold ivar_eqb. intros.
  apply Z_eqb_iff_eq.
Qed.

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
  | BTrue : bvar -> vprop
  | CTrue : vprop.

(* A literal is either a positive
 * or negative proposition. *)
Inductive lit : Type :=
  | Pos : vprop -> lit
  | Neg : vprop -> lit.

(* Evaluate a proposition under an assignment. *)
Definition eval_vprop
  (p : vprop) (theta : asg) : Prop :=
  match p with
  | ILeq iv k => (eval_ivar iv theta) <= k
  | IEq iv k => (eval_ivar iv theta) = k
  | BTrue bv => (eval_bvar bv theta) = true
  | CTrue => True
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
  omega. omega. tauto. tauto. tauto.
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
  tauto.
  unfold eval_lit; unfold eval_vprop; destruct v.
  omega. omega. tauto. tauto.
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

Theorem app_clause_or : forall (cx cy : clause) (theta : asg),
  eval_clause (cx ++ cy) theta <-> eval_clause cx theta \/ eval_clause cy theta.
Proof.
  intros; induction cx.
    unfold eval_clause; simpl; fold eval_clause. tauto.

    unfold eval_clause; simpl; fold eval_clause. rewrite IHcx. tauto.
Qed.

Theorem notapp_clause_iff : forall (cx cy : clause) (theta : asg),
  ~ eval_clause (cx ++ cy) theta <-> ~ eval_clause cx theta /\ ~ eval_clause cy theta.
Proof.
  intros; split.
    intros.
      split.
        assert (~eval_clause cx theta \/ eval_clause cx theta).
          tauto.
        destruct H0.
          exact H0.
          apply or_introl with (B := eval_clause cy theta) in H0.
          apply app_clause_or in H0. tauto.

        assert (~eval_clause cy theta \/ eval_clause cy theta).
          tauto.
        destruct H0.
          exact H0.
          apply or_intror with (A := eval_clause cx theta) in H0.
          apply app_clause_or in H0. tauto.

        intros; destruct H.
        assert (~ eval_clause (cx ++ cy) theta \/ eval_clause (cx ++ cy) theta).
          tauto.
        destruct H1.
          exact H1.
          apply app_clause_or in H1. tauto.
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

Record Constraint : Type := mkConstraint
  { T : Type ;
    eval : T -> asg -> Prop ;
    check : T -> clause -> bool ;
    check_valid : 
      forall (x : T) (cl : clause),
      check x cl = true -> implies (eval x) (eval_clause cl) }.

Definition check_inf (C : Constraint) (x : C.(T)) (cl : clause) := C.(check) x cl.

Definition vprop_leqb (u : vprop) (v : vprop) :=
  match u with
  | ILeq x kx =>
    match v with
    | ILeq y ky => (ivar_eqb x y) && (Z_leb kx ky)
    | _ => false
    end
  | IEq x kx =>
    match v with
    | ILeq y ky => (ivar_eqb x y) && (Z_leb kx ky)
    | IEq y ky => (ivar_eqb x y) && (Z_eqb kx ky)
    | _ => false
    end
  | BTrue x =>
    match v with
    | BTrue y => bvar_eqb x y
    | _ => false
    end
  | CTrue =>
    match v with
    | CTrue => true
    | _ => false
    end
  end.

Theorem vprop_leqb_valid : forall (u v : vprop),
  vprop_leqb u v = true -> implies (eval_vprop u) (eval_vprop v).
Proof.
  intros. unfold implies. intros.
  unfold vprop_leqb in H.
  unfold eval_vprop in H0. unfold eval_vprop. destruct u, v.
  assert (ivar_eqb i i0 = true /\ Z_leb z z0 = true).
  apply andb_true_iff; exact H. destruct H1.
  assert (i = i0). apply ivar_eqb_iff_eq; exact H1.
  assert (z <= z0). apply Z_leb_iff_le; exact H2.
  rewrite <- H3. omega.
  discriminate. discriminate. tauto.
  assert (ivar_eqb i i0 = true /\ Z_leb z z0 = true).
  apply andb_true_iff; exact H. destruct H1.
  assert (i = i0). apply ivar_eqb_iff_eq; exact H1.
  assert (z <= z0). apply Z_leb_iff_le; exact H2.
  rewrite <- H3. omega.
  assert (ivar_eqb i i0 = true /\ Z_eqb z z0 = true).
  apply andb_true_iff; exact H. destruct H1.
  assert (i = i0). apply ivar_eqb_iff_eq; exact H1.
  assert (z = z0). apply Z_eqb_iff_eq; exact H2.
  rewrite <- H3; rewrite <- H4; exact H0.
  discriminate. discriminate. discriminate. discriminate.
  assert (b = b0). apply ivar_eqb_iff_eq; exact H.
  rewrite <- H1; exact H0. tauto.
  discriminate. discriminate. discriminate. tauto.
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

Fixpoint check_clause (cl_x cl_y : clause) : bool :=
  match cl_x with
  | nil => true
  | cons l ls => lit_impl_clause l cl_y && check_clause ls cl_y
  end.

Theorem check_clause_valid : forall (cl_x cl_y : clause),
  check_clause cl_x cl_y = true -> implies (eval_clause cl_x) (eval_clause cl_y).
Proof.
  intros ; unfold implies; intros.
  induction cl_x.
  unfold eval_clause in H0; tauto.
  unfold eval_clause in *; fold eval_clause in *;
  unfold check_clause in H; fold check_clause in H.
  assert (lit_impl_clause a cl_y = true /\ check_clause cl_x cl_y = true).
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

Definition CheckClause := mkConstraint clause eval_clause check_clause.

(* Var reasoning. *)
Definition vprop_ivar (vp : vprop) :=
  match vp with
  | ILeq x _ => Some x
  | IEq x _ => Some x
  | _ => None
  end.

Definition lit_ivar (l : lit) :=
  match l with
  | Pos vp => vprop_ivar vp
  | Neg vp => vprop_ivar vp
  end.

Theorem neglit_ivar : forall (l : lit),
  lit_ivar l = lit_ivar (neglit l).
Proof.
  unfold lit_ivar, neglit; destruct l; simpl.
    trivial. trivial.
Qed.
  
Fixpoint is_clausevar (cl : clause) (x : ivar) :=
  match cl with
  | nil => False
  | cons l cl' => (lit_ivar l = Some x) \/ (is_clausevar cl' x)
  end.
  
