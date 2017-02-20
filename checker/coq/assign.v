(* Alternate formulation of stuff. *)
Require Import ZArith.
Require Decidable.
Require Quote.
Require zset.
Require map.
Require Bool.
Require Psatz.

Open Scope Z_scope.
Definition ivar := Z.
Definition val := Z.

Inductive iterm :=
  | Ivar : ivar -> iterm
  | Ilit : Z -> iterm.
                
Definition valuation := (Z -> val).

Definition eval_ivar (x : ivar) (theta : valuation) := theta x.
Definition eval_iterm (t : iterm) (theta : valuation) :=
  match t with
    | Ivar v => eval_ivar v theta
    | Ilit k => k
  end.

Definition ivar_eqb x y := Z.eqb x y.

Definition expr := valuation -> val.
Definition bexpr := valuation -> bool.

Definition const (k : Z) := (fun theta : valuation => k).
Definition var (v : Z) := (fun theta : valuation => theta v).
Definition unary_op := expr -> expr.
Definition binary_op := expr -> expr.

Definition pred := expr -> expr -> bexpr.
Definition binary_lop := bexpr -> bexpr -> bexpr.
Definition unary_lop := bexpr -> bexpr.

Definition add (x y : expr) := (fun theta => Z.add (x theta) (y theta)).
Definition sub (x y : expr) := (fun theta => Z.sub (x theta) (y theta)).
Definition mul (x y : expr) := (fun theta => Z.mul (x theta) (y theta)).

Definition leq (x y : expr) := (fun theta => Z.leb (x theta) (y theta)).
Definition eq (x y : expr) := (fun theta => Z.eqb (x theta) (y theta)).

Definition not (x : bexpr) := (fun theta => negb (x theta)).
Definition and (x y : bexpr) := (fun theta => andb (x theta) (y theta)).
Definition or (x y : bexpr) := (fun theta => orb (x theta) (y theta)).

Definition approximates (A : Type) (R : Type) (mem : A -> R -> Prop) (ex : valuation -> R) (abs : A) :=
  forall val k, ex val = k -> mem abs k = True.

Definition cst_approx (T R : Type) (mem : R -> Z -> Z -> Prop) (cst : T -> valuation -> Prop) (approx : T -> R) :=
  forall inst theta x, cst inst theta -> mem (approx inst) x (theta x).

(*
Ltac find_if :=
  match goal with
  | [ |- context[if ?X then _ else _] ] => destruct X
  end.
*)
Lemma eq_bool_dec (P : Prop) (b : bool) : (b = true <-> P) -> Decidable.decidable P.
Proof.
  unfold Decidable.decidable.
  intros; destruct b; [left; tauto | right; intro].
  apply H in H0; congruence.
Qed.

Lemma ivar_eq_dec : forall (x y : ivar), x = y \/ x <> y.
Proof. intros. assert (H := Z.eqb_eq x y); now apply eq_bool_dec in H. Qed.
Lemma impl_and_l : forall P Q R, (P -> Q /\ R) -> (P -> Q).
Proof. tauto. Qed.
Lemma impl_and_r : forall P Q R, (P -> Q /\ R) -> (P -> R).
Proof. tauto. Qed.
                        
Ltac ifelim :=
  repeat (match goal with
    (* Eliminating ITEs *)
    | [ H : context[if ?X then _ else _] |- _ ] => (let t := fresh in let eq := fresh in remember X as t eqn:eq; destruct t; symmetry in eq)
    | [ |- context[if ?X then _ else _] ] => (let t := fresh in let eq := fresh in remember X as t eqn:eq; destruct t; symmetry in eq)
  end).

Ltac eqelim term :=
  let id := fresh in let eq := fresh in
  (remember term as id eqn:eq; destruct id; symmetry in eq).

Ltac tsimpl :=
  (
    repeat
    (
    match goal with
    (* Basic stuff on Prop *)
    | [ |- True ] => constructor
    | [ H : False |- _] => contradiction
    | [ H : True |- _ ] => clear H
    | [ H : ?P /\ ?Q |- _ ] => destruct H
    | [ H : ?P <-> ?Q |- _] => destruct H
    | [ |- ~ _ ] => intro
    | [ |- _ -> _] => intro
    | [ |- ?P /\ ?Q ] => split
    | [ |- _ <-> _ ] => split
    | [ H : ?P -> (?Q /\ ?R) |- _ ] =>
      (let r := fresh in assert (l := H) ; apply impl_and_l in H; apply impl_and_r in r)
    (* Dealing with equalities *)                         
    | [ H : Some _ = Some _ |- _] => inversion H; clear H
    (* Eliminating ITEs *)
    | [ H : context[if ?X then _ else _] |- _ ] => (let t := fresh in let eq := fresh in remember X as t eqn:eq; destruct t; symmetry in eq)
    | [ |- context[if ?X then _ else _] ] => (let t := fresh in let eq := fresh in remember X as t eqn:eq; destruct t; symmetry in eq)
    (* Wrangling Booleans. *)                      
    | [ |- context[andb ?X ?Y = true] ] => rewrite Bool.andb_true_iff
    | [ |- context[andb ?X ?Y = false] ] => rewrite Bool.andb_false_iff
    | [ |- context[negb ?X = true] ] => rewrite Bool.negb_true_iff                                                    
    | [ |- context[negb ?X = false] ] => rewrite Bool.negb_false_iff                                                    
    | [ H : context[andb ?X ?Y = true] |- _] => rewrite Bool.andb_true_iff in H
    | [ H : context[andb ?X ?Y = false] |- _] => rewrite Bool.andb_false_iff in H
    | [ H : context[negb ?X = true] |- _ ] => rewrite Bool.negb_true_iff in H
    | [ H : context[negb ?X = false] |- _ ] => rewrite Bool.negb_false_iff in H
    (* Bool/Prop wrangling of Z inequalities *)
    | [ H : context[Z.leb ?X ?Y = true] |- _ ] => rewrite <- Zle_is_le_bool in H
    | [ H : context[Z.leb ?X ?Y = false] |- _ ] => rewrite Z.leb_gt in H
    | [ H : context[Z.ltb ?X ?Y = true] |- _ ] => rewrite <- Zlt_is_lt_bool in H
    | [ H : context[Z.ltb ?X ?Y = false] |- _ ] => rewrite Z.ltb_ge in H
    | [ |- context[Z.leb ?X ?Y = true] ] => rewrite <- Zle_is_le_bool
    | [ |- context[Z.ltb ?X ?Y = true] ] => rewrite <- Zlt_is_lt_bool
    | [ |- context[Z.leb ?X ?Y = false] ] => rewrite Z.leb_gt
    | [ |- context[Z.ltb ?X ?Y = false] ] => rewrite Z.ltb_ge
    end ;
    simpl in *
    )
  ) ; try (tauto || congruence || Psatz.lia).
