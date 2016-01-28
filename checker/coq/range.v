(* Most of these than probably go. *)
Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import Compare_dec.
(* Require Import Omega. *)
Require Import Decidable.
Require Import List.
Require Psatz.

Require Import assign.

(* Bounds on a variable. *)
Inductive bound :=
  | Unbounded : bound
  | Bounded : Z -> bound.

Definition dbound := (bound * bound)%type.

(*
 Definition model_bound := (ivar * Z * Z)%type.
*)

Open Scope Z_scope.

(* Evaluating bounds under an assignment. *)
Definition sat_lb (b : bound) (k : Z) :=
  match b with
  | Unbounded => True
  | Bounded k' => k' <= k
  end.

Definition eval_lb (x : ivar) (b : bound) (theta : valuation) :=
  sat_lb b (theta x).

Definition sat_ub (b : bound) (k : Z) :=
  match b with
  | Unbounded => True
  | Bounded k' => k <= k'
  end.

Definition eval_ub (x : ivar) (b : bound) (theta : valuation) :=
  sat_ub b (theta x).

Definition sat_dbound (db : dbound) (k : Z) :=
  sat_lb (fst db) k /\ sat_ub (snd db) k.

Definition satb_lb (b : bound) (k : Z) :=
  match b with
  | Unbounded => true
  | Bounded k' => Z.leb k' k
  end.
Theorem satb_lb_iff_lb : forall (b : bound) (k : Z),
  satb_lb b k = true <-> sat_lb b k.
Proof.
  unfold satb_lb, sat_lb; intros; destruct b.
  tauto.
  symmetry; apply Zle_is_le_bool.
Qed.

Definition satb_ub (b : bound) (k : Z) :=
  match b with
  | Unbounded => true
  | Bounded k' => Z.leb k k'
  end.
Definition satb_dbound (db : dbound) (k : Z) :=
  satb_lb (fst db) k && satb_ub (snd db) k.

Definition unsat_db (db : dbound) :=
  forall (k : Z), ~ sat_dbound db k.

Definition unsatb_db (db : dbound) :=
  match (fst db) with
  | Unbounded => false
  | Bounded k =>
      match (snd db) with
      | Unbounded => false
      | Bounded k' => Z.ltb k' k
      end
  end.

Definition eval_dbound (x : ivar) (db : dbound) (theta : valuation) :=
  sat_dbound db (theta x).

Definition bound_le (x : bound) (y : bound) : Prop :=
  match x with
  | Unbounded => True
  | Bounded kx =>
    match y with
    | Unbounded => False
    | Bounded ky => kx <= ky
    end
  end.

Definition bound_leb (x : bound) (y : bound) : bool :=
  match x with
  | Unbounded => true
  | Bounded kx =>
    match y with
    | Unbounded => false
    | Bounded ky => Z.leb kx ky
    end
  end.
Definition bound_max (x : bound) (y : bound) :=
  match x with
  | Unbounded => y
  | Bounded kx =>
    match y with
    | Unbounded => Bounded kx
    | Bounded ky =>
       Bounded (Zmax kx ky)
    end
  end.
Definition bound_must2 (f : Z -> Z -> Z) (x y : bound) :=
  match (x, y) with
  | (Unbounded, _) => Unbounded
  | (_, Unbounded) => Unbounded
  | (Bounded k, Bounded k') => Bounded (f k k')
  end.

Definition bound_may2 (f : Z -> Z -> Z) (x y : bound) :=
  match (x, y) with
  | (Unbounded, _) => y
  | (_, Unbounded) => x
  | (Bounded k, Bounded k') => Bounded (f k k')
  end.

Definition bound_map (x : bound) (f : Z -> Z) :=
  match x with
  | Unbounded => Unbounded
  | Bounded k => Bounded (f k)
  end.

(*
Definition bound_min (x : bound) (y : bound) :=
  match x with
  | Unbounded => y
  | Bounded kx =>
    match y with
    | Unbounded => Bounded kx
    | Bounded ky =>
       Bounded (Zmin kx ky)
    end
  end.
*)
Definition bound_min (x y : bound) := bound_may2 Z.min x y.

Definition bound_add := bound_must2 Z.add.
Definition bound_mul := bound_must2 Z.mul.

Definition db_add (du dv : dbound) :=
  (bound_add (fst du) (fst dv), bound_add (snd du) (snd dv)).

Definition db_meet (dx : dbound) (dy : dbound) :=
  (bound_max (fst dx) (fst dy), bound_min (snd dx) (snd dy)).

Ltac unfold_satdb := unfold sat_dbound, sat_lb, sat_ub in *; simpl in *.

(*
Definition range_join rx ry :=
  match (rx, ry) with
  | (None, _) => ry
  | (_, None) => rx
  | (Some (lx, ux), Some (ly, uy)) =>
     Some (bound_must2 Z.min lx ly, bound_must2 Z.max ux uy)
  end.
*)

Definition db_apply2 (f : Z -> Z -> Z) rx ry :=
  match (rx, ry) with
  | ((lx, ux), (ly, uy)) => (bound_must2 f lx ly, bound_must2 f ux uy)
  end.

Definition monotone2_l (f : Z -> Z -> Z) := forall k k' c, Z.le k k' -> Z.le (f k c) (f k' c).
Definition monotone2_r (f : Z -> Z -> Z) := forall k c c', Z.le c c' -> Z.le (f k c) (f k c').
Definition monotone2 (f : Z -> Z -> Z) := forall k k' c c', Z.le k k' -> Z.le c c' -> Z.le (f k c) (f k' c').

Lemma monotone2_if : forall f, monotone2_l f -> monotone2_r f -> monotone2 f.
Proof.
  unfold monotone2_l, monotone2_r, monotone2; intros.
  apply (H k k' c) in H1; apply (H0 k' c c') in H2; omega.
Qed.

(*
Definition sat_range rx k := match rx with
  | None => False
  | Some db => sat_dbound db k
  end.
*)
Lemma mono_db_apply2 : forall f rx ry k k', monotone2 f -> sat_dbound rx k -> sat_dbound ry k' -> sat_dbound (db_apply2 f rx ry) (f k k').
Proof.
  intros f rx ry k k'; unfold sat_dbound, db_apply2.
  destruct rx, ry; try tauto; simpl in *.

  intros; unfold_satdb; unfold bound_must2; destruct b, b0, b1, b2; simpl in *; try tauto; unfold monotone2 in H; tsimpl; now apply H.
Qed.

Definition db_join x y :=
  if unsatb_db x then
    y
  else if unsatb_db y then
    x
  else
    (match (fst x, fst y) with
       | (Bounded k, Bounded k') => Bounded (Z.min k k')
       | _ => Unbounded
     end,
     match (snd x, snd y) with
       | (Bounded k, Bounded k') => Bounded (Z.max k k')
       | _ => Unbounded
     end).

Definition minus_bound (u : bound) :=
  match u with
  | Unbounded => Unbounded
  | Bounded x => Bounded (-x)
  end.

Definition mul_pos_bound (k : Z) (u : bound) :=
  match u with
  | Unbounded => Unbounded
  | Bounded x => Bounded (k*x)
  end.

Definition minus_dbound (db : dbound) :=
  (minus_bound (snd db), minus_bound (fst db)).
Definition mul_pos_dbound (k : Z) (db : dbound) :=
  (mul_pos_bound k (fst db), mul_pos_bound k (snd db)).
Definition mul_neg_dbound (k : Z) (db : dbound) :=
  minus_dbound (mul_pos_dbound (-k) db).

Definition mul_z_dbound (k : Z) (db : dbound) :=
  match Zcompare k 0%Z with
  | Eq => (Bounded 0%Z, Bounded 0%Z)
  | Gt => mul_pos_dbound k db
  | Lt => mul_neg_dbound k db
  end.

Definition db_contained (db : dbound) (lb ub : Z) :=
  match (fst db) with
  | Unbounded => False
  | Bounded l => Zle lb l
  end /\
  match (snd db) with
  | Unbounded => False
  | Bounded u => Zle u ub
  end.

Definition db_containedb  (db : dbound) (lb ub : Z) :=
  match (fst db) with
  | Unbounded => false
  | Bounded l => Z.leb lb l
  end &&
  match (snd db) with
  | Unbounded => false
  | Bounded u => Z.leb u ub
  end.

(*
Definition sat_bound (b : model_bound) (x : ivar) (k : Z) :=
  match b with
  | (x', lb, ub) =>
    x <> x' \/ (Zle lb k /\ Zle k ub)
  end.
*)
    
       
(*
Fixpoint tighten_model_ub (bs : list model_bound) (x : ivar) (k : Z) :=
  match bs with
  | nil => nil
  | cons (y, l, u) bs' =>
    let tl := tighten_model_ub bs' x k in
    if ivar_eqb x y then cons (y, l, Z.min k u) tl else cons (y, l, u) tl
  end.

Fixpoint eval_bounds (bs : list model_bound) (theta : valuation) :=
  match bs with
  | nil => True
  | cons b bs' => (eval_bound b theta) /\ (eval_bounds bs' theta)
  end.
Fixpoint evalb_bounds bs theta :=
  match bs with
  | nil => true
  | cons b bs' => (evalb_bound b theta) && evalb_bounds bs' theta
  end.
Theorem evalb_bounds_iff : forall bs theta, evalb_bounds bs theta = true <-> eval_bounds bs theta.
Proof.
  intros; induction bs; simpl;
  [tauto |
   unfold evalb_bounds, eval_bounds ; fold evalb_bounds; fold eval_bounds ;
   now rewrite andb_true_iff, evalb_bound_iff, IHbs].
Qed.
  
Lemma tighten_model_ub_correct : forall (bs : list model_bound) (x : ivar) (k : Z) (theta : valuation),
  eval_bounds bs theta -> (eval_ivar x theta <= k) -> eval_bounds (tighten_model_ub bs x k) theta.
Proof.
  intros.
  induction bs; unfold eval_bounds, tighten_model_ub; fold eval_bounds; fold tighten_model_ub;
    try trivial.
  destruct a; destruct p; simpl in *; destruct H as [Hl Hr].
  remember (ivar_eqb x i) as exi; destruct exi; symmetry in Heqexi.
  apply ivar_eqb_iff_eq in Heqexi.
  unfold eval_bounds; fold eval_bounds.

  split; [unfold eval_bound | now apply IHbs].
  rewrite Heqexi in H0; Psatz.lia.

  unfold eval_bounds; fold eval_bounds.
  split; [now unfold eval_bound | now apply IHbs].
Qed.
*)

    
(*
Definition bounded (C : Constraint) : Type :=
  ((list (ivar*Z*Z)) * C.(T))%type.
Definition bounded_eval (C : Constraint) (x : bounded C) (theta : valuation) :=
  eval_bounds (fst x) theta /\ C.(eval) (snd x) theta.
Definition bounded_check (C : Constraint) (Ch : Checker C) (x : bounded C) (cl : clause) :=
  check C Ch (snd x) (negclause_of_bounds (fst x) ++ cl).
Theorem bounded_check_valid : forall (C : Constraint) (Ch : Checker C) (x : bounded C) (cl : clause),
  bounded_check C Ch x cl = true -> implies (bounded_eval C x) (eval_clause cl).
Proof.
  unfold implies, bounded_eval; intros.
    destruct H0.
    apply (check_valid C Ch) in H.
    unfold implies in H.
    assert (eval_clause (negclause_of_bounds (fst x) ++ cl) theta).
      apply H. exact H1.
    apply app_clause_or in H2.
    rewrite negclause_of_bounds_valid in H0.
    destruct H2.
      tauto.
      exact H2.
Qed.

Definition BoundedConstraint (C : Constraint) : Constraint :=
  mkConstraint (bounded C) (bounded_eval C).
Definition BoundedChecker (C : Constraint) (Ch : Checker C)  : Checker (BoundedConstraint C) :=
  mkChecker (BoundedConstraint C) (bounded_check C Ch) (bounded_check_valid C Ch).

*)