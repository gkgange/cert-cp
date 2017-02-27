Require Import ZArith.
Require Import Bool.
Require Import List.
Require Import assign.
Require Import domain.
Require Import range.
Require Import range_properties.
Require Import constraint.
Require arith_ops.
(* Require reif. *)

(* Propagation for multiplication.
 * We're not doing full factorization, just bounds. *)

(*
Inductive int_term :=
  | Const : Z -> int_term
  | Var : ivar -> int_term.

Definition eval_int_term term theta :=
  match term with
  | Const c => c
  | Var v => eval_ivar v theta
  end.

Definition domset_term_dbound term ds :=
  match term with
  | Const c => (Bounded c, Bounded c)
  | Var x => (fst (var_dom ds x))
  end.
*)

Inductive binop := Plus | Times | Sub | Div | Min | Max.

Definition rel_of f : Z -> Z -> Z -> Prop := fun z x y => Z.eq z (f x y).
Definition part_of (f : Z -> Z -> Z) :=
  fun x y => match x, y with
               | Some x', Some y' => Some (f x' y')
               | None, _ => None
               | _, None => None
             end.

Definition binop_rel op :=
   match op with
     | Plus => rel_of Z.add
     | Times => rel_of Z.mul
     | Sub => rel_of Z.sub
     | Div => fun z x y => y <> 0%Z /\ z = Z.quot x y
     | Min => rel_of Z.min
     | Max => rel_of Z.max
   end.
  
Definition binop_pfun op :=
  match op with
    | Plus => part_of Z.add
    | Times => part_of Z.mul
    | Sub => part_of Z.sub
    | Div =>
      (fun x y =>
         match x, y with
           | Some x, Some y =>
             if Z.eqb y 0%Z then
               None
             else
               Some (Z.quot x y)
           | None, _ => None
           | _, None => None
         end)
    | Min => part_of Z.min
    | Max => part_of Z.max
  end.
    
Inductive aexpr :=
| T : iterm -> aexpr
| Op : binop -> aexpr -> aexpr -> aexpr.

Fixpoint eval_aexpr exp theta v :=
  match exp with
    | T t => v = eval_iterm t theta
    | Op op x y =>
      exists x' y', eval_aexpr x theta x' /\ eval_aexpr y theta y' /\ binop_rel op v x' y'
  end.

Definition arith_eq := (iterm * aexpr)%type.
Definition eval_arith_eq aeq theta := eval_aexpr (snd aeq) theta (eval_iterm (fst aeq) theta).

Definition db_of_binop op : dbound -> dbound -> dbound :=
   match op with
     | Plus => db_add
     | Times => arith_ops.db_mul
     | Sub => fun x y => db_add x (arith_ops.db_neg y)
     | Div => fun x y => arith_ops.db_div x y
     | Min => db_min
     | Max => db_max
   end.
Lemma db_of_binop_spec : forall op x x' k k' r, sat_dbound x k -> sat_dbound x' k' -> binop_rel op r k k' -> sat_dbound (db_of_binop op x x') r.
Proof.
  intros op x x' k k' r.
  unfold binop_rel, db_of_binop, rel_of; destruct op; intros Hx Hx' Hr; try rewrite Hr.
  + apply db_impl_adddb; intuition.
  + apply arith_ops.db_mul_sound; assumption.
  + apply arith_ops.db_neg_valid in Hx'.
    apply db_impl_adddb; intuition.
  + destruct Hr as [H0 Hr].
    rewrite Hr; apply arith_ops.db_div_sound; assumption.
  + apply range.db_min_spec; assumption.
  + apply range.db_max_spec; assumption.
Qed.

Fixpoint db_of_aexpr exp ds :=
  match exp with
  | T t => range_of_dom (term_dom ds t)
  | Op op x y => db_of_binop op (db_of_aexpr x ds) (db_of_aexpr y ds)
  end.
Lemma db_of_aexpr_spec : forall exp ds theta r, eval_domset ds theta -> eval_aexpr exp theta r -> sat_dbound (db_of_aexpr exp ds) r.
Proof.
  intros exp ds theta r Hds.
  generalize r; clear r.
  induction exp; intro r; unfold db_of_aexpr, eval_aexpr; fold db_of_aexpr; fold eval_aexpr.
  + intro Hr; rewrite Hr.
    apply term_dom_valid; assumption.
  + intro Hxy; elim Hxy; clear Hxy; intros x' Hy; elim Hy; clear Hy; intros y' Hxy; destruct Hxy as [Hx [Hy Hr]].
    apply db_of_binop_spec with (k := x') (k' := y'); try (apply IHexp1 || apply IHexp2); try assumption.
Qed.    
  
(*
Inductive int_arith :=
  | Mul : ivar -> ivar -> ivar -> int_arith
  | Div : ivar -> ivar -> ivar -> int_arith.
  
(* This is kind of an awkward definition. *)
Definition eval_int_arith arith theta :=
  match arith with
  | Mul x y z => (eval_ivar x theta) = (eval_ivar y theta)*(eval_ivar z theta)
  | Div x y z =>
    (eval_ivar z theta) <> 0 /\ (eval_ivar x theta) = Z.quot (eval_ivar y theta) (eval_ivar z theta)
  end.
*)

Definition ArithConstraint := mkConstraint arith_eq eval_arith_eq.

(* What are the semantics of Div?
   - Round towards zero/round towards -infty?
   - x/0 fails? or x/0 = 0?
   Most sense to have round-towards-zero, x/0 fails. *)
(*
Definition check_int_arith_sol arith theta :=
  match arith with
  | Mul x y z => Z.eqb (eval_ivar x theta) ((eval_ivar y theta)*(eval_ivar z theta))
  | Div x y z =>
    andb (negb (Z.eqb (eval_ivar z theta) 0)) (Z.eqb (eval_ivar x theta) (Z.quot (eval_ivar y theta) (eval_ivar z theta)))
  end.
*)

Fixpoint eval_aexpr_part expr theta :=
  match expr with
    | T t => Some (eval_iterm t theta)
    | Op op x y =>
      binop_pfun op (eval_aexpr_part x theta) (eval_aexpr_part y theta)
  end.
Lemma eval_aexpr_part_sound : forall expr theta r, eval_aexpr_part expr theta = Some r -> eval_aexpr expr theta r.
Proof.
  intros expr theta; induction expr; intro r.
  + unfold eval_aexpr_part, eval_aexpr; intro Hr; inversion Hr; now rewrite H0.
  + unfold eval_aexpr_part, eval_aexpr; fold eval_aexpr_part; fold eval_aexpr.
    remember (eval_aexpr_part expr1 theta) as Ok; remember (eval_aexpr_part expr2 theta) as Ok'.
    unfold binop_pfun, part_of, binop_rel, rel_of; destruct b, Ok, Ok'; intro Hr; try congruence; inversion Hr;
    specialize (IHexpr1 v); specialize (IHexpr2 v0);
    exists v, v0; try intuition.
    rewrite H2 in Hr; simpl in Hr; congruence.
    eqelim (Z.eqb v0 0); try congruence.
Qed.
    
Definition check_arith_sol arith theta :=
  match eval_aexpr_part (snd arith) theta with
    | None => false
    | Some r => Z.eqb r (eval_iterm (fst arith) theta)
  end.
Lemma check_arith_sol_valid : forall arith theta, check_arith_sol arith theta = true -> eval_arith_eq arith theta.
Proof.
  intros arith theta.
  unfold check_arith_sol, eval_arith_eq.
  eqelim (eval_aexpr_part (snd arith) theta).
  intro Hb; apply eval_aexpr_part_sound.
  rewrite Z.eqb_eq in Hb.
  congruence.
  intros; congruence.
Qed.

Definition check_int_arith arith ds :=
  unsatb_db (db_meet (range_of_dom (term_dom ds (fst arith))) (db_of_aexpr (snd arith) ds)).
Lemma check_int_arith_valid : forall arith ds, check_int_arith arith ds = true -> cst_is_unsat ArithConstraint arith ds.
Proof.
  intros arith ds; unfold check_int_arith, cst_is_unsat, eval; simpl; unfold eval_arith_eq; destruct arith; simpl.
  intros Hu theta Hds He.
  rewrite unsatb_db_true_iff in Hu.
  unfold unsat_db in Hu.
  assert (sat_dbound (db_meet (range_of_dom (term_dom ds i)) (db_of_aexpr a ds)) (eval_iterm i theta)).
  apply db_sat_impl_meet; split.
  apply term_dom_valid; assumption.
  apply db_of_aexpr_spec with (theta := theta); try assumption.
  specialize (Hu (eval_iterm i theta)); contradiction.
Qed.

Definition ArithCheck :=
  mkUnsatChecker ArithConstraint (check_int_arith) (check_int_arith_valid).

(*
Definition ArithDbnd := DomboundedConstraint ArithConstraint.
Definition ArithDbndCheck := DomboundedDBCheck ArithConstraint ArithDSet.
*)

(*
Definition check_int_arith arith (ds : domset) :=
  match arith with
  | Mul x y z =>
    unsatb_db
      (db_meet
         (db_from_dom x ds)
         (arith_ops.db_mul (db_from_dom y ds) (db_from_dom z ds)))
  | Div x y z => negb (arith_ops.db_div_check (db_from_dom x ds) (db_from_dom y ds) (db_from_dom z ds))
  end.
*)

(*
Theorem check_int_arith_valid :
  forall (arith : int_arith) (ds : domset),
    check_int_arith arith ds = true -> cst_is_unsat ArithConstraint arith ds.
Proof.
  unfold ArithConstraint, cst_is_unsat.
  unfold eval_int_arith, check_int_arith; destruct arith; simpl in *;
    intros; try discriminate.
  rewrite unsatb_db_true_iff in H.
(*   apply evalclause_contra; intros. *)

  assert (Hx := H0); apply db_from_dom_valid with (x := i) in Hx.
  assert (Hy := H0); apply db_from_dom_valid with (x := i0) in Hy.
  assert (Hz := H0); apply db_from_dom_valid with (x := i1) in Hz.
  remember (db_from_dom i ds) as ix.
  remember (db_from_dom i0 ds) as iy.
  remember (db_from_dom i1 ds) as iz.
  assert (Hyz := arith_ops.db_mul_sound iy iz (eval_ivar i0 theta) (eval_ivar i1 theta)).
  assert (Hmeet := db_sat_impl_meet ix (arith_ops.db_mul iy iz) (eval_ivar i theta)).
  assert (sat_dbound (db_meet ix (arith_ops.db_mul iy iz)) (eval_ivar i theta)).
  apply Hmeet; split; try assumption.
    rewrite H1. apply arith_ops.db_mul_sound; try assumption.
  unfold unsat_db in H. now apply H in H2.

  remember (eval_ivar i0 theta) as k; remember (eval_ivar i1 theta) as k'.
  assert (Hsk := H0); apply db_from_dom_valid with (x := i) in Hsk.
  assert (Hsk' := H0); apply db_from_dom_valid with (x := i0) in Hsk'.
  assert (Hskk' := H0); apply db_from_dom_valid with (x := i1) in Hskk'.
  remember (db_from_dom i ds) as x; remember (db_from_dom i0 ds) as y;
    remember (db_from_dom i1 ds) as z.
  destruct H1 as [Hz Hq].
  assert (Hf := arith_ops.db_div_check_sound x y z k k').
  apply negb_true_iff in H.
  assert (arith_ops.db_div_check x y z = true).
  apply Hf; [assumption | rewrite Heqk | rewrite Heqk' | rewrite <- Hq]; assumption.
  congruence.
Qed.

Definition ArithCheck := mkUnsatChecker ArithConstraint (check_int_arith) (check_int_arith_valid).
*)

(*
Definition check_int_arith_dbfun arith (f : dbfun) :=
  match arith with
  | Mul x y z =>
    unsatb_db
      (db_meet (f x)
         (arith_ops.db_mul (f y) (f z)))
  | Div x y z => negb (arith_ops.db_div_check (f x) (f y) (f z))
  end.

Theorem check_int_arith_dbfun_valid : forall (c : int_arith) (f : dbfun) (cl : clause),
  is_domset_dbfun f cl /\ check_int_arith_dbfun c f = true ->
    implies (eval_int_arith c) (eval_clause cl).
Proof.
  unfold check_int_arith; unfold is_domset_dbfun in *.
  intros; apply check_int_arith_valid; destruct H.
  unfold check_int_arith_dbfun in H0; unfold check_int_arith.
  destruct c; try tauto; try contradiction.

  now rewrite <- (H i), <- (H i0), <- (H i1); congruence. 
  now rewrite <- (H i), <- (H i0), <- (H i1); congruence. 
Qed.
 
Definition ArithDSet :=
  mkDomDBCheck ArithConstraint (check_int_arith_dbfun) (check_int_arith_dbfun_valid).
Definition ArithDbnd := DomboundedConstraint ArithConstraint.
Definition ArithDbndCheck := DomboundedDBCheck ArithConstraint ArithDSet.

Definition ArithDomCheck :=
  CheckOfDomDBCheck ArithDbnd (ArithDbndCheck).

Definition check_arith_dbnd (a : int_arith) (ds : domset) (cl : clause) :=
  (check ArithDbnd ArithDomCheck) (ds, a) cl.

Definition check_reif_arith_dbnd (r : lit) (a : int_arith) (ds : domset) (cl : clause) :=
  (check (reif.ReifiedConstraint ArithDbnd) (reif.ReifiedCheck ArithDbnd ArithDomCheck)) (r, (ds, a)) cl.
*)

(*
Theorem eval_int_arith_sol_valid :
    forall arith theta,
      (check_int_arith_sol arith theta = true) -> eval_int_arith arith theta.
Proof.
  intros arith theta; unfold check_int_arith_sol, eval_int_arith; destruct arith;
    [now rewrite Z.eqb_eq |
     rewrite andb_true_iff; rewrite negb_true_iff; rewrite Z.eqb_eq].
  intro H; destruct H as [H0 Hquot].
  split; [intro Heq ; rewrite <- Z.eqb_eq in Heq; now rewrite Heq in H0 | assumption].
Qed.
*)

Definition ArithSolCheck := mkSolChecker ArithConstraint check_arith_sol check_arith_sol_valid.
