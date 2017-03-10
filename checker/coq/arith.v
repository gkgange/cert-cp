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

Inductive binop := Plus | Times | Sub | Div | Min | Max.
Inductive unop := Abs | Uminus.

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

Definition unop_fun op :=
  match op with
    | Abs => Z.abs
    | Uminus => Z.opp
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
| Op : binop -> aexpr -> aexpr -> aexpr
| Un : unop -> aexpr -> aexpr.

Fixpoint eval_aexpr exp theta v :=
  match exp with
    | T t => v = eval_iterm t theta
    | Op op x y =>
      exists x' y', eval_aexpr x theta x' /\ eval_aexpr y theta y' /\ binop_rel op v x' y'
    | Un op x =>
      exists x', eval_aexpr x theta x' /\ v = unop_fun op x'
  end.

Definition arith_eq := (iterm * aexpr)%type.
Definition eval_arith_eq aeq theta := eval_aexpr (snd aeq) theta (eval_iterm (fst aeq) theta).
Definition eval_arith_neq ane theta := exists v, eval_aexpr (snd ane) theta v /\ v <> (eval_iterm (fst ane) theta).

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

Definition db_of_unop op :=
  match op with
    | Abs => arith_ops.db_abs
    | Uminus => arith_ops.db_neg
  end.
Lemma db_of_unop_spec : forall op db k, sat_dbound db k -> sat_dbound (db_of_unop op db) (unop_fun op k).
Proof.
  intros op db k Hs; unfold db_of_unop, unop_fun.
  destruct op.
  + apply arith_ops.db_abs_valid; assumption.
  + rewrite <- arith_ops.db_neg_valid; assumption.
Qed.

Fixpoint db_of_aexpr exp ds :=
  match exp with
  | T t => range_of_dom (term_dom ds t)
  | Un op x => db_of_unop op (db_of_aexpr x ds)
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
  + intro Hx; elim Hx; clear Hx; intros x' Hx.
    destruct Hx as [Hx Hf].
    rewrite Hf; apply db_of_unop_spec; apply IHexp; assumption.
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
Definition ArithNE := mkConstraint (iterm * aexpr)%type eval_arith_neq.

(* What are the semantics of Div?
   - Round towards zero/round towards -infty?
   - x/0 fails? or x/0 = 0?
   Most sense to have round-towards-zero, x/0 fails. *)

Fixpoint eval_aexpr_part expr theta :=
  match expr with
    | T t => Some (eval_iterm t theta)
    | Un op x =>
      match eval_aexpr_part x theta with
        | Some k => Some (unop_fun op k)
        | None => None
      end
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
  + unfold eval_aexpr, eval_aexpr_part at 1; fold eval_aexpr; fold eval_aexpr_part; intro Hr.
    eqelim (eval_aexpr_part expr theta); try congruence.
    inversion Hr; clear Hr.
    exists v.
    intuition.
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

Definition check_aneq_sol aneq theta :=
  match eval_aexpr_part (snd aneq) theta with
    | None => false
    | Some r => negb (Z.eqb r (eval_iterm (fst aneq) theta))
  end.
Lemma check_aneq_sol_valid : forall arith theta, check_aneq_sol arith theta = true -> eval_arith_neq arith theta.
Proof.
  intros arith theta.
  unfold check_aneq_sol, eval_arith_neq.
  eqelim (eval_aexpr_part (snd arith) theta).
  intro Hv; rewrite Bool.negb_true_iff in Hv.
  rewrite Z.eqb_neq in Hv.
  exists v.
  split; [apply eval_aexpr_part_sound; assumption | assumption].
  intros; discriminate.
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

Definition check_aneq arith ds :=
  let x := term_dom ds (fst arith) in
  let y := db_of_aexpr (snd arith) ds in
  if orb (dom_unsatb x) (unsatb_db y) then
    true
  else
    match (range_of_dom x), y with
      | (Bounded k, Bounded k'), (Bounded k'', Bounded k''')  =>
          andb (Z.eqb k k') (andb (Z.eqb k k'') (Z.eqb k k'''))
      | _, _ => false
    end.
Lemma check_aneq_valid : forall arith ds, check_aneq arith ds = true -> cst_is_unsat ArithNE arith ds.
Proof.
  intros arith ds.
  unfold check_aneq.
  unfold cst_is_unsat, eval; simpl; unfold eval_arith_neq.
  eqelim (dom_unsatb (term_dom ds (fst arith))); eqelim (unsatb_db (db_of_aexpr (snd arith) ds));
    simpl; intros H theta Hds;
    intro Hv; elim Hv; clear Hv; intros v Hv; destruct Hv as [He Hv].
  + assert (Hc := db_of_aexpr_spec (snd arith) ds theta v).
    specialize (Hc Hds He).
    apply unsatb_db_true_iff in H1.
    specialize (H1 v); contradiction.
  + assert (Ht := term_dom_valid ds theta Hds (fst arith)).
    apply dom_unsatb_unsat in H0; specialize (H0 (eval_iterm (fst arith) theta)); contradiction.
  + assert (Hc := db_of_aexpr_spec (snd arith) ds theta v Hds He).
    apply unsatb_db_true_iff in H1; specialize (H1 v); contradiction.
  + eqelim (range_of_dom (term_dom ds (fst arith)));
    eqelim (db_of_aexpr (snd arith) ds); simpl in *; destruct b, b0, b1, b2; try congruence.
    repeat (apply Bool.andb_true_iff in H;
            let H' := fresh in destruct H as [H' H];
            apply Z.eqb_eq in H'); apply Z.eqb_eq in H.
    rewrite <- H2, <- H5, <- H in *.
    assert (Hse := db_of_aexpr_spec (snd arith) ds theta v Hds He).
    assert (Ht := term_dom_valid ds theta Hds (fst arith)).
    unfold sat_dom in Ht; destruct Ht as [Ht _]; unfold range_of_dom in H3; simpl in *.
    assert (fst (term_dom ds (fst arith)) = (Bounded z, Bounded z)).
      eqelim (term_dom ds (fst arith)).
      rewrite H3; trivial.
    rewrite H6 in *.
    rewrite H4 in Hse.
    unfold sat_dbound in Hse, Ht; simpl in *.
    assert (z = v). omega.
    assert (eval_iterm (fst arith) theta = z). 
    apply Z.le_antisymm; intuition.
    congruence.
Qed.

Definition ArithCheck :=
  mkUnsatChecker ArithConstraint (check_int_arith) (check_int_arith_valid).
Definition ArithNECheck :=
  mkUnsatChecker ArithNE (check_aneq) (check_aneq_valid).

Definition ArithSolCheck := mkSolChecker ArithConstraint check_arith_sol check_arith_sol_valid.
Definition ArithNESolCheck := mkSolChecker ArithNE check_aneq_sol check_aneq_sol_valid.
