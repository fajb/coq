(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
Require Import Bool ZArith.
Require Import ZifyClasses.
Open Scope Z_scope.
(* Instances of [ZifyClasses] for dealing with boolean operators.
   Various encodings of boolean are possible.  One objective is to
   have an encoding that is terse but also lia friendly.
*)

(** [Z_of_bool] is the injection function for boolean *)
Definition Z_of_bool (b : bool) : Z := if b then 1 else 0.

(** [bool_of_Z] is a compatible reverse operation *)
Definition bool_of_Z (z : Z) : bool := negb (Z.eqb z 0).

Lemma Z_of_bool_bound : forall x,   0 <= Z_of_bool x <= 1.
Proof.
  destruct x ; simpl; compute; intuition congruence.
Qed.

Program Instance Inj_bool_Z : InjTyp bool Z :=
  {| inj := Z_of_bool ; pred :=(fun x => 0 <= x <= 1) |}.
Next Obligation.
  apply Z_of_bool_bound.
Qed.
Add InjTyp Inj_bool_Z.


(** Boolean operators *)

Program Instance Op_andb : BinOp andb :=
  {| TBOp := Z.min |}. (* Other encodings are possible *)
Next Obligation.
  destruct n,m; simpl; auto.
Qed.
Add BinOp Op_andb.

Program Instance Op_orb : BinOp orb :=
  {| TBOp := Z.max |}.
Next Obligation.
  destruct n,m; simpl; auto.
Qed.
Add BinOp Op_orb.

Program Instance Op_negb : UnOp negb :=
  {| TUOp := fun x => 1 - x |}.
Next Obligation.
  destruct x; simpl; auto.
Qed.
Add UnOp Op_negb.

Program Instance Op_eq_bool : BinRel (@eq bool) :=
  {| TR := @eq Z |}.
Next Obligation.
  destruct n,m ; simpl;intuition congruence.
Qed.
Add BinRel Op_eq_bool.

Program Instance Op_true : CstOp true :=
  {| TCst := 1 |}.

Program Instance Op_false : CstOp false :=
  {| TCst := 0 |}.


(** Comparisons are encoded using the predicates [isZero] and [isLeZero].*)

Definition isZero (z : Z) := Z_of_bool (Z.eqb z 0).

Definition isLeZero (x : Z) := Z_of_bool (Z.leb x 0).

(* Some intermediate lemma *)

Lemma Z_eqb_isZero : forall n m,
    Z_of_bool (n =? m) = isZero (n - m).
Proof.
  intros ; unfold isZero.
  destruct ( n =? m) eqn:EQ.
  - simpl. rewrite Z.eqb_eq in EQ.
    rewrite EQ. rewrite Z.sub_diag.
    reflexivity.
  -
    destruct (n - m =? 0) eqn:EQ'.
    rewrite Z.eqb_neq in EQ.
    rewrite Z.eqb_eq in EQ'.
    apply Zminus_eq in EQ'.
    congruence.
    reflexivity.
Qed.

Lemma Z_leb_sub : forall x y, x <=? y  = ((x - y) <=? 0).
Proof.
  intros.
  destruct (x <=?y) eqn:B1 ;
    destruct (x - y <=?0) eqn:B2 ; auto.
  - rewrite Z.leb_le in B1.
    rewrite Z.leb_nle in B2.
    rewrite Z.le_sub_0 in B2. tauto.
  - rewrite Z.leb_nle in B1.
    rewrite Z.leb_le in B2.
    rewrite Z.le_sub_0 in B2. tauto.
Qed.

Lemma Z_ltb_leb : forall x y, x <? y  = (x +1 <=? y).
Proof.
  intros.
  destruct (x <?y) eqn:B1 ;
    destruct (x + 1 <=?y) eqn:B2 ; auto.
  - rewrite Z.ltb_lt in B1.
    rewrite Z.leb_nle in B2.
    apply Zorder.Zlt_le_succ in B1.
    unfold Z.succ in B1.
    tauto.
  - rewrite Z.ltb_nlt in B1.
    rewrite Z.leb_le in B2.
    apply Zorder.Zle_lt_succ in B2.
    unfold Z.succ in B2.
    apply Zorder.Zplus_lt_reg_r in B2.
    tauto.
Qed.


(** Comparison over Z *)

Program Instance Op_Zeqb : BinOp Z.eqb :=
  {| TBOp := fun x y => isZero (Z.sub x y) |}.
Next Obligation.
  apply Z_eqb_isZero.
Qed.

Program Instance Op_Zleb : BinOp Z.leb :=
  {| TBOp := fun x y => isLeZero (x-y) |}.
Next Obligation.
  unfold isLeZero.
  rewrite Z_leb_sub.
  auto.
Qed.
Add BinOp Op_Zleb.

Program Instance Op_Zgeb : BinOp Z.geb :=
  {| TBOp := fun x y => isLeZero (y-x) |}.
Next Obligation.
  unfold isLeZero.
  rewrite Z.geb_leb.
  rewrite Z_leb_sub.
  auto.
Qed.
Add BinOp Op_Zgeb.

Program Instance Op_Zltb : BinOp Z.ltb :=
  {| TBOp := fun x y => isLeZero (x+1-y) |}.
Next Obligation.
  unfold isLeZero.
  rewrite Z_ltb_leb.
  rewrite <- Z_leb_sub.
  reflexivity.
Qed.
Add BinOp Op_Zltb.

Program Instance Op_Zgtb : BinOp Z.gtb :=
  {| TBOp := fun x y => isLeZero (y-x+1) |}.
Next Obligation.
  unfold isLeZero.
  rewrite Z.gtb_ltb.
  rewrite Z_ltb_leb.
  rewrite Z_leb_sub.
  rewrite Z.add_sub_swap.
  reflexivity.
Qed.
Add BinOp Op_Zgtb.

(** Comparison over nat *)


Lemma Z_of_nat_eqb_iff : forall n m,
  (n =? m)%nat = (Z.of_nat n =? Z.of_nat m).
Proof.
  intros.
  rewrite Nat.eqb_compare.
  rewrite Z.eqb_compare.
  rewrite Nat2Z.inj_compare.
  reflexivity.
Qed.

Lemma Z_of_nat_leb_iff : forall n m,
  (n <=? m)%nat = (Z.of_nat n <=? Z.of_nat m).
Proof.
  intros.
  rewrite Nat.leb_compare.
  rewrite Z.leb_compare.
  rewrite Nat2Z.inj_compare.
  reflexivity.
Qed.

Lemma Z_of_nat_ltb_iff : forall n m,
  (n <? m)%nat = (Z.of_nat n <? Z.of_nat m).
Proof.
  intros.
  rewrite Nat.ltb_compare.
  rewrite Z.ltb_compare.
  rewrite Nat2Z.inj_compare.
  reflexivity.
Qed.


Program Instance Op_nat_eqb : BinOp Nat.eqb :=
  {| TBOp := fun x y => isZero (Z.sub x y) |}.
Next Obligation.
  rewrite  <- Z_eqb_isZero.
  f_equal. apply Z_of_nat_eqb_iff.
Qed.
Add BinOp Op_nat_eqb.

Program Instance Op_nat_leb : BinOp Nat.leb :=
  {| TBOp := fun x y => isLeZero (x-y) |}.
Next Obligation.
  rewrite Z_of_nat_leb_iff.
  unfold isLeZero.
  rewrite Z_leb_sub.
  auto.
Qed.
Add BinOp Op_nat_leb.

Program Instance Op_nat_ltb : BinOp Nat.ltb :=
  {| TBOp := fun x y => isLeZero (x+1-y) |}.
Next Obligation.
  rewrite Z_of_nat_ltb_iff.
  unfold isLeZero.
  rewrite Z_ltb_leb.
  rewrite <- Z_leb_sub.
  reflexivity.
Qed.
Add BinOp Op_nat_ltb.

(** Injected boolean operators *)

Lemma Z_eqb_ZSpec_ok : forall x,  x <> isZero x.
Proof.
  intros.
  unfold isZero.
  destruct (x =? 0) eqn:EQ.
  -  apply Z.eqb_eq in EQ.
     simpl. congruence.
  - apply Z.eqb_neq in EQ.
    simpl. auto.
Qed.

Program Instance Z_eqb_ZSpec : UnOpSpec isZero :=
  {| UPred := fun n r => n <> r ; USpec := Z_eqb_ZSpec_ok |}.
Add Spec Z_eqb_ZSpec.

Lemma leZeroSpec_ok : forall x,  x <= 0 /\ isLeZero x = 1 \/ x > 0 /\ isLeZero x = 0.
Proof.
  intros.
  unfold isLeZero.
  destruct (x <=? 0) eqn:EQ.
  -  apply Z.leb_le in EQ.
     simpl. intuition congruence.
  -  simpl.
     apply Z.leb_nle in EQ.
     apply Zorder.Znot_le_gt in EQ.
     tauto.
Qed.

Instance leZeroSpec : UnOpSpec isLeZero :=
  {| UPred := fun n r => (n<=0 /\ r = 1) \/ (n > 0 /\ r = 0) ; USpec := leZeroSpec_ok|}.
Add Spec leZeroSpec.
