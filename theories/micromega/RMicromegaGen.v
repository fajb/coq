(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria)                                       *)
(*                                                                      *)
(************************************************************************)

Require Import List OrderedRing.
Require Import RingMicromega.
Require Import Refl.
Require Import QArith.
Require Import Qfield.
Require Import Qreals.
Require Import DeclConstant.
Require Import Ztac.
Require Import QMicromega.
Require Import VarMap.
Require Import micromega.Tauto.

Require Setoid.


Section Make.
  Context {R : Type}.

  Context {rO rI: R}.

  Context {rplus rtimes rminus : R -> R -> R}.

  Context {ropp : R -> R}.

  Context {req rle rlt: R -> R -> Prop}.

  Context {Q2R : Q -> R}.

  Context {E : Type}.

  Context {rpow : R -> E -> R}.

  Context {pow_phi : N -> E}.

  Record LRADecl : Type := mk
    {
    Rsrt : ring_theory rO rI rplus rtimes rminus ropp req;
    Rsor : SOR rO rI rplus rtimes rminus ropp req rle rlt;
    Rsoraddon : SORaddon rO rI rplus rtimes rminus ropp req rle 0%Q 1%Q Qplus Qmult Qminus Qopp Qeq_bool Qle_bool Q2R pow_phi rpow
    }.


  Variable LRA : LRADecl.

  Definition Reval_formula := eval_formula rplus rtimes rminus ropp req rle rlt  Q2R  pow_phi rpow .

  Definition Reval_nformula := eval_nformula rO rplus rtimes req rle rlt  Q2R.


  Definition Reval_formula_rtyp (env: PolEnv R) (k:Tauto.kind) : Formula Q -> Tauto.rtyp k :=
    match k as k' return Formula Q -> Tauto.rtyp k' with
    | Tauto.isProp => Reval_formula env
    | _      => fun f  => true (* this is actually dead code *)
    end.

Definition Rnormalise_kind (A: Type) (k:kind) :=
  match k with
  | Tauto.isProp => Qnormalise A k
  | isBool => fun f _  => nil::nil
  end.

Definition Rnegate_kind (A: Type) (k:kind) :=
  match k with
  | Tauto.isProp => Qnegate A k
  | isBool => fun f _  => nil::nil
  end.


Definition RTautoChecker  (f : BFormula (Formula Q) Tauto.isProp) (w: list QWitness)  : bool :=
  @itauto_checker (Formula Q) (NFormula Q) unit
  qunsat qdeduce
  (Rnormalise_kind unit)
  (Rnegate_kind unit) QWitness (fun cl => QWeakChecker (List.map fst cl)) f w.

  Lemma RTautoChecker_sound : forall f w, RTautoChecker f w = true -> forall env, Tauto.eval_bf  (Reval_formula_rtyp env)  f.
  Proof.
    intros f w.
    unfold RTautoChecker.
    apply Tauto.itauto_checker_sound  with (eval:= Reval_formula_rtyp) (eval':= Reval_nformula).
    - intros until env.
      unfold eval_nformula. unfold RingMicromega.eval_nformula.
      destruct t.
      apply (check_inconsistent_sound (Rsor LRA) (Rsoraddon LRA)) ; auto.
    - unfold qdeduce. intros. revert H. apply (nformula_plus_nformula_correct (Rsor LRA) (Rsoraddon LRA));auto.
    - intros.
      destruct k ; simpl; auto.
      revert H.
      now apply (cnf_normalise_correct (Rsor LRA) (Rsoraddon LRA)).
    - intros. rewrite Tauto.hold_eNOT. destruct k ; simpl ; auto.
      now eapply (cnf_negate_correct (Rsor LRA) (Rsoraddon LRA));eauto.
      unfold eval_cnf in H. simpl in H. unfold eval_clause in H. simpl in H.
      tauto.
    - intros l cm H env0.
      unfold Reval_nformula.
      unfold  QWeakChecker in H.
      apply (checker_nf_sound (Rsor LRA) (Rsoraddon LRA) (List.map fst l) cm) with (env:= env0) in H.
      rewrite make_impl_map with (eval := Reval_nformula env0);auto.
      unfold Reval_nformula, Tauto.eval_tt; tauto.
  Qed.

End Make.

Register RTautoChecker_sound   as lra.thm.
Register RTautoChecker         as lra.checker.
Register VarMap.find           as lra.find.




(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
