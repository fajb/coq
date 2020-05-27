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

Require Import OrderedRing.
Require Import RingMicromega.
Require Import Refl.
Require Import QArith.
Require Import Qfield.
Require Import Qreals.
Require Import DeclConstant.
Require Import Ztac.
Require Import QMicromega.
Require Import VarMap.

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

  Lemma RTautoChecker_sound : forall f w, QTautoChecker f w = true -> forall env, Tauto.eval_bf  (Reval_formula env)  f.
  Proof.
    intros f w TC env.
    apply Tauto.tauto_checker_sound with (eval:=Reval_formula) (eval':=    Reval_nformula) (env := env) in TC; auto.
    - intros. apply (eval_nformula_dec (Rsor LRA) Q2R).
    - destruct t. unfold Reval_nformula, eval_nformula.
      intros qunsat env0.
      apply (check_inconsistent_sound (Rsor LRA) (Rsoraddon LRA)) ; auto.
  - intros. revert H.
    eapply (nformula_plus_nformula_correct (Rsor LRA) (Rsoraddon LRA)); eauto.
  - now apply (cnf_normalise_correct (Rsor LRA) (Rsoraddon LRA)).
  - intros. now eapply (cnf_negate_correct (Rsor LRA) (Rsoraddon LRA)); eauto.
  - intros l cm H env0.
    unfold Reval_nformula.
    unfold  QWeakChecker in H.
    apply (checker_nf_sound (Rsor LRA) (Rsoraddon LRA) (List.map fst l) cm) with (env:= env0) in H.
    rewrite make_impl_map with (eval := Reval_nformula env0);auto.
    unfold Reval_nformula, Tauto.eval_tt; tauto.
  Qed.

End Make.

Register RTautoChecker_sound   as lra.thm.
Register QTautoChecker         as lra.checker.
Register VarMap.find           as lra.find.




(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
