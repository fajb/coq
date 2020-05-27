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
Require Import RingMicromega.
Require Import VarMap.
Require Coq.micromega.Tauto.
Declare ML Module "micromega_plugin".


Ltac lra := lra_g.



(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
