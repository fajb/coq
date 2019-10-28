(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import ZifyClasses.
Require Export ZifyInst.
Require Import InitialRing.
Require Import Tify.
Declare ML Module "zify_plugin".

(** [zify_post_hook] is there to be redefined. *)
Ltac zify_post_hook := idtac.

Ltac zify := tify_op BinInt.Z; (iter_specs applySpec) ; zify_post_hook.
