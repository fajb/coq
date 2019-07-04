(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open Constrexpr
module InjTable : sig val register : constr_expr -> unit end
module UnOp     : sig val register : constr_expr -> unit end
module BinOp    : sig val register : constr_expr -> unit end
module CstOp    : sig val register : constr_expr -> unit end
module BinRel   : sig val register : constr_expr -> unit end
module PropOp   : sig val register : constr_expr -> unit end
module Spec     : sig val register : constr_expr -> unit end
module Saturate : sig val register : constr_expr -> unit end

val zify_tac : unit Proofview.tactic
val saturate : unit Proofview.tactic
val iter_specs : (EConstr.t -> unit Proofview.tactic) -> unit Proofview.tactic

val print_zify_types : unit -> unit
val print_zify_binop : unit -> unit
val print_zify_unop  : unit -> unit
val print_zify_cst   : unit -> unit
val print_zify_binrel: unit -> unit
val print_zify_spec  : unit -> unit
