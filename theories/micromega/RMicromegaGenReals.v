Require Import RMicromegaGen.
Require Import RMicromega.
Require Import LraGen.


Definition LRAR :=
  mk Rsrt Rsor QSORaddon.
Add LRA LRAR.

Require Import Rdefinitions Qreals.
Open Scope R_scope.

Goal forall (x y:R), x + y = y + x.
Proof.
  intros.
  lra. (* redefined by LraGen *)
Qed.

Goal forall x, 2 * x = x + x.
Proof.
  intros.
  Fail lra. (* IZR 2 is parsed as a variable *)
Abort.

Goal forall x, Q2R (2#1) * x = x + x.
Proof.
  intros.
  lra.
Qed.

Goal forall x, x >= Q2R (2#1) -> x >= Q2R (1#1).
Proof.
  intros.
  Fail lra. (* >= is not a known operator only <= and < *)
Abort.

Goal forall x, Q2R (2#1) <= x  -> Q2R (1#1) <= x.
Proof.
  intros.
  lra.
Qed.
