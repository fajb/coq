Require Import ZArith.
Require Import Lia.

Lemma bug_9848 : True.
Proof.
  do 1000 pose proof I.
  Timeout 1 Lia.lia. (* fast *)
Timeout 1 Qed. (* Qed is wall-clock slow but Time Qed says otherwise *)


Axiom decompose_nat : nat -> nat -> nat.
Axiom inleft : forall {P}, {m : nat & P m} -> nat.
Axiom foo : nat.

Lemma bug_7886 : forall (x x0 : nat)
  (e : 0 = x0 + S x)
  (H : decompose_nat x 0 = inleft (existT (fun m : nat => 0 = m + S x) x0 e))
  (x1 : nat)
  (e0 : 0 = x1 + S (S x))
  (H1 : decompose_nat (S x) 0 = inleft (existT (fun m : nat => 0 = m + S (S x)) x1 e0)),
    False.
Proof.
  intros.
  lia.
Qed.

Lemma bug_8898 : forall (p : 0 < 0) (H: p = p), False.
Proof.
  intros p H. lia.
Qed.

Open Scope Z_scope.

Lemma two_x_eq_1 : forall x, 2 * x = 1 -> False.
Proof.
  intros.
  lia.
Qed.


Lemma two_x_y_eq_1 : forall x y, 2 * x + 2 * y = 1 -> False.
Proof.
  intros. 
  lia.
Qed.

Lemma two_x_y_z_eq_1 : forall x y z, 2 * x + 2 * y + 2 * z= 1 -> False.
Proof.
  intros.
  lia.
Qed.

Lemma unused : forall x y, y >= 0 /\ x = 1 -> x = 1.
Proof.
  intros x y.
  lia.
Qed.

Lemma omega_nightmare : forall x y, 27 <= 11 * x + 13 * y <= 45 ->  -10 <= 7 * x - 9 * y <= 4 -> False.
Proof.
  intros ; intuition auto.
  lia.
Qed.

Lemma compact_proof : forall z,
 (z < 0) ->
 (z >= 0) ->
  (0 >= z \/ 0 < z) -> False.
Proof.
 intros.
 lia.
Qed.

Lemma dummy_ex : exists (x:Z),  x = x.
Proof.
  eexists.
  lia.
  Unshelve.
  exact Z0.
Qed.

Lemma unused_concl : forall x,
    False -> x > 0 -> x < 0.
Proof.
  intro.
  lia.
Qed.

Lemma unused_concl_match : forall (x:Z),
    False -> match x with
             | Z0 => True
             | _ => x = x
             end.
Proof.
  intros.
  lia.
Qed.

Lemma fresh : forall (__arith : Prop),
    __arith -> True.
Proof.
  intros.
  lia.
Qed.

Class Foo {x : Z} := { T : Type ; dec : T -> Z }.
Goal forall bound {F : @Foo bound} (x y : T), 0 <= dec x < bound -> 0 <= dec y 
< bound -> dec x + dec y >= bound -> dec x + dec y < 2 * bound.
Proof.
  intros.
  lia.
Qed.

Section S.
  Variables x y: Z.
  Variables XGe : x >= 0.
  Variables YGt : y > 0.
  Variables YLt : y < 0.

  Goal False.
  Proof using - XGe.
    lia.
  Qed.

  Goal False.
  Proof using YGt YLt x y.
    lia.
  Qed.

  End S.

(*  Bug 5073 *)
Lemma opp_eq_0_iff a : -a = 0 <-> a = 0.
Proof.
  lia.
Qed.

Lemma ex_pos : forall x, exists z t, x = z - t /\ z >= 0 /\ t >= 0.
Proof.
  intros.
  destruct (dec_Zge x 0).
  exists x, 0.
  lia.
  exists 0, (-x).
  lia.
Qed.

Goal forall
    (b q r : Z)
    (H : b * q + r <= 0)
    (H5 : - b < r)
    (H6 : r <= 0)
    (H2 : 0 <= b),
  b = 0 -> False.
Proof.
  intros b q r.
  lia.
Qed.
