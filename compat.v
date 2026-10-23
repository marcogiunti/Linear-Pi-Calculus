(* Compatibility layer for porting the development from Coq 8.8 to Rocq 9.2. *)

From Stdlib Require Import PeanoNat Lia.

(* Coq 8.8's [Omega] re-exported [ZArith_base], which re-exported
   [Arith_base]; proofs rely on the names and hints these provided. *)
From Stdlib Require Export ZArith_base Arith_base.

(* Rocq 9.2 closes [intuition] goals with [auto] only;
   Coq 8.8 used [auto with *]. Restore the old behaviour. *)
Ltac Tauto.intuition_solver ::= auto with *.

(* Hints registered by Coq 8.8's [Omega], with [lia] in place of [omega]. *)
#[global] Hint Extern 10 (_ = _ :>nat) => abstract lia: zarith.
#[global] Hint Extern 10 (_ <= _) => abstract lia: zarith.
#[global] Hint Extern 10 (_ < _) => abstract lia: zarith.
#[global] Hint Extern 10 (_ >= _) => abstract lia: zarith.
#[global] Hint Extern 10 (_ > _) => abstract lia: zarith.
#[global] Hint Extern 10 (_ <> _ :>nat) => abstract lia: zarith.
#[global] Hint Extern 10 (~ _ <= _) => abstract lia: zarith.
#[global] Hint Extern 10 (~ _ < _) => abstract lia: zarith.
#[global] Hint Extern 10 (~ _ >= _) => abstract lia: zarith.
#[global] Hint Extern 10 (~ _ > _) => abstract lia: zarith.
#[global] Hint Extern 10 False => abstract lia: zarith.

(* Names removed from the standard library since Coq 8.8, with their
   original statements. *)
Notation beq_nat := Nat.eqb (only parsing).

Lemma beq_nat_refl : forall n, true = beq_nat n n.
Proof. intro n. symmetry. apply Nat.eqb_refl. Qed.

Lemma beq_nat_true : forall n m, beq_nat n m = true -> n = m.
Proof. intros n m. apply Nat.eqb_eq. Qed.

Notation le_trans := Nat.le_trans (only parsing).
