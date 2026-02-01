Require Import
        Bool List Omega PeanoNat.

Notation name  := nat.

(* Decidable equivalence on channels *)
Lemma nat_pair_eq_dec : forall n m : name * name,
    {n = m} + {n <> m}.
Proof.
  decide equality. decide equality. decide equality.
Qed. 

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
      set (x := name); move_to_top x
    | assert_eq x name; move_to_top x
    | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.