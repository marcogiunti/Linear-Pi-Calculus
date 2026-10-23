Require Import
        Bool List Lia PeanoNat
        header operations.

Require Import CpdtTactics LibTactics.

Section PairEq.

  Definition pair_eq (p1 p2 : name * name) :=
    (fst p1 =? fst p2) && (snd p1 =? snd p2).

  Hint Unfold pair_eq.
  
  Lemma pairEq_eq: forall p1 p2 : name*name,
      p1 = p2 <->  pair_eq p1 p2 = true.
  Proof with eauto.
    intuition.
    unfold pair_eq; fold pair_eq; simpl...
    assert (a = a0 /\ b = b0); apply projections_injective in H; simpl...
    destruct H0; subst...
    clear H.
    specialize beq_nat_refl with a0 as BNR1.
    specialize beq_nat_refl with b0 as BNR2.
    intuition.
    unfold pair_eq in H; fold pair_eq in H; simpl...
    apply andb_true_iff in H; destruct H.
    unfold fst in H; unfold snd in H0.
    specialize beq_nat_true with a a0 as BNR1.
    specialize beq_nat_true with b b0 as BNR2.
    intuition.
  Qed.

  Lemma pairEq_neq: forall p1 p2 : name*name,
      p1 <> p2 <->  pair_eq p1 p2 = false.
  Proof.
    intros. split.
    - intros. assert (p1 = p2 -> False) by auto.
      rewrite pairEq_eq in H0.
      assert ({pair_eq p1 p2 = true} + {pair_eq p1 p2 = false}); intuition.
    - intros. assert (not (not (pair_eq  p1 p2 = false))) by auto.
      specialize pairEq_eq with p1 p2; intros; auto.
      assert ( p1 = p2-> False); intros.
      apply H1 in H2. rewrite H2 in H. inversion H.
      auto.
  Qed.
  
  Lemma pair_equal_spec :
    forall (A B : Type) (a1 a2 : A) (b1 b2 : B),
      (a1, b1) = (a2, b2) <-> a1 = a2 /\ b1 = b2.
  Proof with auto.
    split; intros.
    - split.
      + replace a1 with (fst (a1, b1)); replace a2 with (fst (a2, b2))...
        rewrite H...
      + replace b1 with (snd (a1, b1)); replace b2 with (snd (a2, b2))...
        rewrite H...
    - destruct H; subst...
  Qed.

  
  Lemma pairEq_eq_true : forall b1 b2,
      (pair_eq (b1, b2) (b1, b2) = true).
  Proof.
    intros. apply pairEq_eq.
    tauto.
  Qed.
  

  Fixpoint In2 a l :=
    match l with
    | nil => false 
    | b :: m =>
      if pair_eq a b then true else In2 a m
    end.

  
  
  Lemma in2_In_iff: forall x l,
      In2 x l = true <-> In x l.
  Proof with eauto.
    intuition; induction l; inv H;
      try case_eq (pair_eq (a, b) a0); intros;
        try rewrite <-pairEq_eq in *;
        subst;
        try rewrite H in *; simpl;
          try rewrite pairEq_eq_true;
          try rewrite H...
  Qed.

  Lemma in2_implies_in: forall x l,
      In2 x l = true -> In x l.
  Proof with eauto.
    intuition. apply in2_In_iff...
  Qed.

  Hint Resolve in2_implies_in.

 


  Lemma in2_nIn_iff: forall x l,
      In2 x l = false <-> ~In x l.
  Proof with eauto using in2_In_iff.
    intuition; try rewrite <-in2_In_iff in *;
      try rewrite H0 in *; try discriminate...
    case_eq ( In2 (a, b) l); intros; try rewrite in2_In_iff in *; intuition...
  Qed. 

End PairEq.
