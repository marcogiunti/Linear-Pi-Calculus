Require Import
        Bool List Lia PeanoNat Classical
        ListAddOns
        pairEq pi_syntax type_system.

Require Import CpdtTactics LibTactics.



Lemma ltb_nlt: forall n m, (n <? m) = false -> m <= n.
Proof.
  induction n; destruct m; intros ; auto using le_n_S; discriminate.
Qed.

Lemma cons_max: forall a1 a2 l n,
    max ((a1, a2) :: l) <= n ->
    a2 <= n.
Proof with eauto.
  introv MAX; simpl in *;
    case_eq(a2 <? max l ); intros;
  try rewrite H in *;
  try rewrite Nat.ltb_lt in *;
  lia...
Qed.



Lemma max_cons: forall a l,
    max l <= max (a :: l).
Proof with eauto.
  intros.
  induction l.
  unfold max... lia.
  unfold max... fold max.
  destruct a, a0.
  case_eq (n2 <? max l); intros. 
  case_eq (n0 <? max l); intros.
  lia.
  unfold max at 2 in IHl; fold max in IHl.
  rewrite H0 in IHl...
  unfold max at 2 in IHl; fold max in IHl.
  case_eq ( n0 <? max l); intros.
  rewrite H0 in IHl...
  case_eq (n0 <? n2); intros...
  rewrite Nat.ltb_ge in H1...
  case_eq (n0 <? n2); intros...
  rewrite Nat.ltb_ge in H1...
Qed.


Lemma max_cont a1 a2 f t g M:
  max(domain((a1,a2, f,t)::g))<= M ->
  max(domain g) <= M.
Proof with eauto.
  introv MAX;
  simpl in MAX; case_eq (a2<?max (domain g));
    intros EQ3; try rewrite EQ3 in *...
  eapply ltb_nlt in EQ3; lia...
Qed.


Lemma rewrite_max_var : forall x v t g,
    snd x < max (domain g) ->
    max (domain g) = max (domain ((x, v, t) :: g)).
Proof with lia.
  introv LT; induction g; destruct x as [x1 x2];
    simpl in *; intuition;
      try destruct a as [[[a1 a2]f1]t1].
  try rewrite <-Nat.ltb_lt in *;
    try rewrite LT...
Qed.


Lemma max_app : forall l1 l2,
    max (l1 ++ l2) =
    if max l1 <? max l2 then max l2 else max l1.
Proof with eauto.
  intros. induction l1 as [|[a1 a2] l1 IHl1].
  rewrite app_nil_l; unfold Nat.ltb; simpl.
  destruct (max l2)...
  assert (EQ: ((a1, a2) :: l1) ++ l2 = (a1, a2) :: (l1 ++ l2))...
  rewrite EQ; simpl. rewrite IHl1.
  simpl.
  case_eq (max l1 <? max l2). intros. 
  case_eq (a2 <? max l2 ). intros.
  case_eq (a2 <? max l1). intros; rewrite H...
  intros; rewrite H0...
  intros.
  case_eq (a2 <? max l1). intros; rewrite H...
  rewrite Nat.ltb_ge in H0; rewrite Nat.ltb_lt in H1;rewrite Nat.ltb_lt in H; lia.
  intros; rewrite H0...

  intros.
  case_eq (a2 <? max l1). intros; rewrite H...
  intros. 
  case_eq (a2 <? max l2 ). intros.
  rewrite Nat.ltb_ge in H0; rewrite Nat.ltb_lt in H1;rewrite Nat.ltb_ge in H; lia.
  eauto.
Qed.

Lemma max_app_l: forall l1 l2 l,
      max (l1 ++ l2) <= max l ->
      max l1 <= max l.
  Proof with eauto.
    intros.
    rewrite max_app in H.
    case_eq (max l1 <? max l2); intros MIN; rewrite MIN in H...
    rewrite Nat.ltb_lt in MIN; lia.
  Qed.

  
  Lemma max_app_r: forall l1 l2 l,
      max (l1 ++ l2) <= max l ->
      max l2 <= max l.
   Proof with eauto.
    intros.
    rewrite max_app in H.
    case_eq (max l1 <? max l2); intros MIN; rewrite MIN in H...
    rewrite Nat.ltb_ge in MIN; lia.
  Qed.

Lemma max_sl_par : forall p q n,
    max (secLabs (dPar p q)) <= n ->
    max (secLabs p) <= n /\
    max (secLabs q) <= n.
Proof with eauto.
  intros. 
  simpl in H. erewrite max_app in H.
  case_eq (max (secLabs q) <? max (secLabs p)); intros...
  rewrite H0 in H; split...
  rewrite Nat.ltb_lt in H0; lia.
  rewrite H0 in H.
  rewrite Nat.ltb_nlt in H0; lia.
Qed.



Lemma max_sl_bang : forall a1 a2  x1 x2 p n,
    max (secLabs (dBang a1 a2 x1 x2 p)) <= n ->
    max (secLabs p) <= n .
Proof with eauto.
  intros; simpl in H...
Qed.

Lemma max_sl_nu : forall a1 a2  p n,
    max (secLabs (dNu a1 a2 p)) <= n ->
    max (secLabs p) <= n .
Proof with eauto.
  intros; simpl in H. erewrite max_app in H...
  case_eq ( max (secLabs p) <? max ((a1, a2) :: nil)); intros.
  rewrite H0 in H.
  rewrite Nat.ltb_lt in H0; lia.
  rewrite H0 in H.
  rewrite Nat.ltb_nlt in H0; lia.
Qed.



Lemma max_in_domain: forall x l,
    max l = x -> x <> 0 ->
    exists y, In (y, x) l.

Proof with eauto.
  intros.
  induction l.
  unfold max in H; intuition.
  destruct a; unfold max in H; fold max in H.
  case_eq (n0 <? max l); intros PEQ.
  rewrite PEQ in H; intuition.
  destruct H1. exists x0.
  rewrite in_app_iff with
      (l := (n, n0) :: nil) (l' := l)...
  rewrite PEQ in H; subst; intuition.
  exists n; apply in_eq.
Qed.

Lemma max_not_in_domain: forall x l,
    max l < x ->
    ~exists y, In (y, x) l.
Proof with eauto.
  intros; intuition.
  destruct H0.
  induction l...
  apply in_inv in H0.
  intuition; subst.
  unfold max in H; fold max in H.
  case_eq (x <? max l); intros MIN; rewrite MIN in H.
  intuition.
  apply Nat.ltb_lt in MIN; intuition.
  lia.
  destruct a; unfold max in H; fold max in H.
  case_eq (n0 <? max l); intros MIN; rewrite MIN in H.
  intuition...
  apply ltb_nlt in MIN.
  intuition.
Qed.

#[global] Hint Resolve max_not_in_domain.

Lemma max_diff_domain : forall m l,
    max m <> max l ->
    exists x,
      (In x m /\ ~ In x l) \/
      (In x l /\ ~ In x m).
Proof with eauto.
  intros.
  case_eq (max m <? max l); intros MLEFT.
  apply Nat.ltb_lt in MLEFT.
  apply max_not_in_domain in MLEFT as NOTIN.
  specialize max_in_domain with
      (x := max l) (l := l) as IN.
  intuition.
  destruct H1.
  exists  (x, max l)...
  apply ltb_nlt in MLEFT.
  assert (MSTRICT : max l < max m) by lia.
  apply max_not_in_domain in MSTRICT as NOTIN.
  specialize max_in_domain with
      (x := max m) (l := m) as IN.
  intuition.
  destruct H1.
  exists  (x, max m)...
Qed.


#[global] Hint Resolve max_diff_domain.

Lemma max_same_domain : forall m l,
    (forall x, In x m <-> In x l) ->
    max m = max l.
Proof with eauto.
  intros; intuition. apply Peirce; intros ABS.
  apply  max_diff_domain in ABS.
  destruct ABS.
  intuition.
  specialize H with x; intuition.
  specialize H with x; intuition.
Qed.




Lemma  max_removeEntry2: forall b1 b2 g1,
    max (domain (removeEntry (b1, b2) g1)) <= max (domain g1).
Proof with eauto.
  intros. 
  induction g1. simpl...
  destruct a as (((a1 & a2) &f) &t).
  case_eq (pair_eq (a1, a2) (b1, b2)). intros EQ. rewrite <-pairEq_eq in EQ; inversion EQ; subst.
  unfold removeEntry; fold removeEntry; rewrite pairEq_eq_true.
  simpl.
  case_eq ( b2 <? max (domain g1)); intros...
  eapply ltb_nlt...
  intros NEQ. unfold removeEntry; fold removeEntry; rewrite NEQ.
  simpl.
  case_eq (a2 <? max (domain (removeEntry (b1, b2) g1))); intros.
  case_eq (a2 <? max (domain g1)); intros...
  eapply Nat.ltb_lt in H; eapply Nat.ltb_ge in H0; lia.
  case_eq (a2 <? max (domain g1)); intros...
  eapply Nat.ltb_ge in H; eapply Nat.ltb_lt in H0; lia.
Qed.


#[global] Hint Resolve max_removeEntry2.

Lemma max_removeEntry3 : forall x1 x2 g,
    x2 < max (domain g) ->
    max (domain (removeEntry (x1, x2) g)) = max  (domain g).
Proof with eauto.
  intros.
  induction g...
  destruct a as [[[a1 a2] f] t].
  simpl in H.
  case_eq (a2 <? max (domain g)); intros; rewrite H0 in *.
  - eapply IHg in H.
    case_eq (pair_eq (a1, a2) (x1, x2)); intros PEQ.
    + unfold removeEntry; rewrite PEQ; simpl; rewrite H0...
    + unfold removeEntry; fold removeEntry;
        rewrite PEQ; simpl; rewrite H, H0...
  - case_eq (pair_eq (a1, a2) (x1, x2)); intros PEQ.
    rewrite <-pairEq_eq in PEQ; inversion PEQ; subst; lia.
    assert (REM2: max (domain (removeEntry (x1, x2) ((a1, a2, f, t) :: g))) <=
                  max (domain ((a1, a2, f, t) :: g)))...
    assert ( max (domain (removeEntry (x1, x2) ((a1, a2, f, t) :: g))) <  max (domain ((a1, a2, f, t) :: g)) -> False).
    intros ABS; simpl in ABS; rewrite PEQ in ABS; simpl in ABS.
    case_eq (a2 <? max (domain (removeEntry (x1, x2) g))); intros; rewrite H0,H1 in *... rewrite Nat.ltb_lt in H1; lia.
    all:lia.
Qed.

