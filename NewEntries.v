Require Import
        Bool List Lia PeanoNat Program.Equality
        ListAddOns Max RemoveEntry Domain
        header
        operations pi_syntax 
        pairEq type_system semantics
        proposition27
        disjoint_newEntries
        type_operations_1.

Require Import CpdtTactics LibTactics.


Lemma newEntries_iff g1 g2 l M (nd_pf1 : NoDup (domain g1))
      (nd_pf2: NoDup (domain g2)):
  (forall x, In x g1 <-> In x g2) ->
  newEntries g1 l M =  newEntries g2 l M.
Proof with eauto using no_dup_isMap.
  introv IFF.
  induction l...
  destruct a as[a1 a2].
  simpl.
  case_eq (InB (a1, a2) g1). introv INB.
  destruct b.
  eapply inB_implies_In_2,IFF in INB;
    try eapply  in_implies_InB in INB;
    try rewrite INB...
  case_eq (InB (a1, a2) g2); introv ABS.
  destruct b.
  eapply inB_implies_In_2,IFF in ABS;
    try eapply  in_implies_InB in ABS;
    try rewrite ABS in INB; inv INB...
  
  case_eq (InB (a1, a2 - M) g1); introv INB1.
  destruct b.
  eapply inB_implies_In_2,IFF in INB1;
    try eapply  in_implies_InB in INB1;
    try rewrite INB1; simpl in *;
    try rewrite IHl...
  case_eq (InB (a1, a2 - M) g2). introv ABS2.
  destruct b.
   eapply inB_implies_In_2,IFF in ABS2;
    try eapply  in_implies_InB in ABS2;
     try rewrite ABS2 in INB1; inv INB1...
   destruct p1, p2;
     eapply InB_false in INB1;
     eapply InB_false in ABS2;
     intuition; subst;simpl;
   try rewrite IHl...
Qed.

Lemma newEntries_cons :
    forall b1 b2 f1 t1 p g1 nd_pf1,
      b2 <= max (domain  g1) ->
      sl_pos p ->
      ~In (b1, b2) (secLabs p) ->
      newEntries g1 (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1)) =
      newEntries ((b1, b2, f1, t1) :: removeEntry (b1, b2) g1)
                 (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1)).
Proof with eauto.
  intros b1 b2 f1 t1 p g1 nd_pf1 IN SLP NIN.
  erewrite identif_seclabs_of_dep_relabel.
  unfold sl_pos,pos in SLP.
  induction (secLabs p).
  rewrite map_nil_eq; unfold newEntries; fold newEntries...
  rewrite map_cons.
  destruct a as [a1 a2].
  assert (EQ1 : a1 = fst (a1, a2)). simpl...
  assert (EQ2 : a2 = snd (a1, a2)). simpl...
  rewrite <-EQ1, <-EQ2.
  unfold newEntries; fold newEntries.
  case_eq (InB (a1, a2 + max (domain g1)) g1).
  intros. case_eq b; intros; subst.
  
 - eapply inB_implies_In_2 in H.
   eapply in_g_in_domain,proposition27.in_preserves_max in H.
   assert (a2 = 0). lia.
  assert (In (a1, a2) ((a1, a2) :: l))...
  specialize SLP with a1 a2; intuition auto.
  lia.
 - 
   assert (K := H). clear H.
  case_eq (InB (a1, a2 + max (domain g1)) ((b1, b2, f1, t1) :: removeEntry (b1, b2) g1)).
  intros. case_eq b; intros; subst.
   eapply inB_implies_In_2 in H.
  inversion H. inversion H0.
  assert (a2 = 0). lia.
  assert (In (a1, a2) ((a1, a2) :: l))...
  specialize SLP with a1 a2; intuition auto.
  lia.
  eapply in_g_in_domain,proposition27.in_preserves_max in H0.
  assert (max (domain (removeEntry (b1, b2) g1)) <= max (domain g1)). eapply max_removeEntry2...
  assert (a2 = 0). lia.
   assert (In (a1, a2) ((a1, a2) :: l))...
  specialize SLP with a1 a2; intuition auto.
  lia.
  assert (EQ3: a2 + max (domain g1) - max (domain g1) = a2).
  lia. 
  erewrite EQ3,inB_removeEntry.
  assert ((forall x1 x2 : name, In (x1, x2) l -> x2 > 0) ).
  eapply pos_cons...
  assert( ~ In (b1, b2) l). intros ABS.
  assert (In (b1, b2) ((a1, a2):: l)).
  eapply in_cons...
  contradiction.
  intuition.
  rewrite <-H3...
  intros ABS. inversion ABS; subst.
  assert (In (b1, b2) ((b1, b2) :: l))...
  Qed.


Lemma  newEntries_remove0 g1 nd_pf1 l p x1 x2 f t M:
  l = secLabs (dep_relabel p (domain g1) nd_pf1) ->
  M = max (domain  g1) ->
  x2 <= M ->
  sl_pos p ->
  ~ In (x1, x2) (secLabs p) ->
  NoDup (domain ((x1, x2, f, t) :: g1)) ->
  newEntries ((x1, x2, f, t) :: g1) l M =
  newEntries g1 l M.
Proof with eauto.
  intros; subst;
    erewrite newEntries_cons with (f1 := f) (t1 := t);
    try rewrite removeEntry_idempot;
    try intros ABS;
    simpl in *; try inversion H4...
Qed.

Lemma  newEntries_swap g g1 g2 nd_pf1 l p x1 x2 f1 t1 f2 t2 M:
  g1 = (x1, x2, f1, t1) :: g ->
  g2 = (x1, x2, f2, t2) :: g ->
  l = secLabs (dep_relabel p (domain g1) nd_pf1) ->
  M = max (domain g1) ->
  sl_pos p ->
  ~ In (x1, x2) (secLabs p) ->
  newEntries g1 l M =
  newEntries g2 l M.
Proof with eauto using in_preserves_max,not_in_cons.
  introv EQ1 EQ2 SL MAX SLP NIN.
  unfold sl_pos,pos in SLP;
    erewrite identif_seclabs_of_dep_relabel in SL; subst l.
  induction (secLabs p);
    try rewrite identif_seclabs_of_dep_relabel, map_nil_eq,map_cons;
    try destruct a as[a1 a2]...
  rewrite <-MAX in *;
    remember (fun x : name * name => (fst x, snd x + M)) as f.
  assert (NIN2:  ~ In (x1, x2) l).
  eapply not_in_cons in NIN as (_&K)...
  repeat erewrite map_cons, Heqf,<-Heqf; unfold fst, snd;
    simpl.
  assert (INB2: InB (a1, a2 + M) g2 = InB (a1, a2 + M) g1).
  rewrite EQ1, EQ2. simpl.
  assert (a2+M> x2).
  assert (x2 <=M).
  subst M g1; unfold domain; fold domain...
  assert (IN:In (a1, a2) ((a1, a2) :: l))...
  eapply SLP in IN.
  destruct a2; 
      try lia.
  assert (PNEQ: pair_eq (a1, a2 + M) (x1, x2)= false).
  rewrite <-pairEq_neq; intros ABS; inv ABS; try lia.
  repeat erewrite PNEQ...
  case_eq (InB (a1, a2 + M) g1); introv INB1;
    case_eq b; intros; subst b.
  erewrite INB1 in *;
    try erewrite INB2,IHl...
  intros y1 y2 IN; specialize SLP with y1 y2;
    eapply SLP; try right...
  erewrite INB1 in *;
    try erewrite INB2,IHl...
  assert (EQ: a2 + M - M = a2) by lia.
  repeat erewrite EQ.
  assert (PNEQ:  pair_eq (a1, a2) (x1, x2) = false).
  rewrite <-pairEq_neq; intros ABS; inv ABS; intuition.
  assert (INB2': InB (a1, a2) g2 = InB (a1, a2) g1).
  rewrite EQ1, EQ2; simpl; rewrite PNEQ...
  rewrite  INB2'...
  intros y1 y2 IN; specialize SLP with y1 y2;
    eapply SLP; try right...
Qed.

 Lemma newEntries_nil_nil g n:
    newEntries g nil n = nil.
  Proof with eauto.
    induction g; simpl...
  Qed.
  
  Lemma newEntries_distr: forall g l1 l2 n,
      newEntries g (l1 ++ l2) n =
      newEntries g l1 n ++ newEntries g l2 n.
  Proof with eauto.
    induction l1, l2; 
       try rewrite app_nil_r;
       try rewrite app_nil_l;
      intros; try rewrite  newEntries_nil_nil...
    try rewrite app_nil_r...
    destruct a as [a1 a2]. rewrite <-app_comm_cons. unfold newEntries at 1.  
    case_eq (InB (a1, a2) g); intros.
    destruct b.
    fold newEntries.
    unfold newEntries at 2.
    rewrite H.
    fold newEntries...
    fold newEntries.
    case_eq (InB (a1, a2 - n) g). intros. destruct p1 as [f1 t1].
    unfold fst, snd.
    unfold newEntries at 2.
    rewrite H.
    fold newEntries.
    rewrite H0;unfold fst, snd...
    rewrite IHl1...
  Qed.


 
