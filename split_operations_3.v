Require Import
        Bool List Omega PeanoNat Program.Equality
        ListAddOns Max RemoveEntry Domain Classical
        header
        operations pi_syntax 
        pairEq type_system semantics
        type_operations_1
        split_exists_neutral
        sub_split
        no_dup_split_no_dup
        split_existential
        split_cons_remove
        split_not_exists
        split_operations
        lts_operations
        split_operations_2
        disjoint_newEntries.

Hint Resolve no_dup_split_no_dup_r no_dup_split_no_dup_l.

Lemma split_new_un_top :
                   forall g1 g2 g pf1 pf2 pf 
                        a1 a2 b1 b2 t f p
                        h1 h2 h pf' pf'' pf''' (nd_pf : NoDup(domain g)),
    tEnv_split g1 g2 g pf1 pf2 pf ->
    In (a1, a2, f, Chan un p t) g1->
     In (b1, b2, h1, Top) g1->
    flag_plus h1 h2 h ->
    (a1, a2) <> (b1, b2) ->
    tEnv_split g1
               ( (b1, b2, h2, Top)::  (removeEntry (b1, b2) g2))
               ((b1, b2, h, Top) ::  (removeEntry (b1, b2) g))
               pf' pf'' pf'''.
Proof with eauto.
  intros.
  assert (pff1 : NoDup (domain (removeEntry (b1, b2) g1))).
  assert (nd_pf1: NoDup(domain g1))...
   assert (pff2 : NoDup (domain (removeEntry (b1, b2)  ((b1, b2, h2, Top) :: removeEntry (b1, b2) g2)))).
 assert (nd_pf2: NoDup(domain g2))...
 assert (nd_pf'' : NoDup (domain ( (b1, b2, h2, Top) ::removeEntry (b1, b2) g2))).
  apply no_dup_cons_removeEntry...
  eauto.
  assert (pff : NoDup (domain
                         (removeEntry (b1, b2) ((b1, b2, h, Top) :: removeEntry (b1, b2) g)))).
  assert (nd_pf''' : NoDup (domain  ((b1, b2, h, Top) ::removeEntry (b1, b2) g))).
  apply no_dup_cons_removeEntry...
  all:eauto.
  apply no_dup_isMap in pff1 as pfm1.
  apply no_dup_isMap in pff2 as pfm2.
  apply no_dup_isMap in pff as pfm.
  assert (pfmm1 : isMap (removeEntry (b1, b2) g1))...
  assert (pfmm2 : isMap
              (removeEntry (b1, b2)
                 ((b1, b2, h2, Top)
                  ::  (removeEntry (b1, b2) g2)))).
  apply isMap_removeEntry...
  assert (pfmm : isMap (removeEntry (b1, b2) ( (b1, b2, h, Top) :: removeEntry (b1, b2) g))).
  apply isMap_removeEntry...
  apply SpTop with
      (n := (b1, b2)) (f := h1) (f' := h) (g := h2)
      (pf' := pfmm1)  (pf'' := pfmm2) (pf''' := pfmm).
  all:eauto. 
  
  revert dependent pfmm2. revert dependent pfmm1. revert dependent pfmm.
  assert (PEQ: pair_eq (b1, b2) (b1, b2) = true)...
  unfold removeEntry.
  rewrite PEQ.
  fold removeEntry.
  intros.

  apply split_remove with (pf1 := pf1) (pf2 := pf2) (pf3 := pf)...
  Qed.

(* split_removeEntry_domain is now in split_not_exists *)

  Lemma split_removeEntry_domain_2 :
  forall b1 b2 f1 s1 f2 s2 g1 g2 g pf1 pf2 pf
         (nd_pf : NoDup (domain g)),
    tEnv_split g1 g2 g pf1 pf2 pf ->
    forall x,
      In x (domain ((b1, b2, f1, s1) :: removeEntry (b1, b2) g)) <->
      In x (domain ((b1, b2, f2, s2) :: removeEntry (b1, b2) g1)).
  Proof.
    intros.
    apply split_removeEntry_domain with (x := x)
      (b1 := b1) (b2 := b2) (f1 := f1) (f2 := f2) (s1 := s1) (s2 := s2)in H.
    all:assumption.
  Qed.
    

Lemma split_flag_plus : forall g1 g2 g pf1 pf2 pf a t1 t,
    flagOf g1 a t1 ->
    flagOf g a t ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    exists t2,
      flagOf g2 a t2 /\
      flag_plus t1 t2 t.
Proof with eauto.
    intros  g1 g2 g pf1 pf2 pf a t1 t TYP1 TYP TS.
    dependent induction TS.
    - subst. inversion TYP1. inversion H.
    - destruct a as [a1 a2]; destruct n as [n1 n2].
      case_eq (pair_eq (n1, n2) (a1, a2)). intros PEQ. 
      rewrite <-pairEq_eq in PEQ; inversion PEQ; subst.
      exists  g. split...
      inversion TYP1; inversion TYP; inversion H5; subst.
      assert (f = t1 /\ Chan lin p t0 = t2).
      apply in_isMap with (x := (a1, a2)) (g := g1)...
      inversion H4; subst. 
      assert (t = f' /\ t3 =  t4).
      apply in_isMap with (x := (a1, a2)) (g := g3)...
      destruct H6; destruct H8.  subst...
      intros PNEQ. assert (PNEQ2 := PNEQ).
      rewrite <-pairEq_neq in PNEQ.
      inversion TYP1. subst.
      assert ( In (a1, a2, t1, t2)  (removeEntry (n1, n2) g1)).
      apply removeEntry_in...
      apply F_Entry in H3 as IHH.
      apply IHTS in IHH.
      destruct IHH as [ft2 [TYP2 TP]].
      exists ft2.
      split. inversion TYP2.  subst. apply in_removeEntry in H7...
      eauto.
      inversion TYP; subst. apply removeEntry_in with (y := (n1, n2)) in H7...
    - destruct a as [a1 a2]; destruct n as [n1 n2].
      case_eq (pair_eq (n1, n2) (a1, a2)). intros PEQ. 
      rewrite <-pairEq_eq in PEQ; inversion PEQ; subst.
      exists g.
      split...
      inversion TYP1; inversion TYP; inversion H3; subst.
      assert (f = t1 /\ Chan un p t0 = t2).
      apply in_isMap with (x := (a1, a2)) (g := g1)...
      assert (t = f' /\ t3 =  t4).
      apply in_isMap with (x := (a1, a2)) (g := g3)...
      destruct H5; destruct H6; subst...

      intros PNEQ. assert (PNEQ2 := PNEQ).
      rewrite <-pairEq_neq in PNEQ.
      inversion TYP1. subst.
      assert ( In (a1, a2, t1, t2)  (removeEntry (n1, n2) g1)).
      apply removeEntry_in...
      apply F_Entry in H2 as IHH.
      apply IHTS in IHH.
      destruct IHH as [ft2 [TYP2 TP]].
      exists ft2.
      split. inversion TYP2.  subst. apply in_removeEntry in H6...
      eauto.
      inversion TYP; subst. apply removeEntry_in with (y := (n1, n2)) in H6...
      - destruct a as [a1 a2]; destruct n as [n1 n2].
      case_eq (pair_eq (n1, n2) (a1, a2)). intros PEQ. 
      rewrite <-pairEq_eq in PEQ; inversion PEQ; subst.
      exists g.
      split...
      inversion TYP1; inversion TYP; inversion H3; subst.
      assert (f = t1 /\ Top = t0).
      apply in_isMap with (x := (a1, a2)) (g := g1)...
      assert (t = f' /\ t2 =  t3).
      apply in_isMap with (x := (a1, a2)) (g := g3)...
      destruct H5; destruct H6; subst...
      intros PNEQ. assert (PNEQ2 := PNEQ).
      rewrite <-pairEq_neq in PNEQ.
      inversion TYP1. subst.
      assert ( In (a1, a2, t1, t0)  (removeEntry (n1, n2) g1)).
      apply removeEntry_in...
      apply F_Entry in H2 as IHH.
      apply IHTS in IHH.
      destruct IHH as [ft2 [TYP2 TP]].
      exists ft2.
      split. inversion TYP2.  subst. apply in_removeEntry in H6...
      eauto.
      inversion TYP; subst. apply removeEntry_in with (y := (n1, n2)) in H6...
Qed.

Lemma plus_sub_exists : forall t s r s1,
    type_plus t s r ->
    type_sub s1 s ->
    exists r1,
      type_plus t s1 r1.
Proof with eauto.
  intros.
  destruct s.
  - destruct p.
    exists t.
    inversion H... subst.
    inversion H0; subst...
    assert (p1 = pol_cup p1 empty)...
    subst.  inversion H0; subst...
    rewrite H6 at 2... rewrite H6 at 2...
    
    inversion H0; subst.
    exists r...
    exists t...
    inversion H; subst...
    assert (p1 = pol_cup p1 empty)...
    rewrite H1 at 2...

     inversion H0; subst.
    exists r...
    exists t...
    inversion H; subst...
    assert (p1 = pol_cup p1 empty)...
    rewrite H1 at 2...

     inversion H0; subst.
    exists r...
    exists t...
    inversion H; subst...
    assert (p1 = pol_cup p1 empty)...
    rewrite H1 at 2...
    inversion H; subst...
    inversion H6; subst...
     inversion H; subst...
     inversion H6; subst...
  - exists Top... inversion H; subst... inversion H0; subst...
Qed.

 
(*Lemma lts_type_plus_lin_in: forall g0 p1 a1 a2 b1 b2 t f1 s1 p2 pf0 s f s0 s01 g1 pf1,
    lts g0 p1
       (aIn a1 a2 b1 b2)
       ((a1, a2, vis, Chan lin empty t) :: (b1, b2, f1, s1) :: (removeEntry (a1, a2) (removeEntry (b1, b2) g0))) p2 pf0 ->
   In (a1, a2, vis, Chan lin inp t) g0 ->
   In (b1, b2, f, s) g0 ->
   type_plus s0 t s01 ->
   In (a1, a2, vis, Chan lin inp t) g1 ->
   In (b1, b2, f, s0) g1 ->
  lts g1 p1
       (aIn a1 a2 b1 b2)
       ((a1, a2, vis, Chan lin empty t) :: (b1, b2, f1, s01) :: (removeEntry (a1, a2) (removeEntry (b1, b2) g1))) p2 pf1.
  Proof with
eauto.
  intros g0 p1 a1 a2 b1 b2 t f1 s1 p2 pf0 s f s0 s01 g1 pf1
         LTS INa INb TREM INa1 INb1.
  assert ((a1, a2) <> (b1, b2)).
  apply nonRecActions1 in LTS...
  generalize dependent f. generalize dependent g1.
  dependent induction LTS.
  - specialize IHLTS with
        (a3 := a1) (a4 := a2)
        (b3 := b1) (b4 := b2)
        (t0 := t)
        (s2 := s1) (f2 := f1). 
    intuition.
    apply parL...
  - intros. apply lIn with (t1 := s0) (f := f0).
    eauto.
    assert (f = f0).
    apply  flag_of_map with g (b1, b2)...
    subst...
    eauto. eauto.
  - intuition.
  - intros.
    assert (vis = vis /\ Chan lin inp t = Chan un pol t0).
    apply in_isMap with (x := (a1, a2)) (g := g)...
    inversion H5. inversion H7.
    Unshelve.
    all:eauto.
  Qed.
*)

  Lemma split_new_lin_lin: forall g1 g2 g pf1 pf2 pf 
                        a1 a2 s b1 b2 t f1 f2 f p1 p2 p
                        h1 h2 h q1 q2 q pf' pf'' pf'''
                        (nd_pf : NoDup(domain g)),
    tEnv_split g1 g2 g pf1 pf2 pf ->
    In (a1, a2, f1, Chan lin p1 t) g1->
    flag_plus f1 f2 f ->
    pol_plus p1 p2 p ->
     In (b1, b2, h1, Chan lin q1 s) g1->
    flag_plus h1 h2 h ->
    pol_plus q1 q2 q ->
    (a1, a2) <> (b1, b2) ->
    tEnv_split g1
               ((a1, a2, f2 , Chan lin p2 t)
                  :: (b1, b2, h2, Chan lin q2 s)
                  :: removeEntry (a1, a2) (removeEntry (b1, b2) g2))
               ((a1, a2, f, Chan lin p t)
                  :: (b1, b2, h, Chan lin q s) 
                  :: removeEntry (a1, a2) (removeEntry (b1, b2) g)) pf' pf'' pf'''.
Proof with eauto.
  intros.
  assert (pff1 : NoDup (domain (removeEntry (a1, a2) (removeEntry (b1, b2) g1)))).
  assert (nd_pf1: NoDup(domain g1))...
   assert (pff2 : NoDup (domain (removeEntry (a1, a2) (removeEntry (b1, b2)  ((a1, a2, f2, Chan lin p2 t)
     :: (b1, b2, h2, Chan lin q2 s) :: removeEntry (a1, a2) (removeEntry (b1, b2) g2)))))).
 assert (nd_pf2: NoDup(domain g2))...
 assert (nd_pf'' : NoDup (domain ((a1, a2, f2, Chan lin p2 t)
                                    :: (b1, b2, h2, Chan lin q2 s) :: removeEntry (a1, a2) (removeEntry (b1, b2) g2)))).
  apply no_dup_cons_removeEntry_app...
  eauto.
  assert (pff : NoDup (domain
                         (removeEntry (a1, a2)
                                      (removeEntry (b1, b2) ((a1, a2, f, Chan lin p t)
                                  :: (b1, b2, h, Chan lin q s) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)))))).
  assert (nd_pf''' : NoDup (domain  ((a1, a2, f, Chan lin p t)
                                  :: (b1, b2, h, Chan lin q s) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)))).
  apply no_dup_cons_removeEntry_app...
  eauto.
  apply no_dup_isMap in pff1 as pfm1.
  apply no_dup_isMap in pff2 as pfm2.
  apply no_dup_isMap in pff as pfm.
  assert (pfmm1 : isMap (removeEntry (b1, b2) g1))...
  assert (pfmm2 : isMap
              (removeEntry (b1, b2)
                 ((a1, a2, f2, Chan lin p2 t)
                  :: (b1, b2, h2, Chan lin q2 s)
                  :: removeEntry (a1, a2) (removeEntry (b1, b2) g2)))).
  apply isMap_removeEntry...
  assert (pfmm : isMap (removeEntry (b1, b2) ((a1, a2, f, Chan lin p t)
                                               :: (b1, b2, h, Chan lin q s) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)))).
  apply isMap_removeEntry...
  apply SpLin with
      (n := (b1, b2)) (f := h1) (f' := h) (g := h2)
      (p := q1) (q := q2) (p' := q) (t := s)
      (pf' := pfmm1)  (pf'' := pfmm2) (pf''' := pfmm).
  all:eauto.
   apply SpLin with
      (n := (a1, a2)) (f := f1) (f' := f) (g := f2)
      (p := p1) (q := p2) (p' := p) (t := t)
      (pf' := pfm1)  (pf'' := pfm2) (pf''' := pfm).
   eauto. eauto. apply removeEntry_in... apply removeEntry_in...
   assert (SWAP: (removeEntry (a1, a2)
       (removeEntry (b1, b2)
          ((a1, a2, f2, Chan lin p2 t)
             :: (b1, b2, h2, Chan lin q2 s) :: removeEntry (a1, a2) (removeEntry (b1, b2) g2)))) =
                 removeEntry (a1, a2) ((a1, a2, f2, Chan lin p2 t) :: removeEntry (b1, b2) ((b1, b2, h2, Chan lin q2 s) :: removeEntry (a1, a2) (removeEntry (b1, b2) g2)))).
   rewrite <-removeEntry_shift.
   eauto.
   eauto.
   revert dependent pfm2. 
   rewrite SWAP.
   unfold removeEntry at 2.
   unfold removeEntry at 9.
   assert (PEQ: pair_eq (b1, b2) (b1, b2) = true)...
   rewrite PEQ.
   unfold removeEntry at 1.
   unfold removeEntry at 7.
    assert (PEQ2: pair_eq (a1, a2) (a1, a2) = true)...
    rewrite PEQ2.
    intros. 

   assert (SWAP2: (removeEntry (a1, a2)
       (removeEntry (b1, b2)
          ((a1, a2, f, Chan lin p t)
             :: (b1, b2, h, Chan lin q s) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)))) =
                 removeEntry (a1, a2) ((a1, a2, f, Chan lin p t) :: removeEntry (b1, b2) ((b1, b2, h, Chan lin q s) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)))).
   rewrite <-removeEntry_shift.
   eauto.
   eauto.
   revert dependent pfm. 
   rewrite SWAP2.
   unfold removeEntry at 2.
   unfold removeEntry at 11.
   rewrite PEQ.
   unfold removeEntry at 1.
   unfold removeEntry at 9.
   rewrite PEQ2.
   intros.
   assert (pfm'' : isMap (removeEntry (b1, b2) g2))...
   assert (pfm''' : isMap (removeEntry (b1, b2) g))...
   apply split_remove
         with (pf1 := pfmm1) (pf2 := pfm'') (pf3 := pfm''')...
   apply split_remove
     with (pf1 := pf1) (pf2 := pf2) (pf3 := pf)...
   eauto.
   assert (In (a1, a2, f, Chan lin p t) (removeEntry (b1, b2)
       ((a1, a2, f, Chan lin p t)
          :: (b1, b2, h, Chan lin q s) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)))).
    apply removeEntry_in...
   eauto.
   assert (In (a1, a2, f, Chan lin p t) (removeEntry (b1, b2)
       ((a1, a2, f, Chan lin p t)
          :: (b1, b2, h, Chan lin q s) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)))).
    apply removeEntry_in...
    eauto.
Qed.

Lemma split_new_lin_un: forall g1 g2 g pf1 pf2 pf 
                        a1 a2 s b1 b2 t f1 f2 f p1 p2 p
                        h1 h2 h q pf' pf'' pf''' (nd_pf : NoDup(domain g)),
    tEnv_split g1 g2 g pf1 pf2 pf ->
    In (a1, a2, f1, Chan lin p1 t) g1->
    flag_plus f1 f2 f ->
    pol_plus p1 p2 p ->
     In (b1, b2, h1, Chan un q s) g1->
    flag_plus h1 h2 h ->
    (a1, a2) <> (b1, b2) ->
    tEnv_split g1
               ((a1, a2, f2 , Chan lin p2 t)
                  :: (b1, b2, h2, Chan un q s)
                  :: removeEntry (a1, a2) (removeEntry (b1, b2) g2))
               ((a1, a2, f, Chan lin p t)
                  :: (b1, b2, h, Chan un q s) 
                  :: removeEntry (a1, a2) (removeEntry (b1, b2) g)) pf' pf'' pf'''.
Proof with eauto.
  intros.
  assert (pff1 : NoDup (domain (removeEntry (a1, a2) (removeEntry (b1, b2) g1)))).
  assert (nd_pf1: NoDup(domain g1))...
   assert (pff2 : NoDup (domain (removeEntry (a1, a2) (removeEntry (b1, b2)  ((a1, a2, f2, Chan lin p2 t)
     :: (b1, b2, h2, Chan un q s) :: removeEntry (a1, a2) (removeEntry (b1, b2) g2)))))).
 assert (nd_pf2: NoDup(domain g2))...
 assert (nd_pf'' : NoDup (domain ((a1, a2, f2, Chan lin p2 t)
                                    :: (b1, b2, h2, Chan un q s) :: removeEntry (a1, a2) (removeEntry (b1, b2) g2)))).
  apply no_dup_cons_removeEntry_app...
  eauto.
  assert (pff : NoDup (domain
                         (removeEntry (a1, a2)
                                      (removeEntry (b1, b2) ((a1, a2, f, Chan lin p t)
                                  :: (b1, b2, h, Chan un q s) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)))))).
  assert (nd_pf''' : NoDup (domain  ((a1, a2, f, Chan lin p t)
                                  :: (b1, b2, h, Chan un q s) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)))).
  apply no_dup_cons_removeEntry_app...
  eauto.
  apply no_dup_isMap in pff1 as pfm1.
  apply no_dup_isMap in pff2 as pfm2.
  apply no_dup_isMap in pff as pfm.
  assert (pfmm1 : isMap (removeEntry (b1, b2) g1))...
  assert (pfmm2 : isMap
              (removeEntry (b1, b2)
                 ((a1, a2, f2, Chan lin p2 t)
                  :: (b1, b2, h2, Chan un q s)
                  :: removeEntry (a1, a2) (removeEntry (b1, b2) g2)))).
  apply isMap_removeEntry...
  assert (pfmm : isMap (removeEntry (b1, b2) ((a1, a2, f, Chan lin p t)
                                               :: (b1, b2, h, Chan un q s) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)))).
  apply isMap_removeEntry...
  apply SpUn with
      (n := (b1, b2)) (f := h1) (f' := h) (g := h2)
      (p := q) (t := s)
      (pf' := pfmm1)  (pf'' := pfmm2) (pf''' := pfmm).
  all:eauto.
   apply SpLin with
      (n := (a1, a2)) (f := f1) (f' := f) (g := f2)
      (p := p1) (q := p2) (p' := p) (t := t)
      (pf' := pfm1)  (pf'' := pfm2) (pf''' := pfm).
   eauto. eauto. apply removeEntry_in... apply removeEntry_in...
   assert (SWAP: (removeEntry (a1, a2)
       (removeEntry (b1, b2)
          ((a1, a2, f2, Chan lin p2 t)
             :: (b1, b2, h2, Chan un q s) :: removeEntry (a1, a2) (removeEntry (b1, b2) g2)))) =
                 removeEntry (a1, a2) ((a1, a2, f2, Chan lin p2 t) :: removeEntry (b1, b2) ((b1, b2, h2, Chan un q s) :: removeEntry (a1, a2) (removeEntry (b1, b2) g2)))).
   rewrite <-removeEntry_shift.
   eauto.
   eauto.
   revert dependent pfm2. 
   rewrite SWAP.
   unfold removeEntry at 2.
   unfold removeEntry at 9.
   assert (PEQ: pair_eq (b1, b2) (b1, b2) = true)...
   rewrite PEQ.
   unfold removeEntry at 1.
   unfold removeEntry at 7.
    assert (PEQ2: pair_eq (a1, a2) (a1, a2) = true)...
    rewrite PEQ2.
    intros. 

   assert (SWAP2: (removeEntry (a1, a2)
       (removeEntry (b1, b2)
          ((a1, a2, f, Chan lin p t)
             :: (b1, b2, h, Chan un q s) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)))) =
                 removeEntry (a1, a2) ((a1, a2, f, Chan lin p t) :: removeEntry (b1, b2) ((b1, b2, h, Chan un q s) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)))).
   rewrite <-removeEntry_shift.
   eauto.
   eauto.
   revert dependent pfm. 
   rewrite SWAP2.
   unfold removeEntry at 2.
   unfold removeEntry at 11.
   rewrite PEQ.
   unfold removeEntry at 1.
   unfold removeEntry at 9.
   rewrite PEQ2.
   intros.
   assert (pfm'' : isMap (removeEntry (b1, b2) g2))...
   assert (pfm''' : isMap (removeEntry (b1, b2) g))...
   apply split_remove
         with (pf1 := pfmm1) (pf2 := pfm'') (pf3 := pfm''')...
   apply split_remove
     with (pf1 := pf1) (pf2 := pf2) (pf3 := pf)...
   eauto.
   assert (In (a1, a2, f, Chan lin p t) (removeEntry (b1, b2)
       ((a1, a2, f, Chan lin p t)
          :: (b1, b2, h, Chan un q s) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)))).
    apply removeEntry_in...
   eauto.
   assert (In (a1, a2, f, Chan lin p t) (removeEntry (b1, b2)
       ((a1, a2, f, Chan lin p t)
          :: (b1, b2, h, Chan un q s) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)))).
    apply removeEntry_in...
    eauto.
Qed.

Lemma split_new_lin_top: forall g1 g2 g pf1 pf2 pf 
                        a1 a2 b1 b2 t f1 f2 f p1 p2 p
                        h1 h2 h pf' pf'' pf''' (nd_pf : NoDup(domain g)),
    tEnv_split g1 g2 g pf1 pf2 pf ->
    In (a1, a2, f1, Chan lin p1 t) g1->
    flag_plus f1 f2 f ->
    pol_plus p1 p2 p ->
     In (b1, b2, h1, Top) g1->
    flag_plus h1 h2 h ->
    (a1, a2) <> (b1, b2) ->
    tEnv_split g1
               ((a1, a2, f2 , Chan lin p2 t)
                  :: (b1, b2, h2, Top)
                  :: removeEntry (a1, a2) (removeEntry (b1, b2) g2))
               ((a1, a2, f, Chan lin p t)
                  :: (b1, b2, h, Top) 
                  :: removeEntry (a1, a2) (removeEntry (b1, b2) g)) pf' pf'' pf'''.
Proof with eauto.
  intros.
  assert (pff1 : NoDup (domain (removeEntry (a1, a2) (removeEntry (b1, b2) g1)))).
  assert (nd_pf1: NoDup(domain g1))...
   assert (pff2 : NoDup (domain (removeEntry (a1, a2) (removeEntry (b1, b2)  ((a1, a2, f2, Chan lin p2 t)
     :: (b1, b2, h2, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g2)))))).
 assert (nd_pf2: NoDup(domain g2))...
 assert (nd_pf'' : NoDup (domain ((a1, a2, f2, Chan lin p2 t)
                                    :: (b1, b2, h2, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g2)))).
  apply no_dup_cons_removeEntry_app...
  eauto.
  assert (pff : NoDup (domain
                         (removeEntry (a1, a2)
                                      (removeEntry (b1, b2) ((a1, a2, f, Chan lin p t)
                                  :: (b1, b2, h, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)))))).
  assert (nd_pf''' : NoDup (domain  ((a1, a2, f, Chan lin p t)
                                  :: (b1, b2, h, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)))).
  apply no_dup_cons_removeEntry_app...
  eauto.
  apply no_dup_isMap in pff1 as pfm1.
  apply no_dup_isMap in pff2 as pfm2.
  apply no_dup_isMap in pff as pfm.
  assert (pfmm1 : isMap (removeEntry (b1, b2) g1))...
  assert (pfmm2 : isMap
              (removeEntry (b1, b2)
                 ((a1, a2, f2, Chan lin p2 t)
                  :: (b1, b2, h2, Top)
                  :: removeEntry (a1, a2) (removeEntry (b1, b2) g2)))).
  apply isMap_removeEntry...
  assert (pfmm : isMap (removeEntry (b1, b2) ((a1, a2, f, Chan lin p t)
                                               :: (b1, b2, h, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)))).
  apply isMap_removeEntry...
  apply SpTop with
      (n := (b1, b2)) (f := h1) (f' := h) (g := h2)
      (pf' := pfmm1)  (pf'' := pfmm2) (pf''' := pfmm).
  all:eauto.
   apply SpLin with
      (n := (a1, a2)) (f := f1) (f' := f) (g := f2)
      (p := p1) (q := p2) (p' := p) (t := t)
      (pf' := pfm1)  (pf'' := pfm2) (pf''' := pfm).
   eauto. eauto. apply removeEntry_in... apply removeEntry_in...
   assert (SWAP: (removeEntry (a1, a2)
       (removeEntry (b1, b2)
          ((a1, a2, f2, Chan lin p2 t)
             :: (b1, b2, h2, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g2)))) =
                 removeEntry (a1, a2) ((a1, a2, f2, Chan lin p2 t) :: removeEntry (b1, b2) ((b1, b2, h2, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g2)))).
   rewrite <-removeEntry_shift.
   eauto.
   eauto.
   revert dependent pfm2. 
   rewrite SWAP.
   unfold removeEntry at 2.
   unfold removeEntry at 9.
   assert (PEQ: pair_eq (b1, b2) (b1, b2) = true)...
   rewrite PEQ.
   unfold removeEntry at 1.
   unfold removeEntry at 7.
    assert (PEQ2: pair_eq (a1, a2) (a1, a2) = true)...
    rewrite PEQ2.
    intros. 

   assert (SWAP2: (removeEntry (a1, a2)
       (removeEntry (b1, b2)
          ((a1, a2, f, Chan lin p t)
             :: (b1, b2, h, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)))) =
                 removeEntry (a1, a2) ((a1, a2, f, Chan lin p t) :: removeEntry (b1, b2) ((b1, b2, h, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)))).
   rewrite <-removeEntry_shift.
   eauto.
   eauto.
   revert dependent pfm. 
   rewrite SWAP2.
   unfold removeEntry at 2.
   unfold removeEntry at 11.
   rewrite PEQ.
   unfold removeEntry at 1.
   unfold removeEntry at 9.
   rewrite PEQ2.
   intros.
   assert (pfm'' : isMap (removeEntry (b1, b2) g2))...
   assert (pfm''' : isMap (removeEntry (b1, b2) g))...
   apply split_remove
         with (pf1 := pfmm1) (pf2 := pfm'') (pf3 := pfm''')...
   apply split_remove
     with (pf1 := pf1) (pf2 := pf2) (pf3 := pf)...
   eauto.
   assert (In (a1, a2, f, Chan lin p t) (removeEntry (b1, b2)
       ((a1, a2, f, Chan lin p t)
          :: (b1, b2, h, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)))).
    apply removeEntry_in...
   eauto.
   assert (In (a1, a2, f, Chan lin p t) (removeEntry (b1, b2)
       ((a1, a2, f, Chan lin p t)
          :: (b1, b2, h, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)))).
    apply removeEntry_in...
    eauto.
Qed.

 Lemma split_new_un_lin: forall g1 g2 g pf1 pf2 pf 
                        a1 a2 s b1 b2 t f p
                        h1 h2 h q1 q2 q pf' pf'' pf'''
                        (nd_pf : NoDup(domain g)),
    tEnv_split g1 g2 g pf1 pf2 pf ->
    In (a1, a2, f, Chan un p t) g1->
     In (b1, b2, h1, Chan lin q1 s) g1->
    flag_plus h1 h2 h ->
    pol_plus q1 q2 q ->
    (a1, a2) <> (b1, b2) ->
    tEnv_split g1
               ((b1, b2, h2, Chan lin q2 s)
                  :: removeEntry (b1, b2) g2)
               ( (b1, b2, h, Chan lin q s) 
                  :: removeEntry (b1, b2) g) pf' pf'' pf'''.
Proof with eauto.
  intros.
  assert (pff1 : NoDup (domain (removeEntry (b1, b2) g1))).
  assert (nd_pf1: NoDup(domain g1))...
   assert (pff2 : NoDup (domain (removeEntry (b1, b2)  ((b1, b2, h2, Chan lin q2 s) :: removeEntry (b1, b2) g2)))).
 assert (nd_pf2: NoDup(domain g2))...
 assert (nd_pf'' : NoDup (domain ( (b1, b2, h2, Chan lin q2 s) ::removeEntry (b1, b2) g2))).
  apply no_dup_cons_removeEntry...
  eauto.
  assert (pff : NoDup (domain
                         (removeEntry (b1, b2) ((b1, b2, h, Chan lin q s) :: removeEntry (b1, b2) g)))).
  assert (nd_pf''' : NoDup (domain  ((b1, b2, h, Chan lin q s) ::removeEntry (b1, b2) g))).
  apply no_dup_cons_removeEntry...
  eauto.
  apply no_dup_isMap in pff1 as pfm1.
  apply no_dup_isMap in pff2 as pfm2.
  apply no_dup_isMap in pff as pfm.
  assert (pfmm1 : isMap (removeEntry (b1, b2) g1))...
  assert (pfmm2 : isMap
              (removeEntry (b1, b2)
                 ((b1, b2, h2, Chan lin q2 s)
                  ::  (removeEntry (b1, b2) g2)))).
  apply isMap_removeEntry...
  assert (pfmm : isMap (removeEntry (b1, b2) ( (b1, b2, h, Chan lin q s) :: removeEntry (b1, b2) g))).
  apply isMap_removeEntry...
  apply SpLin with
      (n := (b1, b2)) (f := h1) (f' := h) (g := h2)
      (p := q1) (q := q2) (p' := q) (t := s)
      (pf' := pfmm1)  (pf'' := pfmm2) (pf''' := pfmm).
  all:eauto. 
  
  revert dependent pfmm2. revert dependent pfmm1. revert dependent pfmm.
  assert (PEQ: pair_eq (b1, b2) (b1, b2) = true)...
  unfold removeEntry.
  rewrite PEQ.
  fold removeEntry.
  intros.

  apply split_remove with (pf1 := pf1) (pf2 := pf2) (pf3 := pf)...
Qed.

Lemma split_new_un_un: forall g1 g2 g pf1 pf2 pf 
                        a1 a2 s b1 b2 t f p
                        h1 h2 h q pf' pf'' pf'''
                        (nd_pf : NoDup(domain g)),
    tEnv_split g1 g2 g pf1 pf2 pf ->
    In (a1, a2, f, Chan un p t) g1->
     In (b1, b2, h1, Chan un q s) g1->
    flag_plus h1 h2 h ->
    (a1, a2) <> (b1, b2) ->
    tEnv_split g1
               ((b1, b2, h2, Chan un q s)
                  :: removeEntry (b1, b2) g2)
               ( (b1, b2, h, Chan un q s) 
                  :: removeEntry (b1, b2) g) pf' pf'' pf'''.
Proof with eauto.
  intros.
  assert (pff1 : NoDup (domain (removeEntry (b1, b2) g1))).
  assert (nd_pf1: NoDup(domain g1))...
   assert (pff2 : NoDup (domain (removeEntry (b1, b2)  ((b1, b2, h2, Chan un q s) :: removeEntry (b1, b2) g2)))).
 assert (nd_pf2: NoDup(domain g2))...
 assert (nd_pf'' : NoDup (domain ( (b1, b2, h2, Chan un q s) ::removeEntry (b1, b2) g2))).
  apply no_dup_cons_removeEntry...
  eauto.
  assert (pff : NoDup (domain
                         (removeEntry (b1, b2) ((b1, b2, h, Chan un q s) :: removeEntry (b1, b2) g)))).
  assert (nd_pf''' : NoDup (domain  ((b1, b2, h, Chan un q s) ::removeEntry (b1, b2) g))).
  apply no_dup_cons_removeEntry...
  eauto.
  apply no_dup_isMap in pff1 as pfm1.
  apply no_dup_isMap in pff2 as pfm2.
  apply no_dup_isMap in pff as pfm.
  assert (pfmm1 : isMap (removeEntry (b1, b2) g1))...
  assert (pfmm2 : isMap
              (removeEntry (b1, b2)
                 ((b1, b2, h2, Chan un q s)
                  ::  (removeEntry (b1, b2) g2)))).
  apply isMap_removeEntry...
  assert (pfmm : isMap (removeEntry (b1, b2) ( (b1, b2, h, Chan un q s) :: removeEntry (b1, b2) g))).
  apply isMap_removeEntry...
  apply SpUn with
      (n := (b1, b2)) (f := h1) (f' := h) (g := h2)
      (p := q)  (t := s)
      (pf' := pfmm1)  (pf'' := pfmm2) (pf''' := pfmm).
  all:eauto. 
  
  revert dependent pfmm2. revert dependent pfmm1. revert dependent pfmm.
  assert (PEQ: pair_eq (b1, b2) (b1, b2) = true)...
  unfold removeEntry.
  rewrite PEQ.
  fold removeEntry.
  intros.

  apply split_remove with (pf1 := pf1) (pf2 := pf2) (pf3 := pf)...
Qed.
