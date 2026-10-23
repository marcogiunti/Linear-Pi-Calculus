Require Import
         Bool List Lia PeanoNat Program.Equality
        ListAddOns Max RemoveEntry Domain
        header
        operations pi_syntax 
        pairEq type_system 
        semantics  
        type_system_rules
        proposition27
        disjoint_newEntries
        no_dup_split_no_dup
        substitution_prelim
        split_cons_remove
        tc_prelim
        type_checking_0
        type_checking_1
        type_operations_1 (*move no_dup_isMap somewhere else*)
        sub_split
        split_operations
        split_operations_2
        tc_premises2
        split_existential
        split_not_exists.

#[global] Hint Resolve split_comm.
#[global] Hint Constructors cons.
#[global] Hint Constructors type_sub.
#[global] Hint Constructors type_plus.


  #[global] Hint Constructors cons.

#[global] Hint Resolve
     gcons_removeEntry
     cons_lin
     cons_cons_iff
     no_dup_removeEntry_no_dup
     type_plus_type_sub
     plus_sub_exists_2
     typeCheck_rewrite_pf beq_nat_refl.
      
  Lemma typeCheck_substitution: forall b1 b2 x1 x2 f s1 s s2 g pf pf1 p (nd_pf : NoDup (domain g)),
      In (b1, b2, f, s1) g ->
      In (x1, x2, vis, s) g ->
      (x1,x2)<> (b1, b2) ->
      (x2 < max (domain g) \/ x2 < b2)->
      f <> hid ->
      type_plus s1 s s2 ->
      typeCheck g pf p ->
      typeCheck ((b1, b2, vis, s2)
                   :: removeEntry (b1, b2)
                   (removeEntry (x1, x2) g)) pf1
                (pmap p x1 x2 b1 b2).
  Proof with eauto.
    intros b1 b2 x1 x2 f s1 s s2 g pf pf1 p nd_pf
           INb INx DIFFX MIN NOTHID TP TC.
    generalize dependent s1.
    generalize dependent s.
    generalize dependent s2.
    generalize dependent nd_pf.
    dependent induction TC.
    - intros. unfold pmap; eapply TNil.
      (* cons ((b1, b2, vis, t2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g)) pf1*)
      assert (nd_pf': NoDup (domain (removeEntry (b1, b2) ((b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g))))).
      eapply no_dup_removeEntry_no_dup,no_dup_cons_removeEntry,no_dup_removeEntry_no_dup...
      eapply no_dup_isMap in nd_pf' as pf'.
      destruct s2; try destruct m.
      + inversion TP; subst.
        try assert (p1 = empty).
        try eapply cons_lin with (x1 := b1)(x2 := b2)(pf := pf)...
        try assert (p2 = empty).
        try eapply cons_lin with (x1 := x1)(x2 := x2)(pf := pf)...
        subst;try inversion H3; subst.
        eapply Co_lin with (pf' := pf').
        eauto.
        revert dependent pf'.
        unfold removeEntry; fold removeEntry.
        assert (EQ: pair_eq (b1, b2) (b1, b2) = true).
        eapply pairEq_eq...
        rewrite EQ.
        intros...
        eapply Co_lin with (pf' := pf').
        eauto.
        revert dependent pf'.
        unfold removeEntry; fold removeEntry.
        assert (EQ: pair_eq (b1, b2) (b1, b2) = true).
        eapply pairEq_eq...
        rewrite EQ.
        intros...
      + eapply Co_un with (pf' := pf').
        eauto.
        revert dependent pf'.
        unfold removeEntry; fold removeEntry.
        assert (EQ: pair_eq (b1, b2) (b1, b2) = true).
        eapply pairEq_eq...
        rewrite EQ.
        intros...
      + eapply Co_top with (pf' := pf').
        eauto.
        revert dependent pf'.
        unfold removeEntry; fold removeEntry.
        assert (EQ: pair_eq (b1, b2) (b1, b2) = true).
        eapply pairEq_eq...
        rewrite EQ.
        intros...
        Unshelve. all:eauto.
    -  intros. unfold pmap; fold pmap.
      assert (nd_pf2 : NoDup (domain ((n, vis, t) :: (removeEntry n ((b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g)))))).
      eapply no_dup_cons_removeEntry,no_dup_cons_removeEntry,no_dup_removeEntry_no_dup...
      eapply no_dup_isMap in nd_pf2 as pf2.
      assert (DIFF1 : n <> (b1, b2)).
      try intros ABS; subst.
      assert (f = hid). eapply flag_of_map with (g := g)...
      subst; try discriminate...
      assert (DIFF2 : n <> (x1, x2)).
      try intros ABS; subst.
      assert (vis = hid). eapply flag_of_map with (g := g)...
      try discriminate...
      apply TNew with (t := t) (pf1 := pf2).
      + (* In (n, hid, t0)
    ((b1, b2, vis, t2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g))*)
      right; eapply removeEntry_in,removeEntry_in... 
      + 
      destruct n.
      assert (nd_pf': NoDup (domain ( ((b1, b2, vis, s2)
                         :: removeEntry (b1, b2)
                         (removeEntry (x1, x2)
                                      ((n, n0, vis, t) :: removeEntry (n, n0) g)))))).
      eapply no_dup_cons_removeEntry,no_dup_removeEntry_no_dup,no_dup_cons_removeEntry...
      eapply no_dup_isMap in nd_pf' as pf1'.
      specialize IHTC with s2 pf1' s s1.
      assert (nd_pf1 : NoDup (domain ((n, n0, vis, t) :: removeEntry (n, n0) g))).
      apply no_dup_cons_removeEntry...
      apply IHTC in nd_pf1 as TC2.
      assert
        (EQ1 : (b1, b2, vis, s2)
                 :: removeEntry (b1, b2)
                 (removeEntry (x1, x2) ((n, n0, vis, t) :: removeEntry (n, n0) g)) =
               ((b1, b2, vis, s2) ::
                                  (n, n0, vis, t) :: removeEntry (b1, b2)
                                  (removeEntry (x1, x2) ( removeEntry (n, n0) g)))). 
      erewrite <-removeEntry_shift,<-removeEntry_shift...
      assert (EQ2 :(n, n0, vis, t)
                     :: removeEntry (n, n0)
                     ((b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g)) =
                   (n, n0, vis, t)
                     :: (b1, b2, vis, s2) :: removeEntry (n, n0)
                     ( removeEntry (b1, b2) (removeEntry (x1, x2) g))).
      erewrite <-removeEntry_shift...
      revert dependent pf2; rewrite EQ2;
        rewrite removeEntry_swap.
      assert (removeEntry (n, n0) (removeEntry (x1, x2) g) =
              removeEntry (x1, x2) (removeEntry (n, n0) g)).
      apply removeEntry_swap...
      rewrite H0; intros.
      clear EQ2 H0.
      eapply typeCheck_impl with (pf1 := pf1').
      eauto.
      erewrite   removeEntry_swap with (a := (x1, x2)),removeEntry_swap with (a := (b1, b2)).
      eapply no_dup_cons_removeEntry_app...
      all:eauto.
      erewrite <-removeEntry_shift,<-removeEntry_shift...
      erewrite <-max_removeEntry_cons... 
      all:right; apply removeEntry_in...
    - intros.
      assert (pfx' : isMap (removeEntry (x1, x2) g1))...
      assert (pfx'' : isMap (removeEntry (x1, x2) g2))...
       assert (pfx : isMap (removeEntry (x1, x2) g))...
      destruct s1.
      + eapply tsuper_payload with (pf1 := pf1) in INb as IN1b.
      destruct IN1b as [q1 TYP1].
      assert (TP2:  exists t2 : piType, typeOf g2 (b1, b2) t2 /\ type_plus (Chan m q1 s1) t2 (Chan m p s1)). 
      eapply split_type_plus...
      destruct TP2 as [t2 [TYP2 TP2]].
      assert (EX: exists q, s = Chan m q s1).
      inversion TP; subst...
      destruct EX as [k EQ2]; subst.
      eapply tsuper_payload with (pf1 := pf1) in INx as IN1x.
      destruct IN1x as [k1 TYP1x].
      assert (TP3:  exists t2 : piType, typeOf g2 (x1, x2) t2 /\ type_plus (Chan m k1 s1) t2 (Chan m k s1)). 
      eapply split_type_plus...
      destruct TP3 as [r2 [TYP2x TP3]].
      
      assert (TP4 : exists w1 w2,
        type_plus (Chan m q1 s1)  (Chan m k1 s1) w1 /\
        type_plus t2 r2 w2 /\
        type_plus w1 w2 s2 /\
        (is_unrestricted (Chan m p s1) ->
         w1 =w2 /\ w2 = s2)).
      eapply type_plus_distr.
      eauto. eauto. eauto.
      intros; unfold is_unrestricted in H0;
        destruct H0; destruct H0; inversion H0; subst x x0 m.
      inversion TP2; subst.
      inversion H0. 
      assert (EQUN: q1 = p3 /\ p3 = (pol_cup q1 p3)).
      inversion TYP1; inversion TYP2; subst. 
      eapply split_plus_un with (pf1 := pf1) (pf2 := pf2) (pf3 := pf) (b1 := b1) (b2 := b2) (t := s1)...
      inversion TP3; inversion TYP1x; inversion TYP2x; subst.
      assert (EQUN2: k1 = p4 /\ p4 = (pol_cup k1 p4)).
      eapply split_plus_un with (pf1 := pf1) (pf2 := pf2) (pf3 := pf) (b1 := x1) (b2 := x2) (t := s1)...
      clear MIN; intuition; subst. tauto. rewrite H2 at 1...
      tauto. rewrite H5 at 1...

      destruct TP4 as [w1 [w2 [TP4 [TP5 TP6]]]].
      assert (pf' : isMap ((b1, b2, vis, w1):: removeEntry (b1, b2)  (removeEntry (x1, x2) g1))).
      eapply cons_removeEntry, no_dup_removeEntry_no_dup, no_dup_split_no_dup_l...
       assert (pf'' : isMap ((b1, b2, vis, w2):: removeEntry (b1, b2) (removeEntry (x1, x2) g2))).
       eapply cons_removeEntry, no_dup_removeEntry_no_dup, no_dup_split_no_dup_r...
        assert
         (TS2: tEnv_split
                 ((b1, b2, vis, w1):: removeEntry (b1, b2) (removeEntry (x1, x2) g1))
         ((b1, b2, vis, w2):: removeEntry (b1, b2) (removeEntry (x1, x2) g2))
         ((b1, b2, vis, s2):: removeEntry (b1, b2) (removeEntry (x1, x2) g))
         pf' pf'' pf0).
       eapply tEnv_split_add_vis with
           (pf1 := pfx') (pf2 := pfx'') (pf := pfx).
       eauto. intuition eauto. inversion  TP; subst.
       intros. destruct H0; destruct H0; inversion H0.
       intros.
       assert (is_unrestricted (Chan un p s1)).
       eapply un_is_unrestricted... intuition.
       eapply split_remove.
       eapply no_dup_split_no_dup_l...
       eapply no_dup_split_no_dup_r...
       all:eauto.
       eapply TPar with (pf1 := pf') (pf2 := pf'').
       eauto.
       all:fold pmap.
       
       specialize IHTC1 with
           (pf1 := pf') (s := (Chan m k1 s1)) (s1 := Chan m q1 s1).
       assert (TC3 : NoDup(domain g1)). eapply no_dup_split_no_dup_l...
       eapply IHTC1 in TC3.
       eauto.
       erewrite split_max...
       eapply fsuper_vis with (pf1 := pf1) in INx as FYP.
       inversion FYP as [FYP2 F2]. inversion FYP2; subst.
       assert (t =  Chan m k1 s1).
       eapply type_of_map with (g := g1)...
       subst...
       eauto. inversion TYP1. subst. eapply fsuper_flag with (pf1 := pf1) (f1 := f0) in INb as FYP2.
       subst...
       eauto. eauto. eauto. eauto.

       specialize IHTC2 with
           (pf1 := pf'') (s := r2) (s1 := t2).
       assert (TC3 : NoDup(domain g2)). eapply no_dup_split_no_dup_r...
       eapply IHTC2 in TC3.
       eauto.
       erewrite split_max with (g1 := g2) (g2 := g1) ...
       eapply split_comm...
       eapply fsuper_vis with (pf1 := pf1) (pf2 := pf2) in INx as FYP.
       inversion FYP as [F2 FYP2]. inversion FYP2; subst.
       assert (t =  r2).
       eapply type_of_map with (g := g2)...
       subst...
      
       eauto. inversion TYP2. subst. eapply fsuper_flag_r with (pf1 := pf1) (f1 := f0) in INb as FYP2.
       subst...
       eauto. eauto. eauto. eauto.
      + inversion TP; subst.
        assert (pf' : isMap ((b1, b2, vis, Top):: removeEntry (b1, b2)  (removeEntry (x1, x2) g1))).
      eapply cons_removeEntry, no_dup_removeEntry_no_dup, no_dup_split_no_dup_l...
       assert (pf'' : isMap ((b1, b2, vis, Top):: removeEntry (b1, b2) (removeEntry (x1, x2) g2))).
       eapply cons_removeEntry, no_dup_removeEntry_no_dup, no_dup_split_no_dup_r...

       assert
         (TS2: tEnv_split
                 ((b1, b2, vis, Top):: removeEntry (b1, b2) (removeEntry (x1, x2) g1))
         ((b1, b2, vis, Top):: removeEntry (b1, b2) (removeEntry (x1, x2) g2))
         ((b1, b2, vis, Top):: removeEntry (b1, b2) (removeEntry (x1, x2) g))
         pf' pf'' pf0).
       eapply tEnv_split_add_vis with
           (pf1 := pfx') (pf2 := pfx'') (pf := pfx).
       eauto. eauto. inversion  TP; subst.
       intros. inversion H0. intuition.
       eapply split_remove.
       eapply no_dup_split_no_dup_l...
       eapply no_dup_split_no_dup_r...
       all:eauto.
       eapply TPar with (pf1 := pf') (pf2 := pf'').
       eauto.
       all:fold pmap.
       
        specialize IHTC1 with
           (pf1 := pf') (s := Top) (s1 := Top).
       assert (TC3 : NoDup(domain g1)). eapply no_dup_split_no_dup_l...
       eapply IHTC1 in TC3.
       eauto.
        erewrite split_max... 
       eapply fsuper_vis with (pf1 := pf1) in INx as FYP.
       inversion FYP as [FYP2 F2]. inversion FYP2; subst.
       assert (t =  Top).
       eapply tsuper_top with (a1 := x1) (a2 := x2)in INx.       eapply type_of_map with (g := g1)...
       eauto. subst...
       eauto.
       eapply tsuper_top with (pf1 := pf1) in INb as K. inversion K; subst.
       assert (f= f0).
       eapply fsuper_flag with (pf1 := pf1) (pf2 := pf2) (pf := pf)...
       subst...
       eauto.
       eauto.

       specialize IHTC2 with
           (pf1 := pf'') (s := Top) (s1 := Top).
       assert (TC3 : NoDup(domain g2)). eapply no_dup_split_no_dup_r...
       eapply IHTC2 in TC3.
       eauto.
       erewrite split_max with (g1 := g2) (g2 := g1) ...
       eapply split_comm...

       eapply fsuper_vis with (pf1 := pf1) (pf2 := pf2) in INx as FYP.
       inversion FYP as [F2 FYP2]. inversion FYP2; subst.
       assert (t =  Top).
       eapply tsuper_top_r with (a1 := x1) (a2 := x2)in INx.       eapply type_of_map with (g := g2).
       eauto. subst...
       eauto.
       eapply tsuper_top_r with (pf2 := pf2) in INb as K. inversion K; subst.
       assert (f= f0).
       eapply fsuper_flag_r with (pf1 := pf1) (pf2 := pf2) (pf := pf).
       eauto. eauto. eauto. eauto.
       subst...
       eauto.
       subst...
       eauto.
      eapply tsuper_top_r with (pf2 := pf2) in INb as K. inversion K; subst.
       specialize fsuper_flag_r with (pf1 := pf1) (pf2 := pf2) (pf := pf) (a := (b1, b2)) (t := Top) (t1 := Top) (f := f) (f1 := f0) as FLAG.
       intuition; subst...
       eauto. eauto.
    - Case TOutL.
      assert (HIP: typeCheck g pf (dOut (fst u) (snd u) (fst v) (snd v) q))...
      assert (NONREC: nonRec_typable ((dOut (fst u) (snd u) (fst v) (snd v) q))).
      eapply typeCheck_object_neq_subject...
      assert (DIFF: u <> v).
      destruct u; destruct v; simpl in NONREC;
        unfold nonRec_typable in NONREC
        ; fold nonRec_typable in NONREC; intuition.
      intros.
      unfold pmap; fold pmap.
      destruct u as [u1 u2]; destruct v as [v1 v2]; simpl.

      case_eq (pair_eq (u1, u2) (x1, x2)).
      + intros PEQ.
        rewrite <-pairEq_eq in PEQ; inversion PEQ; subst.
        unfold mv; simpl; fold mv.
        assert (EQ1: true = (x1 =? x1)) by apply beq_nat_refl.
        assert (EQ2 : true = (x2 =? x2))  by apply beq_nat_refl.
        rewrite <-EQ1,<-EQ2, true_true, diff_false.
        assert (s = Chan lin p t).
        eapply type_of_map with (g := g)...
        subst; inversion TP; subst.
        inversion H as [TS [TP2 ABS]].
         assert ((b1, b2) <> (v1, v2)). intro ABS2; inversion ABS2; subst.
          destruct nonRecTypes as [NR1 NR2].
          assert (Chan lin p1 t = t').
          eapply type_of_map with (g := g)...
          subst. inversion H0. inversion H3.
          specialize NR1 with lin p1 t; contradiction.
          subst.
          specialize NR1 with lin empty t0; contradiction.
          subst.
          specialize NR1 with lin inp t0; contradiction.
          subst.
          specialize NR1 with lin out t0; contradiction.
        
        inversion TP2; subst. inversion H8; subst.
        *  assert (nd_pf' : NoDup (domain ((b1, b2, vis, Chan lin p1 t)
     :: (v1, v2, vis, t2)
        :: removeEntry (v1, v2)
             (removeEntry (b1, b2)
                ((b1, b2, vis, Chan lin p0 t)
                   :: removeEntry (b1, b2) (removeEntry (x1, x2) g)))))).
          rewrite removeEntry_swap.
          apply no_dup_cons_removeEntry_app. apply no_dup_cons_removeEntry, no_dup_removeEntry_no_dup...
          eauto. eauto.
           apply no_dup_isMap in nd_pf' as pf'.
          eapply TOutL with (u := (b1, b2)) (v := (v1, v2)) (p := p0) (t1 := Chan lin p1 t) (t := t) (pf1 := pf').
          unfold type_remove.
          split. eapply pol_plus_type_sub, pol_plus_comm...
          split. eapply Tp_LinPlus, pol_plus_comm...
          intros. destruct H4; destruct H4;  inversion H4.
          eauto. eauto.
          right. eapply removeEntry_in, removeEntry_in...
          assert (EQ3: removeEntry (v1, v2) (removeEntry (x1, x2) g) = removeEntry (x1, x2) (removeEntry (v1, v2) g)).
          apply removeEntry_swap...
          assert (EQ: pair_eq (x1, x2) (x1, x2) = true)...
           assert (K3 :  (v1, v2) <> (b1, b2))...
          rewrite pairEq_neq in K3.
          unfold removeEntry in IHTC.
          rewrite EQ, K3 in IHTC.
          fold removeEntry in IHTC.
          revert dependent pf'.
           assert (EQb: pair_eq (b1, b2) (b1, b2) = true)...
           unfold removeEntry.  rewrite EQb; fold removeEntry.
           rewrite removeEntry_swap. intros.
         
          
          specialize IHTC with (s2 := Chan lin p1 t) (pf1 := pf').

          assert (IH: NoDup
           (domain
              ((x1, x2, vis, Chan lin empty t)
                 :: (v1, v2, vis, t2) :: removeEntry (v1, v2) (removeEntry (x1, x2) g)))).
          rewrite EQ3; eapply no_dup_cons_removeEntry_app...
          eapply IHTC in IH.
          eauto.
          erewrite max_same_domain with (l := domain ((x1, x2, vis, Chan lin empty t) ::removeEntry (x1, x2) ((v1, v2, vis, t2) ::  removeEntry (v1, v2) g))).
          erewrite <-max_removeEntry_cons, <-max_removeEntry_cons. eauto. eauto. eapply in_g_in_domain...
          eapply no_dup_cons_removeEntry...
          simpl. right. eapply in_g_in_domain,removeEntry_in...
          rewrite <-removeEntry_shift with (a1 := x1),removeEntry_swap; intuition.
          eauto.
          instantiate (1 := Chan lin p1 t).
          right. right. eapply removeEntry_in, removeEntry_in. eauto.
          intro ABS2; inversion ABS2; subst.
          assert (Chan lin out t = Chan lin p1 t).
          eapply type_of_map with (x := (x1, x2)) (g := g)...
          inversion H4; subst. inversion H7.
          all:eauto.
        *  inversion H7; subst.
           assert (nd_pf' : NoDup (domain ((b1, b2, vis, Chan lin inp t)
     :: (v1, v2, vis, t2)
        :: removeEntry (v1, v2)
             (removeEntry (b1, b2)
                ((b1, b2, vis, Chan lin io t)
                   :: removeEntry (b1, b2) (removeEntry (x1, x2) g)))))).
          rewrite removeEntry_swap.
          apply no_dup_cons_removeEntry_app. apply no_dup_cons_removeEntry, no_dup_removeEntry_no_dup...
          eauto. eauto.
           apply no_dup_isMap in nd_pf' as pf'.
          eapply TOutL with (u := (b1, b2)) (v := (v1, v2)) (p := io) (t1 := Chan lin inp t) (t := t) (pf1 := pf').
          unfold type_remove.
          split. eapply pol_plus_type_sub, pol_plus_comm...
          split. eapply Tp_LinPlus, pol_plus_comm...
          intros. destruct H4; destruct H4;  inversion H4.
          eauto. eauto.
          right. eapply removeEntry_in, removeEntry_in...
          assert (EQ3: removeEntry (v1, v2) (removeEntry (x1, x2) g) = removeEntry (x1, x2) (removeEntry (v1, v2) g)).
          apply removeEntry_swap...
          assert (EQ: pair_eq (x1, x2) (x1, x2) = true)...
           assert (K3 :  (v1, v2) <> (b1, b2))...
          rewrite pairEq_neq in K3.
          unfold removeEntry in IHTC.
          rewrite EQ, K3 in IHTC.
          fold removeEntry in IHTC.
          revert dependent pf'.
           assert (EQb: pair_eq (b1, b2) (b1, b2) = true)...
           unfold removeEntry.  rewrite EQb; fold removeEntry.
           rewrite removeEntry_swap. intros.
          
          specialize IHTC with (s2 := Chan lin inp t) (pf1 := pf').

          assert (IH: NoDup
           (domain
              ((x1, x2, vis, Chan lin empty t)
                 :: (v1, v2, vis, t2) :: removeEntry (v1, v2) (removeEntry (x1, x2) g)))).
          rewrite EQ3; eapply no_dup_cons_removeEntry_app...
          eapply IHTC in IH.
          eauto.
          erewrite removeEntry_swap...
         erewrite max_same_domain with (l := domain ((x1, x2, vis, Chan lin empty t) ::removeEntry (x1, x2) ((v1, v2, vis, t2) ::  removeEntry (v1, v2) g))).
          erewrite <-max_removeEntry_cons, <-max_removeEntry_cons. eauto. eauto. eapply in_g_in_domain...
          eapply no_dup_cons_removeEntry...
          simpl. right. eapply in_g_in_domain,removeEntry_in...
          rewrite <-removeEntry_shift with (a1 := x1),removeEntry_swap; intuition. unfold domain; fold domain. eapply cons_cons_iff...
          instantiate (1 := Chan lin empty t).
          right. right. eapply removeEntry_in, removeEntry_in. eauto.
          intro ABS2; inversion ABS2; subst.
          assert (Chan lin io t = Chan lin empty t).
          eapply type_of_map with (x := (x1, x2)) (g := g)...
          inversion H4; subst. inversion H7.
          all:eauto.
        * eauto.
      + intros PNEQ.
        rewrite <-pairEq_neq in PNEQ.
        assert (PNEQ2: (x1, x2) <> (u1, u2)). intuition.
        apply diff_false in PNEQ2 as DIFF2.
        assert (EQ2: (x1 =? x1) && (x2 =? x2) = true). intuition.
        case_eq (pair_eq (v1, v2) (x1, x2)). intros PEQ.
        rewrite <-pairEq_eq in PEQ; inversion PEQ; subst.
        assert (t' = s).
        eapply type_of_map with (x := (x1, x2)) (g := g)...
        subst t'.
        unfold mv. simpl. rewrite DIFF2, EQ2.
        assert (LEM: exists t2,  type_remove s2 t t2).
        eapply type_remove_super...
        destruct LEM as [t'' TREM].
        assert (DIFF3: (u1, u2) <> (b1, b2)).
        intro ABS2; inversion ABS2; subst.
        assert (Chan lin p t = s1).
        eapply type_of_map with (x := (b1, b2)) (g := g)...
        subst. inversion H0 as [TS [TP2 ABS3]].
        inversion TP; inversion TP2; subst.
        inversion H10.
        destruct nonRecTypes as [NR1 NR2].
        specialize NR2 with lin lin lin p2 p5 p3 t3. intuition. inversion H10.
        assert (nd_pf'': NoDup (domain
                         (((u1, u2, vis, t1)
     :: (b1, b2, vis, t'')
        :: removeEntry (b1, b2)
             (removeEntry (u1, u2)
                          ((b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g))))))).
        rewrite removeEntry_swap.
        eapply no_dup_cons_removeEntry_app.
        eapply no_dup_cons_removeEntry, no_dup_removeEntry_no_dup...
        eauto. eauto.
        apply no_dup_isMap in nd_pf'' as pf''.
        
        eapply TOutL with (u := (u1, u2)) (v := (b1, b2)) (t' := s2) (t2 := t'') (pf1 := pf'').
        eauto.
        eauto. right. apply removeEntry_in, removeEntry_in.
        assumption.
        eauto.
        eauto.
        eauto.
        assert (EQ: (removeEntry (x1, x2)
                             ((u1, u2, vis, t1)
                              :: (x1, x2, vis, t2)
                              :: removeEntry (x1, x2) (removeEntry (u1, u2) g))) =
                   (((u1, u2, vis, t1) ::
                                       removeEntry (x1, x2)
                                  ( (x1, x2, vis, t2)
                                      :: removeEntry (x1, x2) (removeEntry (u1, u2) g))))).
        rewrite <-removeEntry_shift...
        unfold removeEntry at 4 in EQ.
        assert (EQ3:pair_eq (x1, x2) (x1, x2) = true). intuition. rewrite EQ3 in EQ.
        assert (EQ4 : (u1, u2, vis, t1) :: removeEntry (x1, x2) (removeEntry (u1, u2) g) =
                      (u1, u2, vis, t1) :: removeEntry (u1, u2) (removeEntry (x1, x2) g)).
        rewrite removeEntry_swap...
         rewrite EQ4 in EQ.
         rewrite EQ in IHTC.
         revert dependent pf''.
         assert (EQ5: removeEntry (b1, b2)
                      (removeEntry (u1, u2)
                                   ((b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g))) =
       removeEntry (u1, u2)
                      (removeEntry (b1, b2)
                                   ((b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g)))).
         rewrite removeEntry_swap...
         rewrite EQ5.
         unfold removeEntry.
         assert (EQ6 : pair_eq (b1, b2) (b1, b2) = true)... 
         rewrite EQ6.
         fold removeEntry.
         intros.
         assert (IH: NoDup
           (domain
              ((u1, u2, vis, t1)
                 :: (x1, x2, vis, t2) :: removeEntry (x1, x2) (removeEntry (u1, u2) g)))).
         rewrite removeEntry_swap.
         eapply no_dup_cons_removeEntry_app...
         eauto.
         specialize IHTC with (s2 := t'').
         assert (EQ7: (b1, b2, vis, t'')
                     :: removeEntry (b1, b2)
                          ((u1, u2, vis, t1)
                             :: removeEntry (u1, u2) (removeEntry (x1, x2) g)) =
                 (b1, b2, vis, t'')
                     :: (u1, u2, vis, t1) :: removeEntry (b1, b2) (removeEntry (u1, u2) (removeEntry (x1, x2) g))).     
         rewrite <-removeEntry_shift...
         rewrite EQ7 in IHTC.
         assert (nd_pf''': NoDup (domain
                                    
                    ((b1, b2, vis, t'')
                     :: (u1, u2, vis, t1)
                        :: removeEntry (b1, b2)
                        (removeEntry (u1, u2) (removeEntry (x1, x2) g))))).
         apply no_dup_cons_removeEntry_app. apply no_dup_removeEntry_no_dup...
         eauto.
         apply no_dup_isMap in nd_pf''' as pf'''.
         eapply IHTC with (pf1 := pf''') in IH.
         eapply typeCheck_impl.
         eauto.
         (*NoDup
    (domain
       ((u1, u2, vis, t1)
        :: (b1, b2, vis, t'') :: removeEntry (u1, u2) (removeEntry (b1, b2) (removeEntry (x1, x2) g))))*)
         eapply no_dup_cons_removeEntry_app...
         eauto.
         (*forall x : name * name * flag * piType,
  In x
    ((b1, b2, vis, t'')
     :: (u1, u2, vis, t1)
        :: removeEntry (b1, b2) (removeEntry (u1, u2) (removeEntry (x1, x2) g))) <->
  In x
    ((u1, u2, vis, t1)
     :: (b1, b2, vis, t'')
        :: removeEntry (u1, u2) (removeEntry (b1, b2) (removeEntry (x1, x2) g)))*)
         erewrite removeEntry_swap...
         erewrite removeEntry_swap...
         erewrite max_same_domain with (l := domain ((x1, x2, vis, Chan lin empty t) ::removeEntry (x1, x2) ((u1, u2, vis, t2) ::  removeEntry (u1, u2) g))).
          erewrite <-max_removeEntry_cons, <-max_removeEntry_cons. eauto. eauto. eapply in_g_in_domain...
          eapply no_dup_cons_removeEntry...
          simpl. right. eapply in_g_in_domain,removeEntry_in...
          rewrite <-removeEntry_shift with (a1 := x1),removeEntry_swap. unfold domain; fold domain. eapply cons_cons_iff...
         eauto. eauto. 
         
         eauto.
         case_eq (pair_eq (b1, b2) (x1, x2)).
         intros ABS; rewrite <-pairEq_eq in ABS; inversion ABS; subst; intuition.   
         intros; right;right. 
         eapply removeEntry_in, removeEntry_in.
         eapply pairEq_neq...
         intuition.

         eauto.
         (* s1 + s = s2 *)
         (* t + t'' = s2 *)
         (* t + t2 = s *)
         (* GOAL: s1 + t2 = t'' *)
         move TP at bottom.
         inversion H0 as [TS1 [TP3 ISUN1]];
           inversion  TREM as [TS2 [TP4 ISUN2]].
         clear TS1 TS2.
         destruct s. destruct m. destruct p0.
         inversion TP3; inversion H6; subst.
         assert (s1 = s2 /\ t'' = s2).
         inversion TP; inversion TP4; subst.
         inversion H8; inversion H13; subst...
         destruct H3; subst...
         assert (s1 = s2 /\ t'' = s2).
         inversion TP; inversion TP4; subst.
         inversion H8; inversion H13; subst...
         destruct H3; subst...
         inversion TP3. subst. inversion TP; subst.
         inversion H6; inversion H8; subst...
         inversion TP4; subst; eauto; inversion H7; subst...
         inversion TP4; subst; eauto; inversion H7; subst...
         inversion TP4; subst; eauto; inversion H7; subst...
         inversion TP4; subst; eauto; inversion H7; subst...
         inversion TP3. subst. inversion TP; subst.
         inversion H6; inversion H8; subst...
         inversion TP4; subst; eauto; inversion H7; subst...
         inversion TP4; subst; eauto; inversion H7; subst...
         inversion TP4; subst; eauto; inversion H7; subst...
         inversion TP4; subst; eauto; inversion H7; subst...
         inversion TP3. subst. inversion TP; subst.
         inversion H6; inversion H8; subst...
         inversion TP4; subst; eauto; inversion H7; subst...
         inversion TP4; subst; eauto; inversion H7; subst...
         inversion TP4; subst; eauto; inversion H7; subst...
         inversion TP4; subst; eauto; inversion H7; subst...
         assert (EQ9: is_unrestricted (Chan un p0 s)).
         eapply un_is_unrestricted...
         apply ISUN1 in EQ9. subst.
         inversion TP3; subst; inversion TP4; subst.
         assert (EQ8:  is_unrestricted (Chan un (pol_cup p1 p3) s)).
         eapply un_is_unrestricted...
         apply ISUN2 in EQ8. subst.
         clear ISUN1 ISUN2. inversion TP; inversion TP3; inversion TP4. rewrite H12, H12, EQ8, <-H8...
         inversion TP; inversion TP3; inversion TP4; subst...
         inversion H8. inversion H7.

         intros PNEQ3.
         rewrite <-pairEq_neq in PNEQ3.
        assert (PNEQ4: (x1, x2) <> (v1, v2)). intuition.
        apply diff_false in PNEQ4 as DIFF3.
         unfold mv. simpl.
         rewrite DIFF2, DIFF3.

         case_eq (pair_eq (u1, u2) (b1, b2)). intros PEQ3.
         rewrite <-pairEq_eq in PEQ3; inversion PEQ3; subst.
         assert (s1 = Chan lin p t).
         apply type_of_map with (x := (b1, b2)) (g := g)...
         subst.
         inversion TP; inversion H as [TS3 [TP5 ISUN]]; inversion TP5; subst.
         assert (PP: exists p3, pol_plus out p3 p0).
         eapply pol_plus_of_pol_plus...
         destruct PP as [p3 PP].

         assert (nd_pf'' :
                   NoDup
                     (domain (
                     ((b1, b2, vis, Chan lin p3 t)
     :: (v1, v2, vis, t2)
        :: removeEntry (v1, v2)
             (removeEntry (b1, b2)
                ((b1, b2, vis, Chan lin p0 t)
                   :: removeEntry (b1, b2) (removeEntry (x1, x2) g))))))).
         rewrite removeEntry_swap.
         eapply no_dup_cons_removeEntry_app.
         eapply no_dup_cons_removeEntry, no_dup_removeEntry_no_dup...
         eauto. eauto.
         apply no_dup_isMap in nd_pf'' as pf''.

         eapply TOutL with
             (p := p0) (t1 := Chan lin p3 t) (t := t)
             (pf1 := pf'').
         unfold type_remove.
         split. inversion PP...
         split. eapply Tp_LinPlus...
         intros. destruct H3. destruct H3; inversion H3; contradiction.
         eauto.
         eauto. right. eapply removeEntry_in, removeEntry_in.
         eauto. eauto. eauto.

          assert (IH: NoDup
           (domain
              ((b1, b2, vis, Chan lin p4 t)
               :: (v1, v2, vis, t2) :: removeEntry (v1, v2) (removeEntry (b1, b2) g))) ).
         rewrite removeEntry_swap.
         eapply no_dup_cons_removeEntry_app...
         eauto.
         specialize IHTC with (s2 := Chan lin p3 t).
         rewrite <-removeEntry_shift in IHTC.
         unfold removeEntry in IHTC.
         assert (EQ5: pair_eq (b1, b2) (b1, b2) = true)...
         assert (EQ6: pair_eq (v1, v2) (x1, x2) = false)...
         rewrite EQ5, EQ6 in IHTC.
         fold removeEntry in IHTC.
         rewrite removeEntry_swap in IHTC.
         assert (EQ7: ((b1, b2, vis, Chan lin p3 t)
                     :: (v1, v2, vis, t2)
                        :: removeEntry (x1, x2)
                             (removeEntry (b1, b2) (removeEntry (v1, v2) g)))  =
                ((b1, b2, vis, Chan lin p3 t)
                     :: (v1, v2, vis, t2)
                        :: removeEntry (b1, b2)
                        (removeEntry (v1, v2) (removeEntry (x1, x2) g)))).
         rewrite removeEntry_swap with (g := removeEntry (v1, v2) g).
         rewrite <-removeEntry_swap with (g := g) at 1...
         eauto. eauto.
         rewrite EQ7 in IHTC.
         revert dependent pf''.
         unfold removeEntry. 
         rewrite EQ5. fold removeEntry.
         rewrite removeEntry_swap.
         intros.
         rewrite removeEntry_swap in IH.
         eapply IHTC with (pf1 := pf'') (s1 := Chan lin p4 t) in IH.
         eauto.
         erewrite removeEntry_swap...
         erewrite max_same_domain with (l := domain ((b1, b2, vis, Chan lin p4 t) ::removeEntry (b1, b2) ((v1, v2, vis, t2) ::  removeEntry (v1, v2) g))).
          erewrite <-max_removeEntry_cons, <-max_removeEntry_cons. eauto. eauto. eapply in_g_in_domain...
          eapply no_dup_cons_removeEntry...
          simpl. right. eapply in_g_in_domain,removeEntry_in...
          rewrite <-removeEntry_shift,removeEntry_swap; intuition.   
          
         right. right.
         eapply removeEntry_in, removeEntry_in...
         assert (f = vis).
         apply flag_of_map with (x := (b1, b2)) (g := g)...
         subst...
         apply Tp_LinPlus...
         move H7 at bottom. move H11 at bottom. move PP at bottom. 
         (* out + p4 = p *)
         (* out + p3 = p0 *)
         (* p + p2 = p0 *)
         (* GOAL *)
         (* p4 + p2 = p3 *)
         eapply pol_plus_middle...
          eauto. eauto. eauto. eauto.

         intros PNEQ5. rewrite <-pairEq_neq in PNEQ5.
         case_eq (pair_eq (v1, v2) (b1, b2)).
         intros PEQ.
         rewrite <-pairEq_eq in PEQ; inversion PEQ; subst.
         assert (t' = s1).
         apply type_of_map with (x := (b1, b2)) (g := g)...
         subst.
       
         assert (EX: exists t'', type_remove s2 t t'').
         destruct s2. destruct m.
         inversion H0 as [TS2 [TP3  ISUN]].
         unfold type_remove.
         
         assert (EX: exists w, type_plus t w (Chan lin p0 s2)).
         eapply plus_sub_exists_2.
         eauto. eauto.
         destruct EX as [t'' TP4].
         exists t''.
         split. eauto. split. eauto.
         intros . destruct H3; destruct H3; inversion H3; contradiction.
         inversion TP; inversion H0 as [TS [TP2 ISUN]]; subst.
         assert (EQ: is_unrestricted (Chan un p1 s2)).
         eapply un_is_unrestricted...
         apply ISUN in EQ; subst.
         inversion TP2; subst.
         exists ( (Chan un (pol_cup (pol_cup p0 p1) p2) s2))...
         unfold type_remove. 
         assert (POLEQ: (pol_cup (pol_cup p0 p1) p2) =
                 pol_cup p0 (pol_cup (pol_cup p0 p1) p2)).
         destruct p0,p1,p2...
         clear MIN; intuition.
         (* type_sub (Chan un p0 s2) (Chan un (pol_cup (pol_cup p0 p1) p2) s2) *)
         erewrite POLEQ; eapply pol_cup_type_sub...
         assert (EQ: (pol_cup (pol_cup p0 p1) p2) =
                pol_cup p0 (pol_cup (pol_cup p0 p1) p2)).
         destruct p0,p1,p2...
         rewrite EQ at 2...
         exists Top. inversion TP; inversion H0; inversion H5; subst.
         econstructor...
         inversion H8. inversion H8. inversion H8.
         
         destruct EX as [t'' TREM2].
          assert (nd_pf' : NoDup
                   (domain ((u1, u2, vis, t1)
     :: (b1, b2, vis, t'')
        :: removeEntry (b1, b2)
             (removeEntry (u1, u2)
                          ((b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g)))))).
          rewrite removeEntry_swap.
          unfold removeEntry.
          assert (EQ5 :  pair_eq (b1, b2) (b1, b2) = true).
          eauto.
          rewrite EQ5. fold removeEntry.
          eapply no_dup_cons_removeEntry_app.
          eapply no_dup_removeEntry_no_dup...
          eauto. eauto.
          apply no_dup_isMap in nd_pf' as pf'.
          eapply TOutL with
              (t' := s2 ) (t2 := t'') (t := t) (pf1 := pf').
          eauto. eauto.
         right; eapply removeEntry_in, removeEntry_in...
         eauto.
         
         assert (IH:
           NoDup
           (domain
              ((u1, u2, vis, t1)
               :: (b1, b2, vis, t2) :: removeEntry (u1, u2) (removeEntry (b1, b2) g)))).
         eapply no_dup_cons_removeEntry_app...
         rewrite removeEntry_swap in IH; 
         move IHTC before IH.
         specialize IHTC with (s2 := t'').
         rewrite <-removeEntry_shift, <-removeEntry_shift in IHTC.
         rewrite removeEntry_swap with  (g := ((b1, b2, vis, t2)
                                 :: removeEntry (b1, b2) (removeEntry (u1, u2) g))) in IHTC.
         
         unfold removeEntry in IHTC.
         assert (EQ5: pair_eq (b1, b2) (b1, b2) = true)...
         assert (EQ6: pair_eq (u1, u2) (x1, x2) = false)...
         assert (EQ7: pair_eq (u1, u2) (b1, b2) = false).
         eapply pairEq_neq...
         rewrite EQ5 in IHTC. fold removeEntry in IHTC.
         rewrite removeEntry_swap with (g := (removeEntry (u1, u2) g)) in IHTC.
         assert (EQ8 :
                   removeEntry (b1, b2)
                             (removeEntry (x1, x2) (removeEntry (u1, u2) g)) = removeEntry (b1, b2)
                             (removeEntry (u1, u2) (removeEntry (x1, x2) g))).
         rewrite removeEntry_swap with (g := g)...
         rewrite EQ8 in IHTC.
         assert (nd_pf'': NoDup
           (domain
              ((b1, b2, vis, t'')
                 :: (u1, u2, vis, t1) :: removeEntry (b1, b2) (removeEntry (u1, u2) (removeEntry (x1, x2) g))))).
         
         eapply no_dup_cons_removeEntry_app.
         eapply no_dup_removeEntry_no_dup...
         assert ( (u1, u2) <> (b1, b2)). 
         apply pairEq_neq... intuition.
         apply no_dup_isMap in nd_pf'' as pf''.
         eapply IHTC with (pf1 := pf'') in IH.
         move IH at bottom.
         revert dependent pf'.
         rewrite removeEntry_swap with (g := ((b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g))).
         unfold removeEntry; rewrite EQ5; fold removeEntry.
         rewrite removeEntry_swap with (g :=  (removeEntry (x1, x2) g)).
         intros.
         eapply typeCheck_impl with (pf1 := pf'').
         (* NoDup
    (domain
       ((b1, b2, vis, t'')
        :: (u1, u2, vis, t1) :: removeEntry (b1, b2) (removeEntry (u1, u2) (removeEntry (x1, x2) g))))*)
         eapply no_dup_cons_removeEntry_app...
         (*NoDup
    (domain
       ((u1, u2, vis, t1)
        :: (b1, b2, vis, t'') :: removeEntry (b1, b2) (removeEntry (u1, u2) (removeEntry (x1, x2) g))))*)
         erewrite removeEntry_swap.
           eapply no_dup_cons_removeEntry_app...
           eauto.
           eauto.
         (* forall x : name * name * flag * piType,
  In x
    ((b1, b2, vis, t'')
     :: (u1, u2, vis, t1)
        :: removeEntry (b1, b2) (removeEntry (u1, u2) (removeEntry (x1, x2) g))) <->
  In x
    ((u1, u2, vis, t1)
     :: (b1, b2, vis, t'')
        :: removeEntry (b1, b2) (removeEntry (u1, u2) (removeEntry (x1, x2) g)))*)
         eauto.
         eauto. eauto.
         erewrite removeEntry_swap...
         erewrite max_same_domain with (l := domain ((u1, u2, vis, t1) ::removeEntry (u1, u2) ((b1, b2, vis, t2) ::  removeEntry (b1, b2) g))).
          erewrite <-max_removeEntry_cons, <-max_removeEntry_cons. eauto. eauto. eapply in_g_in_domain...
          eapply no_dup_cons_removeEntry...
          simpl. right. eapply in_g_in_domain,removeEntry_in...
          rewrite <-removeEntry_shift; intuition. 
         right. right. eapply removeEntry_in. eauto.
         eapply removeEntry_in...
         right. assert (f = vis).
         apply flag_of_map with (x := (b1, b2)) (g := g)...
         subst...
         move H0 at bottom.
         move TP at bottom. move TREM2 at bottom.
         clear IHTC.
         inversion H0 as [TS1 [TP2 ISUN]]; clear H0.
         inversion TREM2 as [TS2 [TP3 ISUN2]]; clear TREM2.
         clear TS1 TS2.
         destruct s. destruct m.
         inversion TP. subst.
         inversion TP2; inversion TP3; subst...
         inversion H9; subst.
         eapply Tp_LinPlus, pol_plus_middle...
         inversion TP; subst. inversion TP2; inversion TP3; subst.
         inversion H4; subst.
         assert (UN2: is_unrestricted (Chan un (pol_cup (pol_cup p2 p3) p0) s)).  eapply un_is_unrestricted...
         assert (UN: is_unrestricted (Chan un (pol_cup p2 p3) s)). eapply un_is_unrestricted...
         apply ISUN2 in UN2; apply ISUN in UN.
         rewrite UN, UN2...
         inversion TP; inversion TP2; inversion TP3; subst...
         all: try discriminate.

         eauto. eauto. eauto. eauto. eauto.


         intros PNEQ6. rewrite <-pairEq_neq in PNEQ6.
         assert (nd_pf':
                   NoDup (domain
          ((u1, u2, vis, t1)
     :: (v1, v2, vis, t2)
        :: removeEntry (v1, v2)
             (removeEntry (u1, u2)
                          ((b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g)))))).
         rewrite removeEntry_swap with (g := ((b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g))).
         eapply no_dup_cons_removeEntry_app.
         eapply no_dup_cons_removeEntry, no_dup_removeEntry_no_dup...
         eauto. eauto.
         apply no_dup_isMap in nd_pf' as pf'.
         eapply TOutL with (pf1 := pf').
         eauto.
         eauto.
         right; apply removeEntry_in, removeEntry_in...
         right; apply removeEntry_in, removeEntry_in...
         move IHTC at bottom.
         rewrite <-removeEntry_shift with (b1 := u1) (b2 := u2) in IHTC.
         rewrite <-removeEntry_shift with (b1 := v1) (b2 := v2) in IHTC.
         rewrite <-removeEntry_shift with (b1 := u1) (b2 := u2) in IHTC.
         rewrite <-removeEntry_shift with (b1 := v1) (b2 := v2) in IHTC.
          rewrite removeEntry_swap with (g := g) in IHTC.
          rewrite removeEntry_swap with (g := (removeEntry (v1, v2) g)) in IHTC.
          assert (EQ8: (removeEntry (u1, u2)
                                    (removeEntry (x1, x2) (removeEntry (v1, v2) g)))=
removeEntry (u1, u2)
            (removeEntry (v1, v2) (removeEntry (x1, x2) g))).
          rewrite removeEntry_swap with (g := g)...
          rewrite EQ8 in IHTC.
          assert (EQ9 :
                    removeEntry (b1, b2)
                                (removeEntry (u1, u2) (removeEntry (v1, v2) (removeEntry (x1, x2) g))) =
          removeEntry (u1, u2)
                      (removeEntry (v1, v2) (removeEntry (b1, b2) (removeEntry (x1, x2) g)))).
          rewrite removeEntry_swap with (g :=(removeEntry (v1, v2) (removeEntry (x1, x2) g))) .
          rewrite removeEntry_swap with (g := (removeEntry (x1, x2) g))...
          eauto.
          rewrite EQ9 in IHTC.
          assert (nd_pf'': NoDup (domain
                    ((b1, b2, vis, s2)
                     :: (u1, u2, vis, t1)
                        :: (v1, v2, vis, t2)
                           :: removeEntry (u1, u2)
                                (removeEntry (v1, v2)
                                             (removeEntry (b1, b2) (removeEntry (x1, x2) g)))))).
          unfold domain. fold domain.
          eapply NoDup_cons_iff. split. intro ABS.
          inversion ABS as [ABS1 | ABS2]. contradiction.
          inversion ABS2 as [ABS3 | ABS4]. contradiction.
          eapply in_domain_in_g in ABS4.
          destruct ABS4 as [f4 [t4 ABS4]]. 
          eapply in_removeEntry, in_removeEntry in ABS4.
          assert (~ In (b1, b2, f4, t4) (removeEntry (b1, b2) (removeEntry (x1, x2) g))).
          eapply no_dup_not_in_removeEntry, no_dup_removeEntry_no_dup...
          contradiction.
          eapply no_dup_cons_removeEntry_app...
          apply no_dup_isMap in nd_pf'' as pf''.
          assert (IH : NoDup
           (domain
              ((u1, u2, vis, t1)
                 :: (v1, v2, vis, t2) :: removeEntry (u1, u2) (removeEntry (v1, v2) g)))).
          eapply no_dup_cons_removeEntry_app...
          eapply IHTC with (pf1 := pf'') (s2 := s2) in IH.
          eapply typeCheck_impl with (pf1 := pf'').
          (*NoDup
    (domain
       ((u1, u2, vis, t1)
        :: (v1, v2, vis, t2)
           :: removeEntry (v1, v2)
                (removeEntry (u1, u2) ((b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g)))))*)
          erewrite
            removeEntry_swap with (a := (v1, v2)),
            removeEntry_swap with (a := (u1, u2)),
                                  removeEntry_shift,removeEntry_shift.
          eapply no_dup_cons_removeEntry,no_dup_cons_removeEntry_app...
          eauto. eauto. eauto. eauto.
          (* NoDup
    (domain
       ((u1, u2, vis, t1)
        :: (v1, v2, vis, t2)
           :: removeEntry (v1, v2)
                (removeEntry (u1, u2) ((b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g)))))*)
          erewrite removeEntry_swap.
          eapply no_dup_cons_removeEntry_app.
          eapply no_dup_cons_removeEntry...
          eauto. eauto.
          eauto.
          (*forall x : name * name * flag * piType,
  In x
    ((b1, b2, vis, s2)
     :: (u1, u2, vis, t1)
        :: (v1, v2, vis, t2)
           :: removeEntry (u1, u2)
                (removeEntry (v1, v2) (removeEntry (b1, b2) (removeEntry (x1, x2) g)))) <->
  In x
    ((u1, u2, vis, t1)
     :: (v1, v2, vis, t2)
        :: removeEntry (v1, v2)
             (removeEntry (u1, u2)
                ((b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g))))*)
          erewrite <-removeEntry_shift with (a1 := u1).
          erewrite <-removeEntry_shift with (a1 := v1).
          erewrite removeEntry_swap.
          eapply cons_cons_cons_iff...
          eauto. eauto. eauto.
          erewrite removeEntry_swap...
         erewrite max_same_domain with (l := domain ((u1, u2, vis, t1) ::removeEntry (u1, u2) ((v1, v2, vis, t2) ::  removeEntry (v1, v2) g))).
          erewrite <-max_removeEntry_cons, <-max_removeEntry_cons. eauto. eauto. eapply in_g_in_domain...
          eapply no_dup_cons_removeEntry...
          simpl. right. eapply in_g_in_domain,removeEntry_in...
          rewrite <-removeEntry_shift,removeEntry_swap; intuition.
          right; right. eapply removeEntry_in, removeEntry_in...
          right; right. eapply removeEntry_in, removeEntry_in...
          all:eauto.
          Unshelve. all:eauto.
    - Case TOutUn.
       assert (HIP: typeCheck g pf (dOut (fst u) (snd u) (fst v) (snd v) q))...
      assert (NONREC: nonRec_typable ((dOut (fst u) (snd u) (fst v) (snd v) q))).
      eapply typeCheck_object_neq_subject...
      assert (DIFF: u <> v).
      destruct u; destruct v; simpl in NONREC;
        unfold nonRec_typable in NONREC
        ; fold nonRec_typable in NONREC; intuition.
      intros.
      unfold pmap; fold pmap.
      destruct u as [u1 u2]; destruct v as [v1 v2]; simpl.

      case_eq (pair_eq (u1, u2) (x1, x2)).
      + intros PEQ.
        rewrite <-pairEq_eq in PEQ; inversion PEQ; subst.
        unfold mv; simpl; fold mv.
        assert (EQ1: true = (x1 =? x1)) by apply beq_nat_refl.
        assert (EQ2 : true = (x2 =? x2))  by apply beq_nat_refl.
        rewrite <-EQ1,<-EQ2, true_true, diff_false; simpl.
        assert (s = Chan un p t).
        eapply type_of_map with (g := g)...
        subst; inversion TP; subst;
          inversion H0 as [TS [TP2 ABS]].
        (* (b1, b2) <> (v1, v2) *)
        case_eq (pair_eq (b1, b2) (v1, v2)); intros PEQ2.
        erewrite <-pairEq_eq in PEQ2; inversion PEQ2; subst.
         assert (Chan un p1 t = t').
          eapply type_of_map with (g := g)...
          subst. move H0 at bottom.  inversion H0; destruct H4.
          assert (is_unrestricted (Chan un p1 t)). eapply un_is_unrestricted... eapply H5 in H6; subst.
          inversion H4; subst.
          destruct nonRecTypes as [NR1 NR2].
          specialize NR1 with un p0 t0; contradiction.
          assert (DIFF2 :=PEQ2). rewrite <-pairEq_neq in PEQ2 .          

          assert (nd_pf': NoDup (domain (((v1, v2, vis, t2)
    :: removeEntry (v1, v2)
         ((b1, b2, vis, Chan un (pol_cup p1 p) t)
            :: removeEntry (b1, b2) (removeEntry (x1, x2) g)))))).
          eapply no_dup_cons_removeEntry,no_dup_cons_removeEntry...
          eapply no_dup_isMap in nd_pf' as pf'.
          
        eapply TOutUn with (u := (b1, b2)) (v := (v1, v2)) (p := (pol_cup p1 p)) (t' := t') (pf1 := pf').
         destruct p1, p;inversion H;try discriminate...
         eauto.
         eauto.
         right.  eapply removeEntry_in,removeEntry_in...

         
         assert (nd_pf'' : NoDup (domain (
           ((b1, b2, vis, Chan un (pol_cup p1 p) t)
            :: removeEntry (b1, b2)
                 (removeEntry (x1, x2) ((v1, v2, vis, t2) :: removeEntry (v1, v2) g)))))).
         eapply no_dup_cons_removeEntry, no_dup_removeEntry_no_dup,no_dup_cons_removeEntry...
         eapply no_dup_isMap in nd_pf'' as pf''.
         eapply typeCheck_impl with (pf1 := pf'').
         eauto.
         eauto.
         eapply IHTC.
         erewrite <-max_removeEntry_cons...
         eapply no_dup_cons_removeEntry...
         right; eapply removeEntry_in...
         right; eapply removeEntry_in...
         econstructor.
         rewrite <-removeEntry_shift,<-removeEntry_shift,
         <-removeEntry_shift,removeEntry_swap with (a := (v1, v2)),removeEntry_swap with (a := (v1, v2)).
         eapply cons_cons_iff.
         all:eauto.
         
      + intros PNEQ. assert (DIFF2 := PNEQ). rewrite <-pairEq_neq in DIFF2.
        unfold mv, pair_eq in *; fold mv;  rewrite PNEQ; simpl.

        (* (x1, x2) = (v1, v2) *)
        case_eq (pair_eq (v1, v2) (x1, x2)); intros PEQ.
        * assert (EQ := PEQ); unfold pair_eq in PEQ; simpl in PEQ; rewrite PEQ.
          rewrite <-pairEq_eq in EQ; inversion EQ; subst v1 v2.
          simpl.
          assert (s = t').
          eapply type_of_map with (g := g)... subst t'.
          case_eq (pair_eq (u1, u2) (b1, b2)); intros ABS.
          rewrite <-pairEq_eq in ABS; inversion ABS; subst.
          assert (Chan un p t = s1).
          eapply type_of_map with (g := g)...
          subst.
          inversion TP; inversion H0; destruct H8; subst.
          assert (ISUN: is_unrestricted (Chan un p2 t)).
          eapply un_is_unrestricted...
          eapply H9 in ISUN. subst. inversion H8. subst.
          destruct nonRecTypes as [NR1 NR2].
          specialize NR1 with un p1 t0; contradiction.

          rewrite <-pairEq_neq in ABS.

          assert (TREM := H0).
          eapply type_remove_super in H0 as TREM2...
          destruct TREM2 as (t'' &TREM2).
          assert (nd_pf' : NoDup (domain ( ((b1, b2, vis, t'')
     :: removeEntry (b1, b2)
     ((b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g))) ))).
          eapply no_dup_cons_removeEntry,no_dup_cons_removeEntry,no_dup_removeEntry_no_dup...
          eapply no_dup_isMap in nd_pf' as pf'.
          eapply TOutUn with (u := (u1, u2)) (v := (b1, b2)) (p := p) (t := t) (t2 := t'') (pf1 := pf').
          eauto.
          eauto.
          right. eapply removeEntry_in,removeEntry_in...
          eauto.
          assert (IH : NoDup (domain ((x1, x2, vis, t2) :: removeEntry (x1, x2) g))).
          eapply no_dup_cons_removeEntry...
          assert (EQx: pair_eq (x1, x2) (x1, x2) = true).
          eapply pairEq_eq...
          assert (nd_pf'' : NoDup (domain (((b1, b2, vis, t'')
          :: removeEntry (b1, b2)
          (removeEntry (x1, x2) ((x1, x2, vis, t2) :: removeEntry (x1, x2) g))) ))).
          eapply no_dup_cons_removeEntry.
          simpl. 
          rewrite EQx. eapply no_dup_removeEntry_no_dup...
          eapply no_dup_isMap in nd_pf'' as pf''.
          eapply IHTC  with (s1 := s1) (s := t2) (s2 := t'') (pf1 := pf'') in IH.
          revert dependent pf'.
           assert (EQb: pair_eq (b1, b2) (b1, b2) = true).
           eapply pairEq_eq...
           revert dependent nd_pf''.
           simpl. erewrite EQb. intros.
           
           revert dependent pf''.
           simpl. rewrite EQx. intros...
          erewrite <-max_removeEntry_cons...
          eauto.
          right; eapply removeEntry_in...
          (*  type_plus s1 t2 t'' *)
          destruct TREM as (TS1 &TP1 &ISUN1).
          destruct TREM2 as (TS2 &TP2 &ISUN2).
          destruct s2. destruct m.
           inversion TP1; inversion TP2; subst; inversion TP; subst; econstructor; inversion H8; subst.
             destruct p0,p1,p2,p3,p5,p6; try inversion H6;
               try inversion H10;try inversion H3...
             assert (ISUN3: is_unrestricted (Chan un p0 s2)). eapply un_is_unrestricted...
             eapply ISUN2 in ISUN3. inversion ISUN3; subst.
             inversion TP1; inversion TP2; subst; inversion TP; subst; inversion H7; subst.
             rewrite ISUN1,H11...
             eapply un_is_unrestricted...

             inversion TP1; inversion TP2; subst; inversion TP; subst...
      

             (*x1, x2) <> (v1, v2*)
        * assert (DIFF3 := PEQ); unfold pair_eq in PEQ;
            simpl in PEQ; rewrite PEQ; simpl;
              rewrite <-pairEq_neq in DIFF3.
          assert (TREM := H0).
          case_eq (pair_eq (v1, v2) (b1, b2)); intros PNEQ2.
          (* (v1, v2) = (b1, b2) *)
          ** assert (EQ:= PNEQ2); rewrite <-pairEq_eq in EQ; inversion EQ; subst.
             assert (K := TREM); destruct K as (TS2 &TP2 &ISUN2).
              assert (EQ2: f = vis /\ s1 = t'). 
              eapply in_isMap with (g := g)...
              destruct EQ2; subst f s1.
              assert (EX: exists t3,
                         type_plus t2 s t3).
              eapply type_plus_distr2...
              destruct EX as (t3 &TP3).
              assert (nd_pf' : NoDup(domain ( ((b1, b2, vis, t3)
                                                 :: removeEntry (b1, b2) ((b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g)))))).
              eapply no_dup_cons_removeEntry,
              no_dup_cons_removeEntry,
              no_dup_removeEntry_no_dup...
              eapply no_dup_isMap in nd_pf' as pf'.
             eapply TOutUn with (u := (u1, u2)) (v := (b1, b2)) (p := p) (t := t) (t' := s2) (t2 := t3) (pf1 := pf').
             eauto.
             
             (* type_remove s2 t t3*)
             destruct s2. destruct m.
             inversion TP;subst;inversion TP2; subst;
               inversion TP3; subst.
             econstructor.
             assert (EX: exists p', pol_plus p3 p' p0).
             eapply pol_plus_of_pol_plus...
             destruct EX as (p' & EX).
             eapply type_plus_type_sub...
             split.
             econstructor.
             destruct p0,p1,p2,p3,p4,p7;
               try inversion H9;
               try inversion H6;
               try inversion H7;
               try discriminate...
             intros ABS; destruct ABS as (ff &tt &ABS); try discriminate.
             inversion TP;subst;inversion TP2; subst;
               inversion TP3; subst.
             assert (EQ2: pol_cup (pol_cup p0 p3) p2  = pol_cup p0 (pol_cup p3 p2)).
             destruct p0,p2,p3...
             erewrite EQ2.
             econstructor.
             eapply type_plus_type_sub...
             split.
             econstructor...
             assert (ISUN3: is_unrestricted (Chan un (pol_cup p0 p3) s2) ). eapply un_is_unrestricted...
             eapply ISUN2 in ISUN3. inversion ISUN3.
             intros _. rewrite <-H4,<-EQ2, <-H4...
             inversion TP;subst;inversion TP2; subst;
               inversion TP3; subst...
             right; eapply removeEntry_in, removeEntry_in...
             eauto.
             assert (IH : NoDup (domain ((b1, b2, vis, t2) :: removeEntry (b1, b2) g))).
             eapply no_dup_cons_removeEntry...
             assert (nd_pf'' : NoDup (domain (((b1, b2, vis, t3)
          :: removeEntry (b1, b2)
          (removeEntry (x1, x2) ((b1, b2, vis, t2) :: removeEntry (b1, b2) g))) ))).
             eapply no_dup_cons_removeEntry,
             no_dup_removeEntry_no_dup,no_dup_cons_removeEntry...
             eapply no_dup_isMap in nd_pf'' as pf''.
             eapply IHTC with (s1 := t2) (s := s) (s2 := t3) (pf1 := pf'') in IH.
             revert dependent pf'.
             simpl.
             assert (EQ2:  pair_eq (b1, b2) (b1, b2) = true).
             eapply pairEq_eq...
             rewrite EQ2.
             intros. 
             revert dependent pf''.
             rewrite removeEntry_swap.
             simpl. rewrite EQ2.
              rewrite removeEntry_swap.
             intros...
             eauto.
             eauto.
             erewrite <-max_removeEntry_cons...
             right; eapply removeEntry_in...
             eauto.
             eauto.
          ** (*  (v1, v2) <> (b1, b2) *)
            rewrite <-pairEq_neq in PNEQ2.

            case_eq (pair_eq (u1, u2) (b1, b2)); intros PEQ2.  rewrite <-pairEq_eq in PEQ2; inversion PEQ2; subst.
            (* (u1, u2) = (b1, b2) *)
             *** assert (s1 = Chan un p t).
                 eapply type_of_map with (g := g)...
                 subst.
                 inversion TP; subst.
                 
            assert (nd_pf' : NoDup(domain ( ((v1, v2, vis, t2)
                                                 :: removeEntry (v1, v2) ((b1, b2, vis, Chan un (pol_cup p p2) t) :: removeEntry (b1, b2) (removeEntry (x1, x2) g)))))).
              eapply no_dup_cons_removeEntry,
              no_dup_cons_removeEntry,
              no_dup_removeEntry_no_dup...
              eapply no_dup_isMap in nd_pf' as pf'.
             eapply TOutUn with (u := (b1, b2)) (v := (v1, v2)) (p :=  (pol_cup p p2)) (t := t) (t' := t') (pf1 := pf').
             destruct H; subst. left...
             destruct p2. right... left...  right... left...            eauto.
             eauto.
             right; eapply removeEntry_in,removeEntry_in...

             (*  typeCheck
    ((v1, v2, vis, t2)
     :: removeEntry (v1, v2)
          ((b1, b2, vis, Chan un (pol_cup p p2) t)
           :: removeEntry (b1, b2) (removeEntry (x1, x2) g))) pf' 
    (pmap q x1 x2 b1 b2) *)
             assert (IH : NoDup (domain ((v1, v2, vis, t2) :: removeEntry (v1, v2) g))).
             eapply no_dup_cons_removeEntry...
             assert (nd_pf'' : NoDup (domain (((b1, b2, vis, Chan un (pol_cup p p2) t)
          :: removeEntry (b1, b2)
               (removeEntry (x1, x2) ((v1, v2, vis, t2) :: removeEntry (v1, v2) g)))))).
             eapply no_dup_cons_removeEntry,
             no_dup_removeEntry_no_dup,no_dup_cons_removeEntry...
             eapply no_dup_isMap in nd_pf'' as pf''.
             eapply IHTC with  (s2 := Chan un (pol_cup p p2) t) (pf1 := pf'') in IH.
             revert dependent nd_pf'; revert dependent pf'.
             rewrite <-removeEntry_shift.
             revert dependent nd_pf''. revert dependent pf''.
             rewrite <-removeEntry_shift,<-removeEntry_shift,removeEntry_swap with (a := (x1, x2)). intros.
             revert dependent nd_pf' . revert dependent pf'.
             rewrite removeEntry_swap.
             intros.

             eapply typeCheck_impl with (pf1 := pf'').
             eauto.
             eauto.
             eauto.
             eapply cons_cons_iff...
             
             eauto.
             eauto.
             eauto.
             eauto.
             eauto.
             erewrite <-max_removeEntry_cons...
             right; eapply removeEntry_in...
             right; eapply removeEntry_in...
             eauto.
             ***
               (* (u1, u2) <> (b1, b2)  *)
               rewrite <-pairEq_neq in PEQ2.
               assert (nd_pf' : NoDup (domain (((v1, v2, vis, t2)
     :: removeEntry (v1, v2)
     ((b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g)))))).
               eapply no_dup_cons_removeEntry,
               no_dup_cons_removeEntry,no_dup_removeEntry_no_dup...
               eapply no_dup_isMap in nd_pf' as pf'.
               eapply TOutUn with (u := (u1, u2)) (v := (v1, v2)) (t :=t) (pf1 := pf').
               eauto.
               eauto.
               right; eapply removeEntry_in,removeEntry_in...
               right; eapply removeEntry_in,removeEntry_in...
               (*  typeCheck
    ((v1, v2, vis, t2)
     :: removeEntry (v1, v2)
          ((b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g))) pf'
    (pmap q x1 x2 b1 b2) *)
               assert (IH:  NoDup (domain ((v1, v2, vis, t2) :: removeEntry (v1, v2) g))).
               eapply no_dup_cons_removeEntry...
               assert (nd_pf'' : NoDup (domain (((b1, b2, vis, s2)
          :: removeEntry (b1, b2)
          (removeEntry (x1, x2) ((v1, v2, vis, t2) :: removeEntry (v1, v2) g)))))).
               eapply no_dup_cons_removeEntry,
               no_dup_removeEntry_no_dup,no_dup_cons_removeEntry...
               eapply no_dup_isMap in nd_pf'' as pf''.
               eapply IHTC with (pf1 := pf'') in IH.
               eapply typeCheck_impl with (pf1 := pf'')...
               rewrite <-removeEntry_shift,<-removeEntry_shift,<-removeEntry_shift,removeEntry_swap with (a := (x1,x2)),removeEntry_swap.
               eapply cons_cons_iff...
               eauto.
               eauto.
               eauto.
               eauto.
               eauto.
               erewrite <-max_removeEntry_cons...
               right; eapply removeEntry_in...
               right; eapply removeEntry_in...
               eauto.
               Unshelve.
               all:eauto.
               
    - Case TInL. intros. 
      destruct x as [y1 y2];
         destruct u as [u1 u2]; unfold fst, snd.  
      assert (DIFF1 : (y1, y2) <> (b1, b2)).
      intros ABS; inversion ABS; subst;
        eapply in_g_in_domain in INb; contradiction.
      assert (DIFF2 : (y1, y2) <> (u1, u2)).
        intros ABS; inversion ABS; subst;
          eapply in_g_in_domain in H0; contradiction.
         assert (DIFF3: (y1, y2) <> (x1, x2)).
           intros ABS; inversion ABS; subst;
             eapply in_g_in_domain in INx; contradiction.
      assert (IH :  NoDup (domain ((u1, u2, vis, t1) :: (y1, y2, vis, t) :: removeEntry (u1, u2) g))).
      erewrite removeEntry_shift.
      eapply no_dup_cons_removeEntry,NoDup_cons...
      eauto.
      case_eq (pair_eq (u1, u2) (x1, x2)); intros EQ; assert (PEQ :=EQ); try rewrite <-pairEq_eq in EQ; inversion EQ; subst. 
      + simpl; unfold mv;
      unfold pair_eq in PEQ; rewrite PEQ;
        simpl.
        assert (s = Chan lin p t).
        eapply type_of_map with (g := g)...
        subst.
        assert (TREM := H); destruct H as (TS2 &TP2 &ISUN2).
        inversion TP; inversion TP2;  subst.
         assert (EX : exists q, pol_plus inp q p0).
        eapply pol_plus_of_pol_plus,pol_plus_comm...
        destruct EX as (q1 &EX).
        assert (nd_pf' : NoDup (domain ( ((b1, b2, vis, Chan lin q1 t)
     :: (y1, y2, vis, t)
        :: removeEntry (b1, b2)
        ((b1, b2, vis, Chan lin p0 t) :: removeEntry (b1, b2) (removeEntry (x1, x2) g)))))).
        rewrite removeEntry_shift.
        eapply no_dup_cons_removeEntry.
        assert (NIN: ~ In (y1, y2) ((b1, b2) :: domain (removeEntry (b1, b2) (removeEntry (x1, x2) g)))).
        intros ABS; inversion ABS. inversion H; subst;
                                     eapply in_g_in_domain in INb; contradiction.
        eapply in_domain_in_g in H as (ff &tt &ABS2);
          eapply in_removeEntry, in_removeEntry,in_g_in_domain in ABS2; contradiction.
        
        unfold domain; fold domain; eapply NoDup_cons,no_dup_cons_removeEntry...
        eauto.
        eapply no_dup_isMap in nd_pf' as pf'.
          
        eapply TInL with (u := (b1, b2)) (x := (y1, y2)) (p := p0) (t1 := Chan lin q1 t) (t := t) (pf1 := pf').
        econstructor.
        eauto.
        split. eauto.
        intros ABS; destruct ABS as (ff &tt &ABS); discriminate.
        eauto.
        intros ABS; eapply in_domain_in_g in ABS as (ff &tt &ABS); inversion ABS; try inversion H; subst;
          eapply in_g_in_domain in   INb; try contradiction.
        eapply in_removeEntry,in_removeEntry in H.
           eapply in_g_in_domain in  H; try contradiction.
           erewrite <-max_removeEntry_cons,max_removeEntry3... destruct MIN as [MIN1 | MIN2]...
           assert (b2 <= max (domain g)). eapply in_preserves_max... lia.
           eapply removeEntry_in in INb.
           eapply in_g_in_domain...
           eauto.
           
           (* typeCheck
    ((b1, b2, vis, Chan lin q1 t)
     :: (y1, y2, vis, t)
        :: removeEntry (b1, b2)
             ((b1, b2, vis, Chan lin p0 t) :: removeEntry (b1, b2) (removeEntry (x1, x2) g)))
    pf' (pmap q x1 x2 b1 b2) *)
           assert (nd_pf'': NoDup (domain (((b1, b2, vis, Chan lin q1 t)
          :: removeEntry (b1, b2)
               (removeEntry (x1, x2)
                  ((x1, x2, vis, Chan lin p4 t)
                     :: (y1, y2, vis, t) :: removeEntry (x1, x2) g)))))).
           eapply no_dup_cons_removeEntry, no_dup_removeEntry_no_dup.
           erewrite removeEntry_shift.
           eapply no_dup_cons_removeEntry.
           unfold domain; fold domain; eapply NoDup_cons...
           eauto.
           eapply no_dup_isMap in nd_pf'' as pf''.
           eapply IHTC with (pf1 := pf'') in IH; move IH at bottom.
           revert dependent pf''.
           revert dependent pf'.
           unfold removeEntry; fold removeEntry.
           assert (PEQ2 : pair_eq (x1, x2) (x1, x2) = true).
           eapply pairEq_eq...
           assert (PEQ3 : pair_eq (b1, b2) (b1, b2) = true).
           eapply pairEq_eq...
           rewrite PEQ2, PEQ3,<-removeEntry_shift.
           intros...
           eauto.
           erewrite removeEntry_shift,<-max_removeEntry_cons.
           simpl. simpl in H2. move H2 at bottom. erewrite <-Nat.ltb_lt in H2; erewrite H2...
           unfold domain; fold domain; eapply NoDup_cons...
           right...
           eauto.
           eauto.
           right; right; eapply removeEntry_in...
           econstructor...
           inversion H10; inversion EX; inversion H6; subst; try discriminate...
      +  simpl; unfold mv;
      unfold pair_eq in PEQ; rewrite PEQ;
        simpl.
         assert (TREM := H); move H at bottom; destruct H as (TS2 &TP2 &ISUN2).
         case_eq (pair_eq (u1, u2) (b1, b2)); intros PEQ2.
         * assert (EQ2 := PEQ2); rewrite <-pairEq_eq in EQ2; inversion EQ2; subst.
           assert (s1 = Chan lin p t).
           eapply type_of_map with (g := g)...
           subst.
           inversion TP;inversion TP2; subst; try discriminate...
           eapply type_remove_super with (s2 := Chan lin p0 t) in TREM as (t2 &EX).
           assert (nd_pf' : NoDup (domain (((b1, b2, vis, t2)
     :: (y1, y2, vis, t)
        :: removeEntry (b1, b2)
        ((b1, b2, vis, Chan lin p0 t) :: removeEntry (b1, b2) (removeEntry (x1, x2) g)))))).
           erewrite removeEntry_shift.
           eapply no_dup_cons_removeEntry.
           assert ((domain
       ((y1, y2, vis, t)
          :: (b1, b2, vis, Chan lin p0 t) :: removeEntry (b1, b2) (removeEntry (x1, x2) g))) =
                   (y1, y2) :: domain ((b1, b2, vis, Chan lin p0 t) :: removeEntry (b1, b2) (removeEntry (x1, x2) g))).
           simpl...
           rewrite H; clear H; 
             eapply NoDup_cons.
           intros ABS; inversion ABS; try inversion H; subst;
          eapply in_g_in_domain in   INb; try contradiction.
           eapply in_domain_in_g in H as (ff &tt &H);
             eapply in_removeEntry,in_removeEntry,in_g_in_domain in H;
             try contradiction.
           eapply no_dup_cons_removeEntry...
           eauto.
           eapply no_dup_isMap in nd_pf' as pf'.
           eapply TInL with (u := (b1, b2)) (x := (y1, y2))(pf1 := pf').
           eauto.
           eauto.
           intros ABS; unfold domain in ABS; fold domain in ABS; inversion ABS; try inversion H; subst;
             eapply in_g_in_domain in INb; try contradiction.
           eapply in_domain_in_g in H as (ff &tt &H);
             eapply in_removeEntry,in_removeEntry,in_g_in_domain in H; try contradiction.
           unfold snd; erewrite <-max_removeEntry_cons,max_removeEntry3...
           destruct MIN as [MIN1 | MIN2]...
           assert (b2 <= max (domain g)). eapply in_preserves_max... lia.
           eapply in_g_in_domain,removeEntry_in...
           (* typeCheck
    ((b1, b2, vis, t2)
     :: (y1, y2, vis, t)
        :: removeEntry (b1, b2)
             ((b1, b2, vis, Chan lin p0 t) :: removeEntry (b1, b2) (removeEntry (x1, x2) g)))
    pf' (pmap q x1 x2 b1 b2) *)
           assert (nd_pf'' : NoDup (domain (((b1, b2, vis, t2)
          :: removeEntry (b1, b2)
               (removeEntry (x1, x2)
                  ((b1, b2, vis, Chan lin p4 t)
                     :: (y1, y2, vis, t) :: removeEntry (b1, b2) g)))))).
           eapply no_dup_cons_removeEntry,no_dup_removeEntry_no_dup. erewrite removeEntry_shift.
           eapply no_dup_cons_removeEntry; simpl...
           eauto.
           eapply no_dup_isMap in nd_pf'' as pf''.
           eapply IHTC with (pf1 := pf'') (s1 := Chan lin p4 t)in IH;
             move IH at bottom.
           assert (PEQ3: pair_eq (b1, b2) (b1, b2) = true).
           eapply pairEq_eq...
           revert dependent pf'.
           simpl. rewrite PEQ3. intros.
           revert dependent pf''.
           rewrite removeEntry_swap;simpl. rewrite PEQ3,<-removeEntry_shift,removeEntry_swap.
           intros...
           eauto.
           eauto.
           eauto.
           erewrite max_same_domain with (l := domain ((y1, y2, vis, t) ::(b1, b2, vis, Chan lin p4 t) ::  removeEntry (b1, b2) g)).
           assert (EQ3: max (domain ((y1, y2, vis, t) :: (b1, b2, vis, Chan lin p4 t) :: removeEntry (b1, b2) g)) =
                        if y2 <? max (domain ((b1, b2, vis, Chan lin p4 t) :: removeEntry (b1, b2) g)) then max (domain ((b1, b2, vis, Chan lin p4 t) :: removeEntry (b1, b2) g)) else y2). simpl...
           rewrite EQ3, <-max_removeEntry_cons;clear EQ3.
           simpl in H2;
             rewrite  <-Nat.ltb_lt in H2; rewrite H2...
           eauto.
           eauto.
          unfold domain; fold domain; eapply cons_cons_iff...
          right; right; eapply removeEntry_in...
          assert (f = vis).
          eapply flag_of_map with (g := g)...
          subst...
          destruct EX as (TS3 &TP3 &ISUN3).
          inversion H11; inversion H7; inversion TP2; inversion TP3; subst; try inversion H18;try inversion H19; subst; try discriminate...
          eauto.
          eapply type_plus_comm...
         * assert (DIFF4 := PEQ2); rewrite <-pairEq_neq in DIFF4,EQ.
           assert (NIN:  ~ In (y1, y2) (domain ((b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g)))).
            intros ABS; unfold domain in ABS; fold domain in ABS; inversion ABS; try inversion H; subst;
             eapply in_g_in_domain in INb; try contradiction.
           eapply in_domain_in_g in H as (ff &tt &H);
             eapply in_removeEntry,in_removeEntry,in_g_in_domain in H; try contradiction.
           assert (nd_pf' : NoDup (domain (((u1, u2, vis, t1)
     :: (y1, y2, vis, t)
        :: removeEntry (u1, u2)
        ((b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g)))))).
           erewrite removeEntry_shift.
           eapply no_dup_cons_removeEntry.
           assert (EQ3: (domain
       ((y1, y2, vis, t)
          :: (b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g))) =
                        (y1, y2) :: domain ((b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g))). simpl...
           rewrite EQ3. eapply NoDup_cons,no_dup_cons_removeEntry,no_dup_removeEntry_no_dup...
           eauto.
           eapply no_dup_isMap in nd_pf' as pf'.
           eapply TInL with (u := (u1, u2)) (x := (y1, y2))(pf1 := pf').
           eauto.
           right; eapply removeEntry_in,removeEntry_in...
           eauto.
           unfold snd; erewrite <-max_removeEntry_cons,max_removeEntry3...
           destruct MIN as [MIN1 | MIN2]...
           assert (b2 <= max (domain g)). eapply in_preserves_max... lia.
            eapply in_g_in_domain,removeEntry_in...
            assert (nd_pf'' : NoDup (domain (((b1, b2, vis, s2)
          :: removeEntry (b1, b2)
               (removeEntry (x1, x2)
                            ((u1, u2, vis, t1) :: (y1, y2, vis, t) :: removeEntry (u1, u2) g))) ))).
            eapply no_dup_cons_removeEntry,
            no_dup_removeEntry_no_dup.
            erewrite removeEntry_shift.
            eapply no_dup_cons_removeEntry.
            simpl...
            eauto.
            eapply no_dup_isMap in nd_pf'' as pf''.
            eapply IHTC with (pf1 := pf'') in IH;
              move IH at bottom.
            revert dependent nd_pf'.
            revert dependent pf'.
            rewrite <-removeEntry_shift; intros.
            revert dependent nd_pf''.
            revert dependent pf''.
            rewrite <-removeEntry_shift,<-removeEntry_shift,<-removeEntry_shift,<-removeEntry_shift,removeEntry_swap with (a := (x1, x2)),removeEntry_swap; intros.
            eapply typeCheck_impl with (g1 := ((b1, b2, vis, s2)
                  :: (u1, u2, vis, t1)
                     :: (y1, y2, vis, t)
                        :: removeEntry (u1, u2)
                        (removeEntry (b1, b2) (removeEntry (x1, x2) g))))...
            
            eapply cons_cons_cons_iff...
            eauto.
            eauto.
            eauto.
             eauto.
            eauto.
            eauto.
            eauto.
            erewrite max_same_domain with (l := domain ((y1, y2, vis, t) ::(u1, u2, vis, t1) ::  removeEntry (u1, u2) g)).
            remember (max ((domain ((u1, u2, vis, t1) :: removeEntry (u1, u2) g)))) as m.
           assert (EQ3: max (domain ((y1, y2, vis, t) :: (u1, u2, vis, t1) :: removeEntry (u1, u2) g)) =
                        if y2 <? m  then m else y2). subst m; simpl...
           rewrite EQ3,Heqm, <-max_removeEntry_cons;clear EQ3.
           simpl in H2;
             rewrite  <-Nat.ltb_lt in H2; rewrite H2...
           eauto.
           eapply in_g_in_domain...
           unfold domain; fold domain; eapply cons_cons_iff...
           right; right; eapply removeEntry_in...
           right; right; eapply removeEntry_in...
           eauto.
           Unshelve. all:eauto.
    - Case TInUn.
      intros. 
      destruct x as [y1 y2];
         destruct u as [u1 u2]; unfold fst, snd.  
      assert (DIFF1 : (y1, y2) <> (b1, b2)).
      intros ABS; inversion ABS; subst;
        eapply in_g_in_domain in INb; contradiction.
      assert (DIFF2 : (y1, y2) <> (u1, u2)).
        intros ABS; inversion ABS; subst;
          eapply in_g_in_domain in H0; contradiction.
         assert (DIFF3: (y1, y2) <> (x1, x2)).
           intros ABS; inversion ABS; subst;
             eapply in_g_in_domain in INx; contradiction.
           assert (NIN: ~ In (y1, y2) (domain (removeEntry (u1, u2) g))).
           intros ABS.
           eapply in_domain_in_g in ABS as (ff &tt &ABS);
             eapply in_removeEntry,in_g_in_domain in ABS;
             try contradiction.
           assert (IH: x2 < max (domain ((y1, y2, vis, t) :: g)) \/ x2 < b2).
           simpl; simpl in H2;
             erewrite <-Nat.ltb_lt in H2; erewrite H2...
           
           assert (IH2 :  NoDup (domain ( (y1, y2, vis, t) :: removeEntry (u1, u2) g))).
           simpl. eapply NoDup_cons...
      case_eq (pair_eq (u1, u2) (x1, x2)); intros EQ; assert (PEQ :=EQ); try rewrite <-pairEq_eq in EQ; inversion EQ; subst. 
      + simpl; unfold mv;
      unfold pair_eq in PEQ; rewrite PEQ;
        simpl.
        assert (s = Chan un p t).
        eapply type_of_map with (g := g)...
        subst.
        inversion TP;   subst.
         assert (NIN2: ~ In (y1, y2) ((b1, b2) :: domain (removeEntry (b1, b2) (removeEntry (x1, x2) g)))).
        intros ABS; inversion ABS; try inversion H3; subst;
                                     eapply in_g_in_domain in INb; try contradiction.
        eapply in_domain_in_g in H3 as (ff &tt &ABS2);
          eapply in_removeEntry, in_removeEntry,in_g_in_domain in ABS2; contradiction.
        assert (nd_pf' : NoDup (domain (((y1, y2, vis, t)
    :: (b1, b2, vis, Chan un (pol_cup p1 p) t)
    :: removeEntry (b1, b2) (removeEntry (x1, x2) g))))).
        assert (EQ3: (domain
       ((y1, y2, vis, t)
        :: (b1, b2, vis, Chan un (pol_cup p1 p) t)
        :: removeEntry (b1, b2) (removeEntry (x1, x2) g))) =
                     (y1, y2) :: domain ((b1, b2, vis, Chan un (pol_cup p1 p) t)
                                           :: removeEntry (b1, b2) (removeEntry (x1, x2) g))).
        simpl...
        rewrite EQ3; eapply NoDup_cons,no_dup_cons_removeEntry...
        eapply no_dup_isMap in nd_pf' as pf'.
          
        eapply TInUn with (u := (b1, b2)) (p := pol_cup p1 p) (x := (y1, y2))  (pf1 := pf') (t := t).
        destruct H; subst. left;destruct p1...
        destruct p1...
        eauto.
        eauto.
        erewrite <-max_removeEntry_cons,max_removeEntry3...
        destruct MIN as [MIN1 | MIN2]...
        assert (b2 <= max (domain g)). eapply in_preserves_max... lia.
        eapply removeEntry_in in INb.
           eapply in_g_in_domain...
           eauto.
           
           (* typeCheck
    ((y1, y2, vis, t)
     :: (b1, b2, vis, Chan un (pol_cup p1 p) t)
        :: removeEntry (b1, b2) (removeEntry (x1, x2) g)) pf' (pmap q x1 x2 b1 b2) *)
           assert (nd_pf'': NoDup (domain (((b1, b2, vis, Chan un (pol_cup p1 p) t)
          :: removeEntry (b1, b2) (removeEntry (x1, x2) ((y1, y2, vis, t) :: g))) ))).
           eapply no_dup_cons_removeEntry, no_dup_removeEntry_no_dup. simpl...
           eapply no_dup_isMap in nd_pf'' as pf''.
           eapply IHTC with (pf1 := pf'') in IH; move IH at bottom.
           revert dependent nd_pf''.
           revert dependent pf''.
           rewrite <-removeEntry_shift,<-removeEntry_shift. intros.
           eapply typeCheck_impl with (pf1 := pf'')...
           eauto.
           eauto.
           simpl...
           right...
           right...
           econstructor...
      +  simpl; unfold mv;
      unfold pair_eq in PEQ; rewrite PEQ;
        simpl.
         case_eq (pair_eq (u1, u2) (b1, b2)); intros PEQ2.
         * assert (EQ2 := PEQ2); rewrite <-pairEq_eq in EQ2; inversion EQ2; subst.
           assert (s1 = Chan un p t).
           eapply type_of_map with (g := g)...
           subst.
           inversion TP; subst; try discriminate...
           assert (NIN2:
                      ~
  In (y1, y2)
    (domain
       ((b1, b2, vis, Chan un (pol_cup p p2) t)
          :: removeEntry (b1, b2) (removeEntry (x1, x2) g)))).
            intros ABS; simpl in ABS; destruct ABS as [ABS1 | ABS2]; try inversion ABS1; subst;
             try eapply in_domain_in_g in ABS1 as (ff &tt &ABS1);
             try eapply in_removeEntry,in_g_in_domain in ABS1;
             try contradiction.
            try eapply in_domain_in_g in ABS2 as (ff &tt &ABS2); eapply in_removeEntry,in_removeEntry,in_g_in_domain in ABS2; try contradiction.
            assert (nd_pf': NoDup (domain (((y1, y2, vis, t):: (b1, b2, vis, Chan un (pol_cup p p2) t)
                                                            :: removeEntry (b1, b2) (removeEntry (x1, x2) g))) )).
            assert (EQ3 : domain (((y1, y2, vis, t):: (b1, b2, vis, Chan un (pol_cup p p2) t)
                                                   :: removeEntry (b1, b2) (removeEntry (x1, x2) g))) =
                          (y1, y2) ::
                                   domain ((b1, b2, vis, Chan un (pol_cup p p2) t)
                                             :: removeEntry (b1, b2) (removeEntry (x1, x2) g))).
            simpl...
            rewrite EQ3. eapply NoDup_cons,no_dup_cons_removeEntry,no_dup_removeEntry_no_dup...
            eapply no_dup_isMap in nd_pf' as pf'.

            eapply TInUn with (u := (b1, b2)) (x := (y1, y2)) (p := (pol_cup p p2)) (pf1 := pf') .
           destruct H; subst; destruct p2...
           eauto.
           eauto.
           unfold snd; erewrite <-max_removeEntry_cons,max_removeEntry3...
           destruct MIN as [MIN1 | MIN2]...
           assert (b2 <= max (domain g)). eapply in_preserves_max... lia.
           eapply in_g_in_domain,removeEntry_in...
           (* typeCheck
    ((y1, y2, vis, t)
     :: (b1, b2, vis, Chan un (pol_cup p p2) t)
        :: removeEntry (b1, b2) (removeEntry (x1, x2) g)) pf' (pmap q x1 x2 b1 b2) *)
           assert (nd_pf'' : NoDup (domain (((b1, b2, vis, Chan un (pol_cup p p2) t)
          :: removeEntry (b1, b2) (removeEntry (x1, x2) ((y1, y2, vis, t) :: g)))))).
           eapply no_dup_cons_removeEntry,no_dup_removeEntry_no_dup. simpl... 
           eapply no_dup_isMap in nd_pf'' as pf''.
           eapply IHTC with (pf1 := pf'') in IH;
             move IH at bottom.
           revert dependent nd_pf''.
           revert dependent pf''.
           erewrite <-removeEntry_shift,<-removeEntry_shift. intros.
           eapply typeCheck_impl with (g1 := ((b1, b2, vis, Chan un (pol_cup p p2) t)
                                                :: (y1, y2, vis, t) :: removeEntry (b1, b2) (removeEntry (x1, x2) g)))...
           eauto.
           eauto.
           simpl...
           right...
           right...
           econstructor...
         * assert (DIFF4 := PEQ2); rewrite <-pairEq_neq in DIFF4,EQ.
           assert (NIN2:  ~ In (y1, y2) (domain ((b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g)))).
            intros ABS; unfold domain in ABS; fold domain in ABS; inversion ABS; try inversion H3; subst;
             eapply in_g_in_domain in INb; try contradiction.
           eapply in_domain_in_g in H3 as (ff &tt &H3);
             eapply in_removeEntry,in_removeEntry,in_g_in_domain in H3; try contradiction.
           assert (nd_pf' : NoDup (domain ( ((y1, y2, vis, t) :: (b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g))))).
           assert (EQ3: (domain
       ((y1, y2, vis, t)
          :: (b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g))) =
                        (y1, y2) :: domain ((b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g))). simpl...
           rewrite EQ3. eapply NoDup_cons,no_dup_cons_removeEntry,no_dup_removeEntry_no_dup...
           eauto.
           eapply no_dup_isMap in nd_pf' as pf'.
           eapply TInUn with (u := (u1, u2)) (x := (y1, y2)) (pf1 := pf').
           eauto.
           right; eapply removeEntry_in,removeEntry_in...
           eauto.
           unfold snd; erewrite <-max_removeEntry_cons,max_removeEntry3...
           destruct MIN as [MIN1 | MIN2]...
           assert (b2 <= max (domain g)). eapply in_preserves_max... lia.
            eapply in_g_in_domain,removeEntry_in...
            assert (nd_pf'' : NoDup (domain (((b1, b2, vis, s2)
          :: removeEntry (b1, b2)
               (removeEntry (x1, x2)
                            ( (y1, y2, vis, t) :: g))) ))).
            eapply no_dup_cons_removeEntry,
            no_dup_removeEntry_no_dup.
            simpl...
            eapply no_dup_isMap in nd_pf'' as pf''.
            eapply IHTC with (pf1 := pf'') in IH;
              move IH at bottom.
            revert dependent nd_pf''.
            revert dependent pf''.
            rewrite <-removeEntry_shift,<-removeEntry_shift. intros.
            eapply typeCheck_impl with (g1 := ((b1, b2, vis, s2)
                                                 :: (y1, y2, vis, t) :: removeEntry (b1, b2) (removeEntry (x1, x2) g)))...
            eauto.
            eauto.
            simpl...
            right...
            right...
            eauto. 
    - Case TInU.
      intros.
      
      assert (CONS_T: is_unrestricted s2 \/ (exists t,
                  s2 = Chan lin empty t) \/ s2 = Top).
      destruct s1; try destruct m; inversion TP; subst; try discriminate...
      destruct f; try contradiction.
      assert (INIP: In (b1, b2, ill, Chan lin p0 s1) (ill_proj g)).  eapply in_ill_proj...
       assert (INVP: In (x1, x2, vis, Chan lin p2 s1) (vis_proj g)). eapply in_vis_proj...
      assert (p0 = empty).
      eapply cons_lin with (g := (vis_proj g ++ ill_proj g)). eauto. eapply in_app_iff; right...
      assert (p2 = empty).
       eapply cons_lin with (g := (vis_proj g ++ ill_proj g)). eauto. eapply in_app_iff; left...
       assert (p3 = empty).
       subst; inversion H8; subst; try discriminate...
       subst. right; left;exists s1...
       assert (INVP: In (b1, b2, vis, Chan lin p0 s1) (vis_proj g)). eapply in_vis_proj...
       assert (INVP2: In (x1, x2, vis, Chan lin p2 s1) (vis_proj g)). eapply in_vis_proj...
      assert (p0 = empty).
      eapply cons_lin with (g := (vis_proj g ++ ill_proj g)). eauto. eapply in_app_iff; left...
      assert (p2 = empty).
       eapply cons_lin with (g := (vis_proj g ++ ill_proj g)). eauto. eapply in_app_iff; left...
       assert (p3 = empty).
       subst; inversion H8; subst; try discriminate...
       subst. right; left; exists s1...

       left; eapply un_is_unrestricted...
       
       
      destruct x as [y1 y2];
         destruct u as [u1 u2]; unfold fst, snd.  
      assert (DIFF1 : (y1, y2) <> (b1, b2)).
      intros ABS; inversion ABS; subst;
        eapply in_g_in_domain in INb; contradiction.
      assert (DIFF2 : (y1, y2) <> (u1, u2)).
        intros ABS; inversion ABS; subst;
          eapply in_g_in_domain in H0; contradiction.
         assert (DIFF3: (y1, y2) <> (x1, x2)).
           intros ABS; inversion ABS; subst;
             eapply in_g_in_domain in INx; contradiction.
           assert (NIN: ~ In (y1, y2) (domain (removeEntry (u1, u2) g))).
           intros ABS.
           eapply in_domain_in_g in ABS as (ff &tt &ABS);
             eapply in_removeEntry,in_g_in_domain in ABS;
             try contradiction.
           assert (IH: x2 < max (domain ((y1, y2, vis, t) :: g)) \/ x2 < b2).
           simpl; simpl in H2;
             erewrite <-Nat.ltb_lt in H2; erewrite H2...
           
           assert (IH2 :  NoDup (domain ( (y1, y2, vis, t) :: removeEntry (u1, u2) g))).
           simpl. eapply NoDup_cons...
      case_eq (pair_eq (u1, u2) (x1, x2)); intros EQ; assert (PEQ :=EQ); try rewrite <-pairEq_eq in EQ; inversion EQ; subst. 
      + simpl; unfold mv;
      unfold pair_eq in PEQ; rewrite PEQ;
        simpl.
        assert (s = Chan un p t).
        eapply type_of_map with (g := g)...
        subst.
        inversion TP;   subst.
         assert (NIN2: ~ In (y1, y2) ((b1, b2) :: domain (removeEntry (b1, b2) (removeEntry (x1, x2) g)))).
        intros ABS; inversion ABS; try inversion H4; subst;
                                     eapply in_g_in_domain in INb; try contradiction.
        eapply in_domain_in_g in H4 as (ff &tt &ABS2);
          eapply in_removeEntry, in_removeEntry,in_g_in_domain in ABS2; contradiction.
        assert (nd_pf' : NoDup (domain (((y1, y2, vis, t)
    :: (b1, b2, vis, Chan un (pol_cup p1 p) t)
    :: removeEntry (b1, b2) (removeEntry (x1, x2) g))))).
        assert (EQ3: (domain
       ((y1, y2, vis, t)
        :: (b1, b2, vis, Chan un (pol_cup p1 p) t)
        :: removeEntry (b1, b2) (removeEntry (x1, x2) g))) =
                     (y1, y2) :: domain ((b1, b2, vis, Chan un (pol_cup p1 p) t)
                                           :: removeEntry (b1, b2) (removeEntry (x1, x2) g))).
        simpl...
        rewrite EQ3; eapply NoDup_cons,no_dup_cons_removeEntry...
        eapply no_dup_isMap in nd_pf' as pf'.
          
        eapply TInU with (u := (b1, b2)) (p := pol_cup p1 p) (x := (y1, y2))  (pf1 := pf') (t := t).
        destruct H; subst. left;destruct p1...
        destruct p1...
        eauto.
        eauto.
        erewrite <-max_removeEntry_cons,max_removeEntry3...
        destruct MIN as [MIN1 | MIN2]...
        assert (b2 <= max (domain g)). eapply in_preserves_max... lia.
        eapply removeEntry_in in INb.
        eapply in_g_in_domain...
        eauto.
        (* cons
    (vis_proj
       ((b1, b2, vis, Chan un (pol_cup p1 p) t)
        :: removeEntry (b1, b2) (removeEntry (x1, x2) g)) ++
     ill_proj
       ((b1, b2, vis, Chan un (pol_cup p1 p) t)
        :: removeEntry (b1, b2) (removeEntry (x1, x2) g))) ?pf2 *)
        assert (nd_pfvp: NoDup (domain ((vis_proj (removeEntry (x1, x2) g))))).
        eapply no_dup_vis_proj, no_dup_removeEntry_no_dup...
        eapply no_dup_isMap in nd_pfvp as pfvp.
         assert (nd_pfip: NoDup (domain ((ill_proj (removeEntry (x1, x2) g))))).
        eapply no_dup_ill_proj, no_dup_removeEntry_no_dup...
        eapply no_dup_isMap in nd_pfip as pfip.
        erewrite cons_distr in *. split.
        eapply gcons_vis_proj_add.
        eapply no_dup_removeEntry_no_dup...
        instantiate (1 := pfvp).
        revert dependent pfvp. arewrite vis_proj_removeEntry.
        intros.
        eapply gcons_removeEntry. destruct H3...
        eapply gcons_ill_proj_add.
        eapply no_dup_removeEntry_no_dup...
        instantiate (1 := pfip).
        revert dependent pfip. rewrite ill_proj_removeEntry.
        intros.
        eapply gcons_removeEntry. destruct H3...
        assumption.
       
        
           (* typeCheck
    ((y1, y2, vis, t)
     :: (b1, b2, vis, Chan un (pol_cup p1 p) t)
        :: removeEntry (b1, b2) (removeEntry (x1, x2) g)) pf' (pmap q x1 x2 b1 b2) *)
           assert (nd_pf'': NoDup (domain (((b1, b2, vis, Chan un (pol_cup p1 p) t)
          :: removeEntry (b1, b2) (removeEntry (x1, x2) ((y1, y2, vis, t) :: g))) ))).
           eapply no_dup_cons_removeEntry, no_dup_removeEntry_no_dup. simpl...
           eapply no_dup_isMap in nd_pf'' as pf''.
           eapply IHTC with (pf1 := pf'') in IH; move IH at bottom.
           revert dependent nd_pf''.
           revert dependent pf''.
           rewrite <-removeEntry_shift,<-removeEntry_shift. intros...
           eapply typeCheck_impl with (pf1 := pf'')...
           eauto.
           eauto.
           simpl...
           right...
           right...
           econstructor...
      +  simpl; unfold mv;
      unfold pair_eq in PEQ; rewrite PEQ;
        simpl.
         case_eq (pair_eq (u1, u2) (b1, b2)); intros PEQ2.
         * assert (EQ2 := PEQ2); rewrite <-pairEq_eq in EQ2; inversion EQ2; subst.
           assert (s1 = Chan un p t).
           eapply type_of_map with (g := g)...
           subst.
           inversion TP; subst; try discriminate...
           assert (NIN2:
                      ~
  In (y1, y2)
    (domain
       ((b1, b2, vis, Chan un (pol_cup p p2) t)
          :: removeEntry (b1, b2) (removeEntry (x1, x2) g)))).
            intros ABS; simpl in ABS; destruct ABS as [ABS1 | ABS2]; try inversion ABS1; subst;
             try eapply in_domain_in_g in ABS1 as (ff &tt &ABS1);
             try eapply in_removeEntry,in_g_in_domain in ABS1;
             try contradiction.
            try eapply in_domain_in_g in ABS2 as (ff &tt &ABS2); eapply in_removeEntry,in_removeEntry,in_g_in_domain in ABS2; try contradiction.
            assert (nd_pf': NoDup (domain (((y1, y2, vis, t):: (b1, b2, vis, Chan un (pol_cup p p2) t)
                                                            :: removeEntry (b1, b2) (removeEntry (x1, x2) g))) )).
            assert (EQ3 : domain (((y1, y2, vis, t):: (b1, b2, vis, Chan un (pol_cup p p2) t)
                                                   :: removeEntry (b1, b2) (removeEntry (x1, x2) g))) =
                          (y1, y2) ::
                                   domain ((b1, b2, vis, Chan un (pol_cup p p2) t)
                                             :: removeEntry (b1, b2) (removeEntry (x1, x2) g))).
            simpl...
            rewrite EQ3. eapply NoDup_cons,no_dup_cons_removeEntry,no_dup_removeEntry_no_dup...
            eapply no_dup_isMap in nd_pf' as pf'.

            eapply TInU with (u := (b1, b2)) (x := (y1, y2)) (p := (pol_cup p p2)) (pf1 := pf') .
           destruct H; subst; destruct p2...
           eauto.
           eauto.
           unfold snd; erewrite <-max_removeEntry_cons,max_removeEntry3...
           destruct MIN as [MIN1 | MIN2]...
           assert (b2 <= max (domain g)). eapply in_preserves_max... lia.
           eapply in_g_in_domain,removeEntry_in...
           (* cons
    (vis_proj
       ((b1, b2, vis, Chan un (pol_cup p p2) t)
        :: removeEntry (b1, b2) (removeEntry (x1, x2) g)) ++
     ill_proj
       ((b1, b2, vis, Chan un (pol_cup p p2) t)
        :: removeEntry (b1, b2) (removeEntry (x1, x2) g))) ?pf20 *)
           assert (nd_pfvp: NoDup (domain ((vis_proj (removeEntry (x1, x2) g))))).
        eapply no_dup_vis_proj, no_dup_removeEntry_no_dup...
        eapply no_dup_isMap in nd_pfvp as pfvp.
         assert (nd_pfip: NoDup (domain ((ill_proj (removeEntry (x1, x2) g))))).
        eapply no_dup_ill_proj, no_dup_removeEntry_no_dup...
        eapply no_dup_isMap in nd_pfip as pfip.
        erewrite cons_distr in *. split.
        eapply gcons_vis_proj_add.
        eapply no_dup_removeEntry_no_dup...
        instantiate (1 := pfvp).
        revert dependent pfvp. arewrite vis_proj_removeEntry.
        intros.
        eapply gcons_removeEntry. destruct H3...
        eapply gcons_ill_proj_add.
        eapply no_dup_removeEntry_no_dup...
        instantiate (1 := pfip).
        revert dependent pfip. rewrite ill_proj_removeEntry.
        intros.
        eapply gcons_removeEntry. destruct H3...
        assumption.
           
           (* typeCheck
    ((y1, y2, vis, t)
     :: (b1, b2, vis, Chan un (pol_cup p p2) t)
        :: removeEntry (b1, b2) (removeEntry (x1, x2) g)) pf' (pmap q x1 x2 b1 b2) *)
           assert (nd_pf'' : NoDup (domain (((b1, b2, vis, Chan un (pol_cup p p2) t)
          :: removeEntry (b1, b2) (removeEntry (x1, x2) ((y1, y2, vis, t) :: g)))))).
           eapply no_dup_cons_removeEntry,no_dup_removeEntry_no_dup. simpl... 
           eapply no_dup_isMap in nd_pf'' as pf''.
           eapply IHTC with (pf1 := pf'') in IH;
             move IH at bottom.
           revert dependent nd_pf''.
           revert dependent pf''.
           erewrite <-removeEntry_shift,<-removeEntry_shift. intros. 
           eapply typeCheck_impl with (g1 := ((b1, b2, vis, Chan un (pol_cup p p2) t)
                                                :: (y1, y2, vis, t) :: removeEntry (b1, b2) (removeEntry (x1, x2) g)))...
           eauto.
           eauto.
           simpl...
           right...
           right...
           econstructor...
         * assert (DIFF4 := PEQ2); rewrite <-pairEq_neq in DIFF4,EQ.
           assert (NIN2:  ~ In (y1, y2) (domain ((b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g)))).
            intros ABS; unfold domain in ABS; fold domain in ABS; inversion ABS; try inversion H4; subst;
             eapply in_g_in_domain in INb; try contradiction.
           eapply in_domain_in_g in H4 as (ff &tt &H4);
             eapply in_removeEntry,in_removeEntry,in_g_in_domain in H4; try contradiction.
           assert (nd_pf' : NoDup (domain ( ((y1, y2, vis, t) :: (b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g))))).
           assert (EQ3: (domain
       ((y1, y2, vis, t)
          :: (b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g))) =
                        (y1, y2) :: domain ((b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g))). simpl...
           rewrite EQ3. eapply NoDup_cons,no_dup_cons_removeEntry,no_dup_removeEntry_no_dup...
           eauto.
           eapply no_dup_isMap in nd_pf' as pf'.
           eapply TInU with (u := (u1, u2)) (x := (y1, y2)) (pf1 := pf').
           eauto.
           right; eapply removeEntry_in,removeEntry_in...
           eauto.
           unfold snd; erewrite <-max_removeEntry_cons,max_removeEntry3...
           destruct MIN as [MIN1 | MIN2]...
           assert (b2 <= max (domain g)). eapply in_preserves_max... lia.
            eapply in_g_in_domain,removeEntry_in...

            (*  cons
    (vis_proj ((b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g)) ++
     ill_proj ((b1, b2, vis, s2) :: removeEntry (b1, b2) (removeEntry (x1, x2) g))) 
    ?pf21  *)
        assert (nd_pfvp: NoDup (domain ((vis_proj (removeEntry (x1, x2) g))))).
        eapply no_dup_vis_proj, no_dup_removeEntry_no_dup...
        eapply no_dup_isMap in nd_pfvp as pfvp.
         assert (nd_pfip: NoDup (domain ((ill_proj (removeEntry (x1, x2) g))))).
        eapply no_dup_ill_proj, no_dup_removeEntry_no_dup...
        eapply no_dup_isMap in nd_pfip as pfip.
        erewrite cons_distr in *. 
        move CONS_T at bottom;
          destruct CONS_T as [ISUN | [EMPTY | TOP]].
        destruct ISUN as (tt &pp &ISUN); subst.
        split.
        eapply gcons_vis_proj_add.
        eapply no_dup_removeEntry_no_dup...
        instantiate (1 := pfvp).
        revert dependent pfvp. arewrite vis_proj_removeEntry.
        intros.
        eapply gcons_removeEntry. destruct H3...
        eapply gcons_ill_proj_add.
        eapply no_dup_removeEntry_no_dup...
        instantiate (1 := pfip).
        revert dependent pfip. arewrite ill_proj_removeEntry.
        intros.
        eapply gcons_removeEntry. destruct H3...

        destruct EMPTY as (tt &EMPTY); subst.
        split.
        eapply gcons_vis_proj_addL.
        eapply no_dup_removeEntry_no_dup...
         instantiate (1 := pfvp).
        revert dependent pfvp. arewrite vis_proj_removeEntry.
        intros.
        eapply gcons_removeEntry. destruct H3...
        eapply gcons_ill_proj_addL.
        eapply no_dup_removeEntry_no_dup...
        instantiate (1 := pfip).
        revert dependent pfip. arewrite ill_proj_removeEntry.
        intros.
        eapply gcons_removeEntry. destruct H3...
        
        
        subst.
        split.
        eapply gcons_vis_proj_addT.
        eapply no_dup_removeEntry_no_dup...
        instantiate (1 := pfvp).
        revert dependent pfvp. arewrite vis_proj_removeEntry.
        intros.
        eapply gcons_removeEntry. destruct H3...
        eapply gcons_ill_proj_addT.
        eapply no_dup_removeEntry_no_dup...
        instantiate (1 := pfip).
        revert dependent pfip. arewrite ill_proj_removeEntry.
        intros.
        eapply gcons_removeEntry. destruct H3...
            
            assert (nd_pf'' : NoDup (domain (((b1, b2, vis, s2)
          :: removeEntry (b1, b2)
               (removeEntry (x1, x2)
                            ( (y1, y2, vis, t) :: g))) ))).
            eapply no_dup_cons_removeEntry,
            no_dup_removeEntry_no_dup.
            simpl...
            eapply no_dup_isMap in nd_pf'' as pf''.
            eapply IHTC with (pf1 := pf'') in IH;
              move IH at bottom.
            revert dependent nd_pf''.
            revert dependent pf''.
            rewrite <-removeEntry_shift,<-removeEntry_shift. intros.
            eapply typeCheck_impl with (g1 := ((b1, b2, vis, s2)
                                                 :: (y1, y2, vis, t) :: removeEntry (b1, b2) (removeEntry (x1, x2) g)))...
            eauto.
            eauto.
            simpl...
            right...
            right...
            eauto. 
            Unshelve.
            all: try solve [ eapply no_dup_isMap;
                               unfold ill_proj; fold ill_proj;
                               eapply no_dup_vis_ill_proj; eauto ].
            all: eauto.
  Qed.
  
