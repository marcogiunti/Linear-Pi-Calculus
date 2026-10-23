Require Import
  Bool List Lia PeanoNat Program.Equality
  ListAddOns Max RemoveEntry Domain Classical
  Permutation
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
  split_operations_3
  type_system_rules
  disjoint_newEntries
  type_checking_1
  proposition27
  tc_premises_4
  lts_iff
  split_exists_neutral.

Require Import CpdtTactics LibTactics.
Import ListNotations.

#[global] Hint Resolve split_cons remove_exists split_sub
  Fp_hi Fp_ih Fp_vv Fp_ii un_is_unrestricted
  type_remove_top type_remove_top_2
  lts_type_remove_lin_out lts_type_remove_un_out
  no_dup_split_no_dup_l.

Lemma split_lts_exists_lts :
  forall g1 g2 g p a g' p' pf1 pf2 pf nd_pf nd_pf1,
    tEnv_split g1 g2 g pf1 pf2 pf ->
    typeCheck g1 pf1 p ->
    lts g p a g' p' nd_pf ->
    sl_pos p ->
    exists k1,
      lts g1 p a k1 p' nd_pf1.
Proof with eauto using typeCheck_no_dup,sl_pos_par_l,sl_pos_par_r.
  intros g1 g2 g p a g' p' pf1 pf2 pf nd_pf nd_pf1 TSPLIT TCHECK LTS SLP.
  generalize dependent g1.
  generalize dependent g2.
  dependent induction LTS.
  remember pf0 as nd_pf. subst pf0.

  - Case parL. 
    intros.

    
    inverts TCHECK as TS1 TC1 TC2.
    assert (WFTC1 := TC1).
    
    specialize IHLTS with (g1 := g0) (pf1 := pf0).
    apply split_of_split with
      g0 g3 g1 g2 g pf0 pf3 pf1 pf2 pf in TS1 as TSPLIT2.
    destruct TSPLIT2 as [w2 TSPLIT2]. 
    destruct TSPLIT2 as [pfw2 TSPLIT2].
    assert (nd_pf0 : NoDup (domain g0)).
    apply no_dup_split_no_dup_l with
      g0 g3 g1 pf0 pf3 pf1
      in nd_pf1...
    specialize IHLTS with
      (g2 := w2) (pf2 := pfw2) (pf := pf) (nd_pf1 := nd_pf0)
    .
    apply IHLTS in TSPLIT2.
    clear IHLTS.
    destruct TSPLIT2 as [k0 LTS2].
    + assert (exists k1,
                 lts g1 p1 a k1 p2 nd_pf1).

      apply Peirce. intros ABSURD.
      specialize  split_not_exists_lts
        with (g:= g1) as SNEA.
      specialize SNEA with
        (g1 :=g0) (g2:=g3) (k1 := k0).
      specialize SNEA with p1 a p2 pf0  pf3 pf1 nd_pf0 nd_pf1.

      assert (TC' := TC1);
        try eapply typeCheck_no_dup in TC1 as [INCL ND];
        try eapply typeCheck_hid_proj in TC';
        try eapply no_dup_split_no_dup_l;
        try eapply incl_preserves_max in INCL...
      (*eapply split_incl_hid_proj in TS1...*)

      assert (WF : wf p1).
      split...
      eapply tc_dep_relabel_premises.fn_disjoint_sl
        with (g := g0)...
      
      apply SNEA in TS1 as ABSURD2; try eassumption.
      clear SNEA.
      
      destruct ABSURD2 as [x1 [x2 [y1 [y2 [t  ABSURD2]]]]].
      destruct ABSURD2 as [AIN | ABSURD2].
      destruct AIN as [pa [TA0 TA1]]; subst.
      inversion TA1; subst.
      apply tsub_io with
        g1 g2 g pf1 pf2 pf x1 x2 f lin t
        in H.
      apply type_of_in_action with
        g p1 x1 x2 y1 y2 p2 g' nd_pf
        in LTS.
      destruct LTS as [t0 [Ta | [Ta | Ta]]].
      assert (G := pf).
      apply type_of_map with
        g (x1, x2) (Chan lin inp t0) (Chan lin io t)
        in G. inversion G.
      eauto.
      eauto.
      assert (G := pf).
      apply type_of_map with
        g (x1, x2) (Chan un inp t0) (Chan lin io t)
        in G. inversion G.
      eauto.
      eauto.
      assert (G := pf).
      apply type_of_map with
        g (x1, x2) (Chan un io t0) (Chan lin io t)
        in G. inversion G.
      eauto.
      eauto.
      eauto.
      
      destruct ABSURD2 as [ANPLUS | ABSURD2].
      destruct ANPLUS as [aeq ANPLUS].
      destruct ANPLUS as [m2 [q2 [ty [TYPx [TYP1y ABSURD2]]]]]; subst.
      inversion TYPx. subst.
      apply tsub_payload with
        (pf1 := pf0) (pf2 := pf3) (pf := pf1) in H as K.
      destruct K as [q1 TYP1x]. 
      apply split_lts_exists_remove_l with
        g1 g2 g pf1 pf2 pf p1 g' p2 nd_pf
        x1 x2 y1 y2 m2 q1 t in TYP1x.
      destruct TYP1x as [ty' [t' [TYP1y' TPLUS]]].
      all:try eassumption.
      apply type_of_map with
        g1 (y1, y2) ty ty'
        in pf1 as TEQ; subst...
      elim ABSURD2; exists t'.
      all:try eassumption.

      destruct ABSURD2 as [AHID | ABSURD2].
      destruct AHID as [AIN [ AILL AHID]].
      inversion AHID; subst...
      apply fsub_hid with
        g1 g2 g pf1 pf2 pf y1 y2 t0
        in H as AHID2.
      apply lts_inp_obj_not_hid with
        g p1 x1 x2 y1 y2 g' p2 nd_pf
        in LTS as NHID...
      contradiction.
      eauto.
      
      destruct ABSURD2 as [AOUT ABSURD2].
      destruct ABSURD2 as [TA0 TA1].
      inversion TA1; subst.
      apply tsub_io with
        g1 g2 g pf1 pf2 pf x1 x2 f lin t
        in H.
      apply type_of_out_action with
        g p1 x1 x2 y1 y2 p2 g' nd_pf
        in LTS.
      destruct LTS as [t0 [Ta | [Ta | Ta]]].
      assert (G := pf).
      apply type_of_map with
        g (x1, x2) (Chan lin out t0) (Chan lin io t)
        in G. inversion G.
      all:try eassumption.
      assert (G := pf).
      apply type_of_map with
        g (x1, x2) (Chan un out t0) (Chan lin io t)
        in G. inversion G.
      all:try eassumption.
      assert (G := pf).
      apply type_of_map with
        g (x1, x2) (Chan un io t0) (Chan lin io t)
        in G. inversion G.
      all:try eassumption.
      eapply no_dup_split_no_dup_r...
      eapply sl_pos_par_l...
      
      destruct H as [k1 LTS3].
      exists k1.
      eapply parL in LTS3...
    + eauto. 
    + eauto.
    + eauto.
    + assumption.
  - Case lOut. 
    intros.
    inversion TCHECK; subst.
    destruct u as [a1 a2].
    destruct v as [b1 b2]. unfold fst. unfold snd.
    unfold fst in H0; unfold snd in H0.
    inversion H7. subst.
    inversion H2; subst.
    
    apply tsuper_payload with
      (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as K0.
    destruct K0 as [pol TYP1]. inversion TYP1; subst.
    assert (vis = f /\ Chan lin out t0 =  Chan lin pol t).
    apply in_isMap with (x := (a1, a2)) (g := g1)...
    destruct H5. inversion H6; subst.
    exists (
        ((a1, a2), vis, Chan lin empty t)
          :: ((b1, b2), vis, t4)
          ::  removeEntry (a1, a2) (removeEntry (b1, b2) g1)).
    apply lOut with (t1 := t').
    eauto.
    eauto.
    eauto.
    eauto.

    apply tsuper_payload with
      (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as K0.
    destruct K0 as [pol TYP1]. inversion TYP1; subst.
    assert (vis = f /\ Chan lin io t0 =  Chan lin pol t).
    apply in_isMap with (x := (a1, a2)) (g := g1)...
    destruct H5. inversion H6; subst.
    apply tsub_io with
      (pf1 := pf1) (pf2 := pf2) (pf := pf) in H4.
    inversion H4. subst...
    assert (vis = f /\ Chan lin out t =  Chan lin io t).
    apply in_isMap with (x := (a1, a2)) (g := g)...
    inversion H12. inversion H14...
    all:try eassumption.
    
    eapply tsuper_payload with (pf1 := pf1) in H0.
    destruct H0 as [pp1 TYP1]. inversion TYP1.
    assert (vis = f /\  Chan un p0 t0 = Chan lin pp1 t).
    destruct u. simpl in H0.
    eapply in_isMap... destruct H5. inversion H6.
    eauto.
  - Case uOut. 
    intros.
    inversion TCHECK; subst.

    eapply tsuper_payload with (pf1 := pf1) in H1.
    destruct H1 as [pp1 TYP1]. inversion TYP1.
    assert (vis = f /\  Chan lin p0 t0 = Chan un pp1 t).
    destruct u. simpl in H1.
    eapply in_isMap... destruct H6. inversion H7.
    eauto.

    destruct u as [a1 a2].
    destruct v as [b1 b2]. simpl.

    exists (
        ((b1, b2), vis, t3)
          ::  (removeEntry (b1, b2) g1)).
    eapply uOut.
    instantiate (1 := p0). intuition.
    instantiate (1 := t0). instantiate (1 := t'). assumption.
    eauto. eauto.
  -  Case lIn. 
     intros.

     specialize split_lts_exists_remove_l with
       g1 g2 g pf1 pf2 pf (dInp a1 a2 x1 x2 p)
       ((a1, a2, vis, Chan lin empty t)
          :: (b1, b2, vis, t2) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)) (pmap p x1 x2 b1 b2) pf0 
       a1 a2 b1 b2 lin inp t as EXPLUS.
     inversion TCHECK; subst.
     inversion H8.
     inversion H3; subst.
     destruct u as [a1 a2]. simpl in H1.
     apply tsuper_payload with
       (pf1 := pf1) (pf2 := pf2) (pf := pf) in H1 as K0.
     destruct K0 as [pol2 TYP1]. inversion TYP1; subst.
     assert (vis = f0 /\ Chan lin inp t0 =  Chan lin pol2 t).
     apply in_isMap with (x := (a1, a2)) (g := g1)...
     inversion H6. inversion H13; subst.
     simpl in EXPLUS.
     assert (TPLUS: typeOf g1 (a1, a2) (Chan lin inp t))...
     apply EXPLUS in TPLUS.
     all:try eassumption.
     destruct TPLUS as [ty [t' [TYPx1 TPLUS]]].
     simpl.
     exists ( (((a1, a2), vis, Chan lin empty t)
                 :: ((b1, b2), vis, t')
                 :: (removeEntry (a1, a2) (removeEntry (b1, b2) g1)))).
     inversion TYPx1; subst. 
     apply lIn with (f := f0) (t1 := ty).
     apply type_plus_comm...
     assert (f = f0).
     apply fsuper_flag with 
       (pf1 := pf1) (pf2 := pf2) (pf := pf)
       (a := (b1, b2)) (t := t1) (t1 := ty)...
     subst...
     eauto. 
     eauto.
     eauto.

     destruct u as [a1 a2]. simpl in H1.
     apply tsuper_payload with
       (pf1 := pf1) (pf2 := pf2) (pf := pf) in H1 as K0.
     destruct K0 as [pol2 TYP1]. inversion TYP1; subst.
     assert (vis = f0 /\ Chan lin io t0 =  Chan lin pol2 t).
     apply in_isMap with (x := (a1, a2)) (g := g1)...
     inversion H6. inversion H13; subst.
     apply tsub_io with
       (pf1 := pf1) (pf2 := pf2) (pf := pf) in H5.
     inversion H5. subst.
     assert (vis = f0 /\ Chan lin inp t =  Chan lin io t).
     apply in_isMap with (x := (a1, a2)) (g := g)...
     inversion H14. inversion H16.
     all:try eassumption.

     eapply tsuper_payload with (pf1 := pf1) in H1.
     destruct H1 as [pp1 TYP1]. inversion TYP1.
     assert (vis = f0 /\  Chan un p0 t0 = Chan lin pp1 t).
     destruct u. simpl in H1.
     eapply in_isMap... destruct H6. inversion H7.
     eauto.
     
  - Case uIn.
    intros.
    inversion TCHECK; subst.

    eapply tsuper_payload with (pf1 := pf1) in H2.
    destruct H2 as [pp1 TYP1]. inversion TYP1.
    assert (vis = f0 /\  Chan lin p0 t0 = Chan un pp1 t).
    destruct u. simpl in H2.
    eapply in_isMap... destruct H7. inversion H8.
    eauto.

    
    destruct u as [a1 a2]. simpl in H2.
    apply tsuper_payload with
      (pf1 := pf1) (pf2 := pf2) (pf := pf) in H2 as K0.
    destruct K0 as [pol2 TYP1]. inversion TYP1; subst.
    destruct x as [x1 x2].
    specialize split_lts_exists_remove_l with
      g1 g2 g pf1 pf2 pf (dInp a1 a2 x1 x2 p)
      ((b1, b2, vis, t2) :: removeEntry (b1, b2) g)
      (pmap p x1 x2 b1 b2) pf0 
      a1 a2 b1 b2 un pol2 t as EXPLUS.
    assert (vis = f0 /\ Chan un p0 t0 = Chan un pol2 t).
    apply in_isMap with (x := (a1, a2)) (g := g1)...
    inversion H5. inversion H7; subst.
    simpl in EXPLUS.
    assert (TPLUS: typeOf g1 (a1, a2) (Chan un pol2 t))...
    apply EXPLUS in TPLUS.
    all:try eassumption.
    destruct TPLUS as [ty [t' [TYPx1 TPLUS]]].
    simpl.
    exists ( (( ((b1, b2), vis, t')
                  :: removeEntry (b1, b2) g1))).
    inversion TYPx1; subst. 
    apply uIn with (f := f0) (t1 := ty) (pol := pol2) (t := t).
    intuition.
    apply type_plus_comm...
    assert (f = f0).
    apply fsuper_flag with 
      (pf1 := pf1) (pf2 := pf2) (pf := pf)
      (a := (b1, b2)) (t := t1) (t1 := ty)...
    subst...
    eauto. 
    eauto.
    eauto.
  - Case uRin.
    intros.

    
    inversion TCHECK; subst.

    destruct u as [a1 a2]. simpl in H2.
    apply tsuper_payload with
      (pf1 := pf1) (pf2 := pf2) (pf := pf) in H2 as K0.
    destruct K0 as [pol2 TYP1]. inversion TYP1; subst.
    destruct x as [x1 x2].
    remember (dep_relabel p (domain g) pf0) as q1.  
    specialize split_lts_exists_remove_l with
      g1 g2 g pf1 pf2 pf (dBang a1 a2 x1 x2 p)
      ((newEntries g (secLabs q1) (max (domain g)))
         ++ (b1, b2, vis, t2) :: removeEntry (b1, b2) g)
      (dPar (pmap p x1 x2 b1 b2) (dBang a1 a2 x1 x2 q1)) pf0 
      a1 a2 b1 b2 un pol2 t as EXPLUS.
    
    assert (TPLUS: typeOf g1 (a1, a2) (Chan un pol2 t))...
    apply EXPLUS in TPLUS.
    all:try eassumption.
    destruct TPLUS as [ty [t' [TYPx1 TPLUS]]].
    simpl.
    remember (dep_relabel p (domain g1) nd_pf1) as q2.
    exists ((newEntries g1 (secLabs q2) (max (domain g1)))
              ++ (b1, b2, vis, t') :: removeEntry (b1, b2) g1).
    inversion TYPx1; subst. 
    specialize uRin with
      (a1 := a1) (a2 := a2) (b1 := b1) (b2 := b2) (x1 := x1) (x2 := x2)
      (p := p) (t2 := t')
      (pf := nd_pf1) (f := f1) (t1 := ty) (pol := p0) (t := t) as URIN.
    assert (LTS: p0 = inp \/ p0 = io) by intuition.
    apply URIN in LTS.
    unfold q.
    specialize split_dep_relabel with
      g1 g2 g pf1 pf2 pf p pf0 nd_pf1 as DEPEQ.
    apply DEPEQ in TSPLIT as HeqDep.
    rewrite HeqDep...
    apply type_plus_comm...
    assert (f = f1).
    apply fsuper_flag with 
      (pf1 := pf1) (pf2 := pf2) (pf := pf)
      (a := (b1, b2)) (t := t1) (t1 := ty).
    eauto.
    subst...
    eauto.
    eauto.
    subst...
    move g1 at top.
    apply tsuper_payload with
      (pf1 := pf1) (pf2 := pf2) (pf := pf) in H2 as K0.
    destruct K0 as [pol3 TYP11]. inversion TYP11; subst.
    assert (vis = f2 /\ Chan un p0 t0 = Chan un pol3 t).
    apply in_isMap with (x := (a1, a2)) (g := g1)...
    inversion H7. inversion H15. subst...
    eauto.
    eauto.
    rewrite Heqq1...
  - Case lcomL.
    
    intros.
    inversion TCHECK; subst.
    remember pf0 as nd_pf; subst pf0.
    remember pf1 as nd_pf0; subst pf1.
    remember pf2 as nd_pf0'; subst pf2.
    remember pf4 as pf1; subst pf4.
    remember pf3 as pf2; subst pf3.
    remember pf5 as pf3; subst pf5.
    remember pf6 as pf4; subst pf6.
    
    assert (TSPLIT2 := H4); clear H4.
    
    assert (pfC : isMap ((a1, a2, vis, Chan lin out t) :: (b1, b2, vis, s) :: g0)).
    apply cons_removeEntry_app.
    eauto.
    apply nonRecActions2 in LTS1...
    

    + apply split_of_split with
        g3 g4 g1 g2 g pf3 pf4 pf1 pf2 pf
        in TSPLIT2 as TSPLIT3.
      destruct TSPLIT3 as [h [pfh TSPLIT3]].
      remember ((a1, a2, vis, Chan lin empty t)
                  :: removeEntry (a1, a2) h) as h1.
      assert (pfh1 : isMap h1).
      rewrite Heqh1. apply cons_removeEntry.
      apply no_dup_split_no_dup_r in TSPLIT3...

      assert (SPLITOUT: tEnv_split
                          g3
                          h1 
                          ((a1, a2, vis, Chan lin out t) :: (b1, b2, vis, s) :: g0)
                          pf3 pfh1 pfC).
      * assert (pf3' : isMap (removeEntry (a1, a2) g3)).
        apply isMap_removeEntry...
        assert (pfh' : isMap (removeEntry (a1, a2) h1)).
        apply isMap_removeEntry...
        assert (pfC' : isMap (
                           removeEntry (a1, a2)
                             (((a1, a2, vis, Chan lin out t)
                                 :: (b1, b2, vis, s)
                                 :: g0)))).
        apply isMap_removeEntry...
        apply SpLin with
          (n := (a1, a2)) (f := vis) (f' := vis) (g := vis)
          (p := out) (q := empty) (p' := out) (t := t)
          (g''' :=  removeEntry (a1, a2)
                      (((a1, a2, vis, Chan lin out t)
                          :: (b1, b2, vis, s)
                          :: g0)))
          (pf' := pf3')  (pf'' := pfh')  (pf''' := pfC').
        ** econstructor.
        ** eauto.

           
        (* tEnv_split g3 g4 g1 pf3 pf4 pf1 *)
        (*  tEnv_split g3 h g pf3 pfh pf *)
        (* GOAL : In (a1, a2, vis, Chan lin out t) g3 *) 
        ** specialize typeCheck_lts_out with
             g3
             ((a1, a2, vis, Chan lin out t) :: (b1, b2, vis, s) :: g0)
             pf3 p1  a1 a2 b1 b2
             ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, s1) :: g0)
             p2 nd_pf0 as TOUT.
           apply TOUT in H5 as TYP.
           destruct TYP as [m1 [t1 [TYP | TYP]]].
           apply tsuper_payload with
             g3 h g pf3 pfh pf a1 a2 vis lin io t
             in H0 as K0.
           destruct K0 as [pol2 TYP2].
           inversion TYP; inversion TYP2; subst.
           apply fsuper_vis with
             g3 h g pf3 pfh pf (a1, a2)  (Chan lin io t)
             in H0. inversion H0; inversion H3; subst. 
           assert (f = f0 /\ Chan m1 out t1 =  Chan lin pol2 t).
           apply in_isMap with (x := (a1, a2)) (g := g3)...
           inversion H9.  inversion H11; subst. 
           assert (f0 = vis /\ Chan lin out t = t0).
           apply in_isMap with (x := (a1, a2)) (g := g3)...
           inversion H10. subst...
           eauto. eauto.
           
           (* ABSURD: typeOf g3 (a1, a2) (Chan m1 io t1) *)
           specialize typeCheck_lts_in with
             g4
             ((a1, a2, vis, Chan lin inp t) :: (b1, b2, vis, s1) :: g0)
             pf4 q1  a1 a2 b1 b2
             ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, s) :: g0)
             q2 nd_pf0' as TIN.
           apply TIN in H6 as TYP2.
           destruct TYP2 as [m2 [t2 [TYP2 | TYP2]]].
           inversion TYP; inversion TYP2; subst.
           apply tsuper_payload with
             g3 h g pf3 pfh pf a1 a2 vis lin io t
             in H0 as K0.
           destruct K0 as [pol2 TYP3].
           inversion TYP3; subst.
           assert (f = f1 /\ Chan m1 io t1 =  Chan lin pol2 t).
           apply in_isMap with (x := (a1, a2)) (g := g3)...
           inversion H4. inversion H9; subst.
           apply tsub_io with
             g3 g4 g1 pf3 pf4 pf1 a1 a2 f1 lin t
             in H2 as K2. inversion K2; subst. 
           assert (ABS: pol_plus io inp io). 
           apply split_plus_lin with
             g3 g4 g1 pf3 pf4 pf1 a1 a2 t f1 f0 f.
           eauto.
           apply tsuper_payload_r with
             g3 g4 g1 pf3 pf4 pf1 a1 a2 f lin io t
             in H7 as K7. destruct K7 as [pol3 K7]; inversion K7; subst.
           assert (f0 =f2 /\  Chan m2 inp t2 = Chan lin pol3 t).
           apply in_isMap with (x := (a1, a2)) (g := g4)...
           inversion H11. inversion H13; subst...
           eauto. eauto. eauto. inversion ABS...
           eauto. eauto.

           inversion TYP; inversion TYP2; subst.
           apply tsuper_payload with
             g1 g2 g pf1 pf2 pf a1 a2 vis lin io t
             in H0 as K0.
           destruct K0 as [pol3 K0]; inversion K0; subst.
           apply tsuper_payload with
             g3 g4 g1 pf3 pf4 pf1 a1 a2 f1 lin pol3 t
             in H3 as K3.
           destruct K3 as [pol4 K3]; inversion K3; subst.
           assert (f = f2 /\ Chan m1 io t1 = Chan lin pol4 t).
           apply in_isMap with (x := (a1, a2)) (g := g3)...
           inversion H7. inversion H10; subst.
           assert (ABS: pol_plus io io io). 
           apply split_plus_lin with
             g3 g4 g1 pf3 pf4 pf1 a1 a2 t f2 f0 f1.
           eauto.
           apply tsuper_payload_r with
             g3 g4 g1 pf3 pf4 pf1 a1 a2 f1 lin pol3 t
             in H3 as K4.
           destruct K4 as [pol4 K4]; inversion K4; subst.
           assert (f0 = f /\ Chan m2 io t2 = Chan lin pol4 t).
           apply in_isMap with (x := (a1, a2)) (g := g4)...
           inversion H11.  inversion H13; subst...
           
           eauto.
           apply tsub_io with
             g3 g4 g1 pf3 pf4 pf1 a1 a2 f2 lin t
             in H2 as K2. inversion K2; subst.
           assert (f1 = f /\ Chan lin pol3 t = Chan lin io t).
           apply in_isMap with (x := (a1, a2)) (g := g1)...
           inversion H11. subst...
           eauto. 
           eauto.
           inversion ABS. 
           all:try eassumption.

        ** rewrite Heqh1...
        ** (* tEnv_split g3 h g pf3 pfh pf *)
          (* GOAL : tEnv_split (removeEntry (a1, a2) g3) (removeEntry (a1, a2) h1)
    (removeEntry (a1, a2) ((a1, a2, vis, Chan lin out t) :: (b1, b2, vis, s) :: g0)) pf3'
    pfh' pfC' *)
          revert dependent pf3'.
          revert dependent pfh'.
          revert dependent pfC'.
          rewrite Heqh1.
          subst g0.
          unfold removeEntry; assert (PEQ: pair_eq (a1,a2) (a1,a2)=true) by apply pairEq_eq_true.  rewrite PEQ.
          fold removeEntry.
          assert (SHIFT: ((b1, b2, vis, s) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)) = removeEntry (a1, a2) ((b1, b2, vis, s) :: (removeEntry (b1, b2) g))).
          apply removeEntry_shift.
          apply nonRecActions2 in LTS1...
          rewrite SHIFT.
          intros.
          clear IHLTS1 IHLTS2.
          assert (nd_pfD: NoDup (domain ((b1, b2, vis, s) :: removeEntry (b1, b2) g))).
          apply no_dup_cons_removeEntry.
          apply no_dup_split_no_dup with
            g1 g2 pf1 pf2 pf...
          apply no_dup_isMap in nd_pfD as pfD.
          apply split_remove with
            (pf1 := pf3) (pf2 := pfh) (pf3 := pfD).
          apply no_dup_split_no_dup_l with h g pf3 pfh pf...
          apply no_dup_split_no_dup_r with g3 g pf3 pfh pf...
          eauto.
          eauto.
        ** tauto. 
        ** eauto.
        ** eauto.
      * apply no_dup_split_no_dup_l in TSPLIT3 as nd_pf3.
        specialize IHLTS1 with (pf1 := pf3) (pf2 := pfh1) (pf := pfC) (nd_pf1 := nd_pf3).
        apply IHLTS1 in SPLITOUT.
        destruct SPLITOUT as [k1 LTSOUT].

        apply split_comm in TSPLIT2 as TSPLIT4. 
        apply split_of_split with
          g4 g3 g1 g2 g pf4 pf3 pf1 pf2 pf
          in TSPLIT4 as TSPLIT5.
        destruct TSPLIT5 as [w [pfw TSPLIT5]].
        (* TSPLIT5 : tEnv_split g4 w g pf4 pfw pf *)
        remember ((a1, a2, vis, Chan lin empty t) :: removeEntry (a1, a2) w) as w1.
        assert (pfw1 : isMap w1).
        rewrite Heqw1. apply cons_removeEntry.
        apply no_dup_split_no_dup_r in TSPLIT5...
        apply no_dup_isMap in  nd_pf0' as pfD.

        specialize IHLTS2 with (pf1 := pf4).
        
        
        assert (T3b : exists s3,
                   In (b1, b2, vis, s3) g3).
        specialize fsuper_vis with g3 h g pf3 pfh pf (b1, b2) s as FVIS.
        
        apply FVIS in TSPLIT3 as FVIS3.
        destruct FVIS3 as [FVIS3 FVISW].
        destruct s.
        apply tsuper_payload with
          (pf1 := pf3) (pf2 := pfh) (pf := pf) in H1 as T1b.
        destruct T1b as [pq1 T1b]. exists (Chan m pq1 s).
        inversion T1b. inversion FVIS3. subst.
        assert (f = vis /\ Chan m pq1 s = t1).
        apply in_isMap with (x := (b1, b2)) (g := g3)...
        destruct H3; subst...
        eauto.
        apply tsuper_top with
          (pf1 := pf3) (pf2 := pfh) (pf := pf) in H1 as T1b.
        exists Top.
        inversion FVIS3. inversion T1b. subst.
        assert (f0 = vis /\ Top = t0).
        apply in_isMap with (x := (b1, b2)) (g := g3)...
        destruct H3; subst...
        eauto.
        eauto.
        destruct T3b as [s3 T3b].
        
        apply tsuper_payload with
          (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as K0.
        destruct K0 as [q' TYP']; inversion TYP'; subst.
        apply tsuper_payload with
          (pf1 := pf3) (pf2 := pf4) (pf := pf1) in H2 as K2.
        destruct K2 as [q'' TYP2]; inversion TYP2; subst.
        assert (LEM1:
                 exists r3,
                   type_remove s3 t r3)...
        assert (T4b : exists s4,
                   In (b1, b2, vis, s4) g4).
        specialize fsuper_vis with g4 w g pf4 pfw pf (b1, b2) s as FVIS.
        
        apply FVIS in TSPLIT5 as FVIS3.
        destruct FVIS3 as [FVIS3 FVISW].
        destruct s.
        apply tsuper_payload with
          (pf1 := pf4) (pf2 := pfw) (pf := pf) in H1 as T1b.
        destruct T1b as [pq1 T1b]. exists (Chan m pq1 s).
        inversion T1b. inversion FVIS3. subst.
        assert (f1 = vis /\ Chan m pq1 s = t1).
        apply in_isMap with (x := (b1, b2)) (g := g4)...
        destruct H7; subst...
        eauto.
        apply tsuper_top with
          (pf1 := pf4) (pf2 := pfw) (pf := pf) in H1 as T1b.
        exists Top.
        inversion FVIS3. inversion T1b. subst.
        assert (f2 = vis /\ Top = t0).
        apply in_isMap with (x := (b1, b2)) (g := g4)...
        destruct H7; subst...
        eauto.
        eauto.
        
        destruct T4b as [s4 T4b].
        
        assert (TYPw : exists sw, In ((b1, b2), vis, sw) w /\
                                    type_plus s4 sw s).
        specialize split_type_plus with
          g4 w g pf4 pfw pf (b1, b2) s4 s as TP1.
        assert (TYP4: typeOf g4 (b1, b2) s4)...
        apply TP1 in TYP4. clear TP1.
        destruct TYP4 as [t2 [INw TP4]].
        exists t2.
        inversion INw; subst.
        apply fsub_vis with
          (pf1 := pf4) (pf2 := pfw) (pf := pf) in T4b as FYP.
        inversion FYP; subst.
        apply fsuper_vis with
          (pf1 := pf4) (pf2 := pfw) (pf := pf) in H7 as FYP2.
        destruct FYP2 as [FYP4 FYPw]; inversion FYPw; subst.
        assert (f1 = vis /\ t2 = t1).
        apply in_isMap with (x := (b1, b2)) (g := w)...
        destruct H9; subst...
        all:eauto.
        
        assert (nd_pf4 : NoDup(domain g4)).
        apply no_dup_split_no_dup_l with
          (pf1 := pf4) (pf2 := pfw) (pf := pf)
          in nd_pf as nd_pf4...
        specialize split_type_plus_r with
          g4 g3 g1 pf4 pf3 pf1 (b1, b2) s4 s3 as TP1...
        assert (TYP4: typeOf g4 (b1, b2) s4)...
        apply TP1 in TYP4. clear TP1.
        destruct TYP4 as [s' [IN1 TPLUS1]].
        assert (TYP3: type_sub t s3).
        destruct LEM1 as [r3 TREM].
        assert (TREM2 := TREM); inversion TREM2...
        assert (TYP1 : type_sub s' s)...
        
        assert (IHPREQ : exists r2, type_plus s4 r2 s1).
        apply type_plus_exists with
          (s := s) (t := t) (s3 := s3) (s' := s')...
        destruct IHPREQ as [r2 IHPREQ].
        remember ((a1, a2, vis, Chan lin empty t)
                    :: (b1, b2, vis, r2)
                    :: removeEntry (a1, a2) (removeEntry (b1, b2) w)) as w2. 
        assert (pfw2 : isMap w2). rewrite Heqw2. 
        apply cons_removeEntry_app.
        try eapply no_dup_split_no_dup_r in TSPLIT5;
          try eassumption.
          try eapply nonRecActions2...
        remember ((a1, a2, vis, Chan lin empty t)
                    :: (b1, b2, vis, s4)
                    :: removeEntry (a1, a2) (removeEntry (b1, b2) w)) as w3. 
        assert (pfw3 : isMap w3). rewrite Heqw3. 
        apply cons_removeEntry_app;
          try eapply no_dup_split_no_dup_r in nd_pf...
        assert (pf0' :
                 isMap ((a1, a2, vis, Chan lin inp t) :: (b1, b2, vis, s1) :: g0)).
        apply cons_removeEntry_app...
        assert (IHTSPLIT:
                 (~is_unrestricted r2 /\ tEnv_split g4 w2 ((a1, a2, vis, Chan lin inp t) :: (b1, b2, vis, s1) :: g0) pf4 pfw2 pf0') \/ 
                   (is_unrestricted r2 /\ tEnv_split g4 w3 ((a1, a2, vis, Chan lin inp t) :: (b1, b2, vis, s1) :: g0) pf4 pfw3 pf0')).
        destruct s1. inversion IHPREQ. subst.
        assert (pf' : isMap (removeEntry (b1, b2) g4)).
        apply isMap_removeEntry...
        assert (pf'' : isMap (removeEntry (b1, b2) ((a1, a2, vis, Chan lin empty t)
                                                      :: (b1, b2, vis, Chan lin p3 s1) :: removeEntry (a1, a2) (removeEntry (b1, b2) w)))).
        apply isMap_removeEntry...
        assert (pf''' : isMap (removeEntry (b1, b2) ((a1, a2, vis, Chan lin inp t) :: (b1, b2, vis, Chan lin p s1) :: g0))).
        apply isMap_removeEntry...

        left.
        split. unfold is_unrestricted. intro ABS.
        destruct ABS as [p9 [t9 ABS]]; inversion ABS.
        apply SpLin with
          (n := (b1, b2)) (f := vis) (g := vis) (f' := vis)
          (p := p0) (q := p3) (p' := p) (t := s1)
          (pf' := pf') (pf'' := pf'') (pf''' := pf''').
        all:try eassumption.
        eauto.
        eauto.
        (* tEnv_split (removeEntry (b1, b2) g4)
    (removeEntry (b1, b2)
       ((a1, a2, vis, Chan lin empty t)
        :: (b1, b2, vis, Chan lin p3 s1) :: removeEntry (a1, a2) (removeEntry (b1, b2) w)))
    (removeEntry (b1, b2) ((a1, a2, vis, Chan lin inp t) :: (b1, b2, vis, Chan lin p s1) :: g0))
    pf' pf'' pf''' *)
        apply split_remove with
          (pf1 :=  pf4) (pf2 := pfw2) (pf3 := pf0').
        eauto. 
        apply no_dup_cons_removeEntry_app;
          try eapply no_dup_split_no_dup_r in nd_pf...
        subst g0. apply no_dup_cons_removeEntry_app...
        apply split_new_lin_lin with
          (pf1 := pf4) (pf2 := pfw) (pf := pf)
          (f1 := vis) (p1 := inp) (h1 := vis) (q1 := p0).
        eauto. eauto.
        specialize typeCheck_lts_in with
          g4 ((a1, a2, vis, Chan lin inp t) :: (b1, b2, vis, Chan lin p s1) :: g0) pf4 q1 a1 a2 b1 b2
          ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, s) :: g0) q2 nd_pf0' as TYP1a.
        apply TYP1a in H6 as TYP1a'.
        clear TYP1a.
        destruct TYP1a' as [m [u TYP1a']].
        specialize typeCheck_lts_out with
          g3 ((a1, a2, vis, Chan lin out t) :: (b1, b2, vis, s) :: g0) pf3 p1 a1 a2 b1 b2
          ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, Chan lin p s1) :: g0) p2 nd_pf0 as TYP2a.
        apply TYP2a in H5 as TYP2a'.
        clear TYP2a.
        destruct TYP2a' as [m' [u' TYP2a']].
        assert (In (a1, a2, vis, Chan lin inp t) g4 /\
                  In (a1, a2, vis, Chan lin out t) g3).
        apply split_lin_capab with
          (pf1 := pf4) (pf2 := pf3) (pf := pf1)
          (m1 := m) (m2 := m') (t1 := u) (t2 := u') (p := q').
        eauto. eauto. inversion TYP'. subst.
        move g1 at top.
        apply fsuper_vis
          with (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as [K1 K2].
        inversion K1; subst. 
        assert (vis = f1 /\ t0 =  Chan lin q' t).
        apply in_isMap with (x := (a1, a2)) (g := g1)...
        destruct H7; inversion H8; subst...
        eauto. eauto. intuition.
        all:try eassumption; try tauto.
        eauto.
        eauto.
        eauto.
        eapply nonRecActions2...
        eauto.
        eauto.
        
        right. split. unfold is_unrestricted.
        exists p3. exists s1...
        assert (ISUNS: is_unrestricted s).
        subst.  inversion TPLUS1. subst. inversion TYP1...
        subst. 
        inversion H. destruct H7 as [TPS ISUN].
        apply ISUN in ISUNS as ISUN2. subst s. clear ISUN.
        apply tsuper_payload with
          (pf1 := pf1) (pf2 := pf2) (pf := pf) in H1 as K1.
        apply tsuper_payload_r with
          (pf1 := pf1) (pf2 := pf2) (pf := pf) in H1 as K2.
        destruct K1 as [pol1 TB1]. destruct K2 as [pol2 TB2].
        inversion TB1. inversion TB2. subst.
        assert (pol1 = pol2 /\ pol2 = (pol_cup p0 p3)).
        apply split_plus_un with
          (pf1 := pf1) (pf2 := pf2) (pf3 := pf)
          (b1 := b1) (b2 := b2) (t := s1)
          (f1 := f1) (f2 := f2) (f3 := vis)...
        destruct H8; subst.
        apply tsuper_payload_r with
          (pf1 := pf4) (pf2 := pf3) (pf := pf1) in H7 as K7.
        destruct K7 as [pol7 TB3]. inversion TB3; subst. 
        assert (p0 = pol7 /\ pol7 = (pol_cup p0 p3)).
        apply split_plus_un with
          (pf1 := pf4) (pf2 := pf3) (pf3 := pf1)
          (b1 := b1) (b2 := b2) (t := s1)
          (f1 := vis) (f2 := f3) (f3 := f1)...
        destruct H9. assert (POLEQ: p0 = pol_cup p0 p3).
        transitivity pol7...
        revert dependent pf0'.
        rewrite <-POLEQ.
        intros.
        assert (pf' : isMap (removeEntry (b1, b2) g4)).
        apply isMap_removeEntry...
        assert (pf'' : isMap (removeEntry (b1, b2) ((a1, a2, vis, Chan lin empty t)
                                                      :: (b1, b2, vis, Chan un p0 s1) :: removeEntry (a1, a2) (removeEntry (b1, b2) w)))).
        apply isMap_removeEntry...
        assert (pf''' : isMap (removeEntry (b1, b2) ((a1, a2, vis, Chan lin inp t) :: (b1, b2, vis, Chan un p0 s1) :: g0))).
        apply isMap_removeEntry...
        apply SpUn with
          (n := (b1, b2)) (f := vis) (g := vis) (f' := vis)
          (p := p0) (t := s1)
          (pf' := pf') (pf'' := pf'') (pf''' := pf''').
        eauto.
        eauto.
        eauto.
        (*tEnv_split (removeEntry (b1, b2) g4)
    (removeEntry (b1, b2)
       ((a1, a2, vis, Chan lin empty t)
        :: (b1, b2, vis, Chan un p0 s1) :: removeEntry (a1, a2) (removeEntry (b1, b2) w)))
    (removeEntry (b1, b2)
       ((a1, a2, vis, Chan lin inp t) :: (b1, b2, vis, Chan un p0 s1) :: g0)) pf' pf'' pf'''*)
        assert (pf0'' : isMap
                          (((a1, a2, vis, Chan lin inp t) :: (b1, b2, vis, Chan un p0 s1) :: g0))).
        subst g0...
        apply split_remove with
          (pf1 :=  pf4) (pf2 := pfw3) (pf3 := pf0'').
        eauto.
        apply no_dup_cons_removeEntry_app;
          try eapply no_dup_split_no_dup_r in nd_pf...
        subst g0.
        apply no_dup_cons_removeEntry_app...
        (*tEnv_split g4
    ((a1, a2, vis, Chan lin empty t)
     :: (b1, b2, vis, Chan un p0 s1) :: removeEntry (a1, a2) (removeEntry (b1, b2) w))
    ((a1, a2, vis, Chan lin inp t) :: (b1, b2, vis, Chan un p0 s1) :: g0) pf4 pfw3 pf0''*)
        apply split_new_lin_un with
          (pf1 := pf4) (pf2 := pfw) (pf := pf)
          (f1 := vis) (p1 := inp) (h1 := vis) (q := p0).
        eauto. eauto.
        specialize typeCheck_lts_in with
          g4 ((a1, a2, vis, Chan lin inp t) :: (b1, b2, vis, Chan un (pol_cup p0 p3) s1) :: g0) pf4 q1 a1 a2 b1 b2
          ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, Chan un (pol_cup p0 p3) s1) :: g0) q2 nd_pf0' as TYP1a.
        apply TYP1a in H6 as TYP1a'.
        clear TYP1a.
        destruct TYP1a' as [m [u TYP1a']].
        specialize typeCheck_lts_out with
          g3  ((a1, a2, vis, Chan lin out t)
                 :: (b1, b2, vis, Chan un (pol_cup p0 p3) s1) :: g0) pf3 p1 a1 a2 b1 b2
          ((a1, a2, vis, Chan lin empty t)
             :: (b1, b2, vis, Chan un (pol_cup p0 p3) s1) :: g0) p2 nd_pf0 as TYP2a.
        apply TYP2a in H5 as TYP2a'.
        clear TYP2a.
        destruct TYP2a' as [m' [u' TYP2a']].
        assert (In (a1, a2, vis, Chan lin inp t) g4 /\
                  In (a1, a2, vis, Chan lin out t) g3).
        apply split_lin_capab with
          (pf1 := pf4) (pf2 := pf3) (pf := pf1)
          (m1 := m) (m2 := m') (t1 := u) (t2 := u') (p := q').
        eauto. eauto. inversion TYP'. subst.
        move g1 at top.
        apply fsuper_vis
          with (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as [K1 K2].
        inversion K1; subst. 
        assert (vis = f4 /\ t0 =  Chan lin q' t).
        apply in_isMap with (x := (a1, a2)) (g := g1)...
        destruct H9; inversion H10; subst...
        eauto. eauto. 
        destruct H12 as [CAP1 CAP2]...

        eauto.
        eauto. eauto. eauto. eauto. eauto. eauto.
        eauto. eauto. eauto. eauto. eauto. eauto.
        
        left. split. 
        unfold is_unrestricted. intro ABS.
        inversion IHPREQ; subst. 
        destruct ABS as [p9 [t9 ABS]]; inversion ABS.
        inversion IHPREQ; subst.
        assert (pf' : isMap (removeEntry (b1, b2) g4)).
        apply isMap_removeEntry...
        assert (pf'' : isMap (removeEntry (b1, b2) ((a1, a2, vis, Chan lin empty t)
                                                      :: (b1, b2, vis, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) w)))).
        apply isMap_removeEntry...
        assert (pf''' : isMap (removeEntry (b1, b2) ((a1, a2, vis, Chan lin inp t) :: (b1, b2, vis, Top) :: g0))).
        apply isMap_removeEntry...
        apply SpTop with
          (n := (b1, b2)) (f := vis) (g := vis) (f' := vis)
          
          (pf' := pf') (pf'' := pf'') (pf''' := pf''').
        all:try eassumption; try tauto.
        eauto.
        eauto.
        (*tEnv_split (removeEntry (b1, b2) g4)
    (removeEntry (b1, b2)
       ((a1, a2, vis, Chan lin empty t)
        :: (b1, b2, vis, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) w)))
    (removeEntry (b1, b2) ((a1, a2, vis, Chan lin inp t) :: (b1, b2, vis, Top) :: g0)) pf'
    pf'' pf''*)
        assert (pf0'' : isMap
                          (((a1, a2, vis, Chan lin inp t) :: (b1, b2, vis, Top) :: g0))).
        subst g0...
        apply split_remove with
          (pf1 :=  pf4) (pf2 := pfw3) (pf3 := pf0'').
        eauto.
        apply no_dup_cons_removeEntry_app;
          try eapply no_dup_split_no_dup_r in nd_pf...
        subst g0.   apply no_dup_cons_removeEntry_app...
        apply split_new_lin_top with
          (pf1 := pf4) (pf2 := pfw) (pf := pf)
          (f1 := vis) (p1 := inp) (h1 := vis).
        eauto. eauto.
        specialize typeCheck_lts_in with
          g4 ((a1, a2, vis, Chan lin inp t) :: (b1, b2, vis, Top) :: g0) pf4 q1 a1 a2 b1 b2
          ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, s) :: g0) q2 nd_pf0' as TYP1a.
        apply TYP1a in H6 as TYP1a'.
        clear TYP1a.
        destruct TYP1a' as [m [u TYP1a']].
        specialize typeCheck_lts_out with
          g3  ((a1, a2, vis, Chan lin out t)
                 :: (b1, b2, vis, s) :: g0) pf3 p1 a1 a2 b1 b2
          ((a1, a2, vis, Chan lin empty t)
             :: (b1, b2, vis, Top) :: g0) p2 nd_pf0 as TYP2a.
        apply TYP2a in H5 as TYP2a'.
        clear TYP2a.
        destruct TYP2a' as [m' [u' TYP2a']].
        assert (In (a1, a2, vis, Chan lin inp t) g4 /\
                  In (a1, a2, vis, Chan lin out t) g3).
        apply split_lin_capab with
          (pf1 := pf4) (pf2 := pf3) (pf := pf1)
          (m1 := m) (m2 := m') (t1 := u) (t2 := u') (p := q').
        eauto. eauto. inversion TYP'. subst.
        move g1 at top.
        apply fsuper_vis
          with (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as [K1 K2].
        inversion K1; subst. 
        assert (vis = f1 /\ t0 =  Chan lin q' t).
        apply in_isMap with (x := (a1, a2)) (g := g1)...
        destruct H7; inversion H8; subst...
        eauto. eauto. 
        destruct H4 as [CAP1 CAP2]...

        eauto.
        eauto. eauto. eauto. eauto. eauto. eauto.
        eauto. eauto.
        
        destruct r2.
        ***
          destruct m.
          (*  ~ is_unrestricted (Chan lin p r2) *)
          ****
            assert (G4IN: exists (m : mode) (t : piType),
                       typeOf g4 (a1, a2) (Chan m inp t) \/ typeOf g4 (a1, a2) (Chan m io t)).
            apply typeCheck_lts_in with
              ((a1, a2, vis, Chan lin inp t) :: (b1, b2, vis, s1) :: g0) pf4 q1 b1 b2
              ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, s) :: g0) q2 nd_pf0'...
            destruct G4IN as [m4 [t4 TYP4]].
            assert (G4OUT: exists (m : mode) (t : piType),
                       typeOf g3 (a1, a2) (Chan m out t) \/ typeOf g3 (a1, a2) (Chan m io t)).
            apply typeCheck_lts_out with
              ((a1, a2, vis, Chan lin out t) :: (b1, b2, vis, s) :: g0) pf3 p1 b1 b2
              ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, s1) :: g0) p2 nd_pf0...
            destruct G4OUT as [m4' [t4' TYP4']].
            move g1 at top. apply fsuper_vis with
              (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as K0. destruct K0 as [K1 K2].
            inversion K1; subst.
            assert (vis = f /\ t0 = Chan lin q' t).
            apply in_isMap with (x := (a1, a2)) (g := g1)...
            destruct H7; subst.
            assert (CAP: In (a1, a2, vis, Chan lin inp t) g4 /\
                           In (a1, a2, vis, Chan lin out t) g3).
            
            apply split_lin_capab with
              (pf1 := pf4) (pf2 := pf3) (pf := pf1)
              (m1 := m4) (m2 := m4') (t1 := t4) (t2 := t4')
              (p := q')...
            destruct CAP as [CAP1 CAP2]...
            assert (TP4 : exists t2 : piType, typeOf g1 (a1, a2) t2 /\ type_plus ( Chan lin inp t) ( Chan lin out t) t2).
            apply split_type_plus_r with
              (pf1 := pf4) (pf2 := pf3) (pf := pf1)...
            destruct TP4 as [u1 [TYPa1 TPP]].
            inversion TPP; subst. inversion H11; subst.
            inversion TYPa1; subst.
            assert (f = vis /\ Chan lin io t = Chan lin q' t).
            apply in_isMap with (x := (a1, a2)) (g := g1)...
            destruct H8; subst. assert (CAP3 := H7).
            clear H7 H9 K1 K2.
            
            destruct IHTSPLIT as
              [[NOTUN IHTSPLIT] | ABS].
            specialize IHLTS2 with
              (nd_pf1 := nd_pf4) (pf2 := pfw2) (pf := pf0').
            
            apply IHLTS2 in IHTSPLIT.
            destruct IHTSPLIT as [k4 LTSIN].
            
            assert (LEM2:
                     exists r4,
                       type_plus s4 t r4).
            apply plus_sub_exists with
              (s := s3) (r := s')...
            
            destruct LEM1 as [r3 TREM].
            destruct LEM2 as [r4 TPLUS].

            specialize split_exists_remove_l with
              g3 g4 g1 pf3 pf4 pf1 b1 b2 vis t s3 r3 as EXREM.
            apply EXREM in T3b as TYP3'.
            destruct TYP3' as [s'' [r'' [TYP1' TREM1]]].

            assert(nd_pfw1 :
                    NoDup(domain
                            ((a1, a2, vis, Chan lin out t)
                               :: (b1, b2, vis, s'')
                               :: removeEntry (a1, a2)
                               (removeEntry (b1, b2) g1)))).
            apply no_dup_cons_removeEntry_app...
            assert (nd_pfw2 :
                     NoDup(domain
                             ((a1, a2, vis, Chan lin inp t)
                                :: (b1, b2, vis, r'')
                                :: removeEntry (a1, a2)
                                (removeEntry (b1, b2) g1)))).
            apply no_dup_cons_removeEntry_app...
            
            exists (((a1, a2), vis, Chan lin empty t)
                      :: ((b1, b2), vis, s'')
                      :: removeEntry (a1, a2)
                      (removeEntry (b1, b2) g1)).
            apply lcomL with
              (s1 := r'') (pf1 := nd_pfw1) (pf2 := nd_pfw2).
            eauto.
            eauto. 
            
            inversion TYP1'; subst.
            move g1 at top. apply fsuper_vis with
              (pf1 := pf1) (pf2 := pf2) (pf := pf) in H1 as K1. destruct K1 as [K1 K2].
            inversion K1; subst.
            assert (vis = f /\ t0 = s'').
            apply in_isMap with (x := (b1, b2)) (g := g1)...
            destruct H9; subst...
            eauto. 

            remember ((a1, a2, vis, Chan lin out t)
                        :: (b1, b2, vis, s'') :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) as gk1.
            assert (EQREM: removeEntry (a1, a2) (removeEntry (b1, b2) gk1) =
                             removeEntry (a1, a2) (removeEntry (b1, b2) g1)).
            rewrite Heqgk1.
            rewrite removeEntry_swap.
            unfold removeEntry at 2.
            assert (PEQ: pair_eq (a1, a2) (a1, a2) = true)...
            rewrite PEQ.
            unfold removeEntry at 1.
            assert (PEQ2: pair_eq (b1, b2) (b1, b2) = true)...
            rewrite PEQ2...
            eauto.
            specialize lts_type_remove_lin_out with
              (a1 := a1) (a2 := a2) (t := t) (b1 := b1) (b2 := b2)
              (f := vis) (f1 := vis) (g1 := gk1)
              (s01 := r'') (s := s3) (s1 := r3) (s0 := s'')
              (g0 := g3) (p1 := p1) (p2 := p2)
              (pf0 := nd_pf3) (pf1 := nd_pfw1)
              as LINOUT.
            rewrite <-EQREM.
            assert (Heqk1:
                     k1 =  ((a1, a2, vis, Chan lin empty t)
                              :: (b1, b2, vis, r3) :: removeEntry (a1, a2) (removeEntry (b1, b2) g3))).

            apply lts_lin_output_action with
              (p := p1) (p' := p2) (nd_pf := nd_pf3)
              (pol := out) (s := s3)...
            
            rewrite <-Heqk1 in LINOUT.

            apply LINOUT in LTSOUT as IH.
            eauto.
            eauto.
            eauto.
            eauto.
            rewrite Heqgk1...
            rewrite Heqgk1...
            subst gk1.
            introv;
            erewrite <-sne_premises.in_removeEntry_cons_iff_2, split_domain_l_2...
            eapply split_domain_l_2... 
            eapply typeCheck_no_dup with (g := g3)...

            subst gk1.
            simpl.
            assert (HIDP3: incl (secLabs (dPar p1 q1)) (domain (hid_proj g1)))...
            eapply typeCheck_hid_proj...
            simpl in HIDP3; eapply incl_app_inv in HIDP3 as [_ HIDP3].
            introv IN; simpl.
            assert (IN2:In a (domain (hid_proj  g1))).
            eapply HIDP3 in IN...
            assert (IN2' := IN2).
            eapply in_domain_in_g in IN2' as (ff &tt &IN2');
              repeat erewrite <-hid_proj_removeEntry; 
              try eapply in_g_in_domain, removeEntry_in...
            introv ABS; subst a.
            assert (ABS: flagOf g1 (a1, a2) hid).
            eapply hid_proj_flagOf...
            inv ABS.
            assert (ABS2: vis = hid /\ Chan lin io t = t0)...
            destruct ABS2; try discriminate.
            eapply removeEntry_in...
            introv ABS; subst a.
            assert (ABS: flagOf g1 (b1, b2) hid).
            eapply hid_proj_flagOf...
            eapply fsuper_vis in TSPLIT as [ABS2 _]...
            inv ABS; inv ABS2.
            assert (ABS2: vis = hid /\ t1 = t0)...
            destruct ABS2; try discriminate.
            
            (* as above by using lts_lin_input_action *)
            remember ((a1, a2, vis, Chan lin inp t)
                        :: (b1, b2, vis, r'') :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) as gk1.
            assert (EQREM: removeEntry (a1, a2) (removeEntry (b1, b2) gk1) =
                             removeEntry (a1, a2) (removeEntry (b1, b2) g1)).
            rewrite Heqgk1.
            rewrite removeEntry_swap.
            unfold removeEntry at 2.
            assert (PEQ: pair_eq (a1, a2) (a1, a2) = true)...
            rewrite PEQ.
            unfold removeEntry at 1.
            assert (PEQ2: pair_eq (b1, b2) (b1, b2) = true)...
            rewrite PEQ2...
            eauto.

            rewrite <-EQREM.
            move LTSIN at bottom.

            (*specialize lts_type_plus_lin_in with
                (a1 := a1) (a2 := a2) (t := t) (b1 := b1) (b2 := b2)
                (f := vis) (f1 := vis) (g1 := gk1)
                (s01 := s4) (s := r4) (s1 := s4) (s0 := r4)
                (q1 := q1) (q2 := q2)
                (pf := nd_pf4) (pf1 := nd_pfw2)
              as LININ.*)
            assert (Heqk4:
                     k4 =  ((a1, a2, vis, Chan lin empty t)
                              :: (b1, b2, vis, r4) :: removeEntry (a1, a2) (removeEntry (b1, b2) g4))).
            apply lts_lin_input_action with
              (p := q1) (p' := q2) (nd_pf := nd_pf4)
              (pol := inp) (s := s4)...
            (*rewrite <-Heqk4 in LININ.*)
            
            eapply lts_type_plus_lin_in;
              try rewrite <-Heqk4; subst gk1;
              try eassumption;
              try tauto.
            eauto.
            eauto.
            inverts TREM1 as [TP _]; eapply type_plus_comm...
            discriminate.
            (* forall x : name * name,
  In x (domain g4) <->
  In x (domain ((a1, a2, vis, Chan lin inp t) :: (b1, b2, vis, r'') :: removeEntry (a1, a2) (removeEntry (b1, b2) g1))) *)
             introv;
            erewrite <-sne_premises.in_removeEntry_cons_iff_2, split_domain_l_2...
             eapply split_domain_l_2...
            eapply typeCheck_no_dup with (g := g4)...

            assert (TCHECK2 := TCHECK).
            inv TCHECK2; try eapply typeCheck_no_dup with (pf := pf5);
              try assumption; try eapply no_dup_split_no_dup_r with (g := g1)...
            
            simpl.
            assert (HIDP3: incl (secLabs (dPar p1 q1)) (domain (hid_proj g1)))...
            eapply typeCheck_hid_proj...
            simpl in HIDP3; eapply incl_app_inv in HIDP3 as [HIDP3 _].
            introv IN; simpl.
            assert (IN2:In a (domain (hid_proj  g1))).
            eapply HIDP3 in IN...
            assert (IN2' := IN2).
            eapply in_domain_in_g in IN2' as (ff &tt &IN2');
              repeat erewrite <-hid_proj_removeEntry; 
              try eapply in_g_in_domain, removeEntry_in...
            introv ABS; subst a.
            assert (ABS: flagOf g1 (a1, a2) hid).
            eapply hid_proj_flagOf...
            inv ABS.
            assert (ABS2: vis = hid /\ Chan lin io t = t0)...
            destruct ABS2; try discriminate.
            eapply removeEntry_in...
            introv ABS; subst a.
            assert (ABS: flagOf g1 (b1, b2) hid).
            eapply hid_proj_flagOf...
            eapply fsuper_vis in TSPLIT as [ABS2 _]...
            inv ABS; inv ABS2.
            assert (ABS2: vis = hid /\ t1 = t0)...
            destruct ABS2; try discriminate.

            
            eauto.
            eauto.
            eapply sl_pos_par_r...
            eauto.
            2:{ eauto. }
              unfold is_unrestricted in ABS.
            destruct ABS as [ABS1 ABS2].
            destruct ABS1 as [p0 [t0 ABS1]];inversion ABS1...
          ****
            destruct IHTSPLIT as
              [[ABS _] | [UN IHTSPLIT]].
            unfold is_unrestricted in ABS.
            elim ABS. exists p. exists r2...
            
            assert (G4IN: exists (m : mode) (t : piType),
                       typeOf g4 (a1, a2) (Chan m inp t) \/ typeOf g4 (a1, a2) (Chan m io t)).
            apply typeCheck_lts_in with
              ((a1, a2, vis, Chan lin inp t) :: (b1, b2, vis, s1) :: g0) pf4 q1 b1 b2
              ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, s) :: g0) q2 nd_pf0'...
            destruct G4IN as [m4 [t4 TYP4]].
            assert (G4OUT: exists (m : mode) (t : piType),
                       typeOf g3 (a1, a2) (Chan m out t) \/ typeOf g3 (a1, a2) (Chan m io t)).
            apply typeCheck_lts_out with
              ((a1, a2, vis, Chan lin out t) :: (b1, b2, vis, s) :: g0) pf3 p1 b1 b2
              ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, s1) :: g0) p2 nd_pf0...
            destruct G4OUT as [m4' [t4' TYP4']].
            move g1 at top. apply fsuper_vis with
              (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as K0. destruct K0 as [K1 K2].
            inversion K1; subst.
            assert (vis = f /\ t0 = Chan lin q' t).
            apply in_isMap with (x := (a1, a2)) (g := g1)...
            destruct H7; subst.
            assert (CAP: In (a1, a2, vis, Chan lin inp t) g4 /\
                           In (a1, a2, vis, Chan lin out t) g3).
            
            apply split_lin_capab with
              (pf1 := pf4) (pf2 := pf3) (pf := pf1)
              (m1 := m4) (m2 := m4') (t1 := t4) (t2 := t4')
              (p := q')...
            destruct CAP as [CAP1 CAP2]...
            assert (TP4 : exists t2 : piType, typeOf g1 (a1, a2) t2 /\ type_plus ( Chan lin inp t) ( Chan lin out t) t2).
            apply split_type_plus_r with
              (pf1 := pf4) (pf2 := pf3) (pf := pf1)...
            destruct TP4 as [u1 [TYPa1 TPP]].
            inversion TPP; subst. inversion H11; subst.
            inversion TYPa1; subst.
            assert (f = vis /\ Chan lin io t = Chan lin q' t).
            apply in_isMap with (x := (a1, a2)) (g := g1)...
            destruct H8; subst. assert (CAP3 := H7).
            clear H7 H9 K1 K2.

            specialize IHLTS2 with
              (nd_pf1 := nd_pf4) (pf2 := pfw3) (pf := pf0').
            
            apply IHLTS2 in IHTSPLIT.
            destruct IHTSPLIT as [k4 LTSIN].

            assert (LEM2:
                     exists r4,
                       type_plus s4 t r4).
            
            apply plus_sub_exists with (s := s3) (r := s')...

            destruct LEM1 as [r3 TREM].
            destruct LEM2 as [r4 TPLUS].

            specialize split_exists_remove_l with
              g3 g4 g1 pf3 pf4 pf1 b1 b2 vis t s3 r3 as EXREM.
            apply EXREM in T3b as TYP3'.
            destruct TYP3' as [s'' [r'' [TYP1' TREM1]]].

            assert(nd_pfw1 :
                    NoDup(domain
                            ((a1, a2, vis, Chan lin out t)
                               :: (b1, b2, vis, s'')
                               :: removeEntry (a1, a2)
                               (removeEntry (b1, b2) g1)))).
            apply no_dup_cons_removeEntry_app...
            assert (nd_pfw2 :
                     NoDup(domain
                             ((a1, a2, vis, Chan lin inp t)
                                :: (b1, b2, vis, r'')
                                :: removeEntry (a1, a2)
                                (removeEntry (b1, b2) g1)))).
            apply no_dup_cons_removeEntry_app...
            exists (((a1, a2), vis, Chan lin empty t)
                      :: ((b1, b2), vis, s'')
                      :: removeEntry (a1, a2)
                      (removeEntry (b1, b2) g1)).
            apply lcomL with
              (s1 := r'') (pf1 := nd_pfw1) (pf2 := nd_pfw2).
            eauto.
            eauto.
            inversion TYP1'; subst.
            move g1 at top. apply fsuper_vis with
              (pf1 := pf1) (pf2 := pf2) (pf := pf) in H1 as K1. destruct K1 as [K1 K2].
            inversion K1; subst.
            assert (vis = f /\ t0 = s'').
            apply in_isMap with (x := (b1, b2)) (g := g1)...
            destruct H9; subst...
            eauto. 

            remember ((a1, a2, vis, Chan lin out t)
                        :: (b1, b2, vis, s'') :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) as gk1.
            assert (EQREM: removeEntry (a1, a2) (removeEntry (b1, b2) gk1) =
                             removeEntry (a1, a2) (removeEntry (b1, b2) g1)).
            rewrite Heqgk1...
            specialize lts_type_remove_lin_out with
              (a1 := a1) (a2 := a2) (t := t) (b1 := b1) (b2 := b2)
              (f := vis) (f1 := vis) (g1 := gk1)
              (s01 := r'') (s := s3) (s1 := r3) (s0 := s'')
              (g0 := g3) (p1 := p1) (p2 := p2)
              (pf0 := nd_pf3) (pf1 := nd_pfw1)
              as LINOUT.
            rewrite <-EQREM.
            assert (Heqk1:
                     k1 =  ((a1, a2, vis, Chan lin empty t)
                              :: (b1, b2, vis, r3) :: removeEntry (a1, a2) (removeEntry (b1, b2) g3))).
            apply lts_lin_output_action with
              (p := p1) (p' := p2) (nd_pf := nd_pf3) (pol := out) (s := s3)...
            rewrite <-Heqk1 in LINOUT.

            apply LINOUT in LTSOUT as IH.
            eauto.
            eauto. 
            eauto.
            eauto.
            rewrite Heqgk1...
            rewrite Heqgk1...
            rewrite Heqgk1.
            (* forall x : name * name,
  In x (domain g3) <->
  In x (domain ((a1, a2, vis, Chan lin out t) :: (b1, b2, vis, s'') :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)))*)
             introv;
            erewrite <-sne_premises.in_removeEntry_cons_iff_2, split_domain_l_2...
            eapply split_domain_l_2... 
            eapply typeCheck_no_dup with (g := g3)...

            
            rewrite Heqgk1...
            simpl.
            assert (HIDP3: incl (secLabs (dPar p1 q1)) (domain (hid_proj g1)))...
            eapply typeCheck_hid_proj...
            simpl in HIDP3; eapply incl_app_inv in HIDP3 as [_ HIDP3].
            introv IN; simpl.
            assert (IN2:In a (domain (hid_proj  g1))).
            eapply HIDP3 in IN...
            assert (IN2' := IN2).
            eapply in_domain_in_g in IN2' as (ff &tt &IN2');
              repeat erewrite <-hid_proj_removeEntry; 
              try eapply in_g_in_domain, removeEntry_in...
            introv ABS; subst a.
            assert (ABS: flagOf g1 (a1, a2) hid).
            eapply hid_proj_flagOf...
            inv ABS.
            assert (ABS2: vis = hid /\ Chan lin io t = t0)...
            destruct ABS2; try discriminate.
            eapply removeEntry_in...
            introv ABS; subst a.
            assert (ABS: flagOf g1 (b1, b2) hid).
            eapply hid_proj_flagOf...
            eapply fsuper_vis in TSPLIT as [ABS2 _]...
            inv ABS; inv ABS2.
            assert (ABS2: vis = hid /\ t1 = t0)...
            destruct ABS2; try discriminate.
            
            (* as above by using lts_lin_input_action *)
            
            remember ((a1, a2, vis, Chan lin inp t)
                        :: (b1, b2, vis, r'') :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) as gk1.
            assert (EQREM: removeEntry (a1, a2) (removeEntry (b1, b2) gk1) =
                             removeEntry (a1, a2) (removeEntry (b1, b2) g1)).
            rewrite Heqgk1.
            rewrite removeEntry_swap.
            unfold removeEntry at 2.
            assert (PEQ: pair_eq (a1, a2) (a1, a2) = true)...
            rewrite PEQ.
            unfold removeEntry at 1.
            assert (PEQ2: pair_eq (b1, b2) (b1, b2) = true)...
            rewrite PEQ2...
            eauto.

            assert (EQREM2: removeEntry (a1, a2) (removeEntry (b1, b2) gk1) =
                              removeEntry (a1, a2) (removeEntry (b1, b2) g1)).
            rewrite Heqgk1.
            rewrite removeEntry_swap.
            unfold removeEntry at 2.
            assert (PEQ: pair_eq (a1, a2) (a1, a2) = true)...
            rewrite PEQ.
            unfold removeEntry at 1.
            assert (PEQ2: pair_eq (b1, b2) (b1, b2) = true)...
            rewrite PEQ2...
            eauto.

            rewrite <-EQREM2.
            assert (Heqk4:
                     k4 =  ((a1, a2, vis, Chan lin empty t)
                              :: (b1, b2, vis, r4) :: removeEntry (a1, a2) (removeEntry (b1, b2) g4))).
            apply lts_lin_input_action with
              (p := q1) (p' := q2) (nd_pf := nd_pf4)
              (pol := inp) (s := s4)...
            (*rewrite <-Heqk4 in LININ.*)

            
            eapply lts_type_plus_lin_in;
              try rewrite <-Heqk4; subst gk1;
              try eassumption;
              try tauto.
            eauto.
            eauto.
            inverts TREM1 as [TP _]; eapply type_plus_comm...
              
            discriminate.

            (*forall x : name * name,
  In x (domain g4) <->
  In x (domain ((a1, a2, vis, Chan lin inp t) :: (b1, b2, vis, r'') :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)))*)
            introv;
            erewrite <-sne_premises.in_removeEntry_cons_iff_2, split_domain_l_2...
            eapply split_domain_l_2... 
            eapply typeCheck_no_dup with (g := g4)...
            

            assert (TCHECK2 := TCHECK);
              inv TCHECK2;
              try eapply typeCheck_no_dup with (pf := pf5);
              try assumption; try eapply no_dup_split_no_dup_r with (g := g1)...
            
            simpl.
            assert (HIDP3: incl (secLabs (dPar p1 q1)) (domain (hid_proj g1)))...
            eapply typeCheck_hid_proj...
            simpl in HIDP3; eapply incl_app_inv in HIDP3 as [HIDP3 _].
            introv IN; simpl.
            assert (IN2:In a (domain (hid_proj  g1))).
            eapply HIDP3 in IN...
            assert (IN2' := IN2).
            eapply in_domain_in_g in IN2' as (ff &tt &IN2');
              repeat erewrite <-hid_proj_removeEntry; 
              try eapply in_g_in_domain, removeEntry_in...
            introv ABS; subst a.
            assert (ABS: flagOf g1 (a1, a2) hid).
            eapply hid_proj_flagOf...
            inv ABS.
            assert (ABS2: vis = hid /\ Chan lin io t = t0)...
            destruct ABS2; try discriminate.
            eapply removeEntry_in...
            introv ABS; subst a.
            assert (ABS: flagOf g1 (b1, b2) hid).
            eapply hid_proj_flagOf...
            eapply fsuper_vis in TSPLIT as [ABS2 _]...
            inv ABS; inv ABS2.
            assert (ABS2: vis = hid /\ t1 = t0)...
            destruct ABS2; try discriminate.
            
            
            all:try eassumption.
            eapply sl_pos_par_r...

        *** 
          destruct IHTSPLIT as
            [[NOTUN IHTSPLIT] | ABS].
          specialize IHLTS2 with
            (nd_pf1 := nd_pf4) (pf2 := pfw2) (pf := pf0').

          assert (G4IN: exists (m : mode) (t : piType),
                     typeOf g4 (a1, a2) (Chan m inp t) \/ typeOf g4 (a1, a2) (Chan m io t)).
          apply typeCheck_lts_in with
            ((a1, a2, vis, Chan lin inp t) :: (b1, b2, vis, s1) :: g0) pf4 q1 b1 b2
            ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, s) :: g0) q2 nd_pf0'...
          destruct G4IN as [m4 [t4 TYP4]].
          assert (G4OUT: exists (m : mode) (t : piType),
                     typeOf g3 (a1, a2) (Chan m out t) \/ typeOf g3 (a1, a2) (Chan m io t)).
          apply typeCheck_lts_out with
            ((a1, a2, vis, Chan lin out t) :: (b1, b2, vis, s) :: g0) pf3 p1 b1 b2
            ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, s1) :: g0) p2 nd_pf0...
          destruct G4OUT as [m4' [t4' TYP4']].
          move g1 at top. apply fsuper_vis with
            (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as K0. destruct K0 as [K1 K2].
          inversion K1; subst.
          assert (vis = f /\ t0 = Chan lin q' t).
          apply in_isMap with (x := (a1, a2)) (g := g1)...
          destruct H7; subst.
          assert (CAP: In (a1, a2, vis, Chan lin inp t) g4 /\
                         In (a1, a2, vis, Chan lin out t) g3).
          
          apply split_lin_capab with
            (pf1 := pf4) (pf2 := pf3) (pf := pf1)
            (m1 := m4) (m2 := m4') (t1 := t4) (t2 := t4')
            (p := q')...
          destruct CAP as [CAP1 CAP2]...
          assert (TP4 : exists t2 : piType, typeOf g1 (a1, a2) t2 /\ type_plus ( Chan lin inp t) ( Chan lin out t) t2).
          apply split_type_plus_r with
            (pf1 := pf4) (pf2 := pf3) (pf := pf1)...
          destruct TP4 as [u1 [TYPa1 TPP]].
          inversion TPP; subst. inversion H11; subst.
          inversion TYPa1; subst.
          assert (f = vis /\ Chan lin io t = Chan lin q' t).
          apply in_isMap with (x := (a1, a2)) (g := g1)...
          destruct H8; subst. assert (CAP3 := H7).
          clear H7 H9 K1 K2.
          
          apply IHLTS2 in IHTSPLIT.
          destruct IHTSPLIT as [k4 LTSIN].
          assert(nd_pfw1 :
                  NoDup(domain
                          ((a1, a2, vis, Chan lin out t)
                             :: (b1, b2, vis, Top)
                             :: removeEntry (a1, a2)
                             (removeEntry (b1, b2) g1)))).
          apply no_dup_cons_removeEntry_app...
          assert (nd_pfw2 :
                   NoDup(domain
                           ((a1, a2, vis, Chan lin inp t)
                              :: (b1, b2, vis, Top)
                              :: removeEntry (a1, a2)
                              (removeEntry (b1, b2) g1)))).
          apply no_dup_cons_removeEntry_app...
          exists (((a1, a2), vis, Chan lin empty t)
                    :: ((b1, b2), vis, Top)
                    :: removeEntry (a1, a2)
                    (removeEntry (b1, b2) g1)).
          apply lcomL with
            (s1 := Top) (pf1 := nd_pfw1) (pf2 := nd_pfw2).

          inversion IHPREQ. subst. inversion TPLUS1; subst.
          inversion TYP3...
          eauto.
          assert (s' = Top).
          inversion IHPREQ; subst.
          inversion TPLUS1. tauto. subst. inversion IN1.
          subst.
          move g1 at top. apply fsuper_vis with
            (pf1 := pf1) (pf2 := pf2) (pf := pf) in H1 as K1. destruct K1 as [K1 K2].
          inversion K1; subst.
          assert (vis = f /\ t0 = Top).
          apply in_isMap with (x := (b1, b2)) (g := g1)...
          destruct H9; subst...
          eauto. 

          
          assert (s3 = Top).
          inversion IHPREQ. subst. inversion TPLUS1; subst.
          tauto. subst. 
          
          remember ((a1, a2, vis, Chan lin out t)
                      :: (b1, b2, vis, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) as gk1.
          assert (EQREM: removeEntry (a1, a2) (removeEntry (b1, b2) gk1) =
                           removeEntry (a1, a2) (removeEntry (b1, b2) g1)).
          rewrite Heqgk1...
          specialize lts_type_remove_lin_out with
            (a1 := a1) (a2 := a2) (t := t) (b1 := b1) (b2 := b2)
            (f := vis) (f1 := vis) (g1 := gk1)
            (s01 := Top) (s := Top) (s1 := Top) (s0 := Top)
            (g0 := g3) (p1 := p1) (p2 := p2)
            (pf0 := nd_pf3) (pf1 := nd_pfw1)
            as LINOUT.
          rewrite <-EQREM.
          assert (Heqk1:
                   k1 =  ((a1, a2, vis, Chan lin empty t)
                            :: (b1, b2, vis, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g3))).
          apply lts_lin_output_action with
            (p := p1) (p' := p2) (nd_pf := nd_pf3) (pol := out) (s := Top).
          eauto. eauto. eauto. inversion TYP3...
          rewrite <-Heqk1 in LINOUT.

          apply LINOUT in LTSOUT as IH.
          eauto.
          eauto.
          eauto.
          inversion TYP3...
          rewrite Heqgk1...
          rewrite Heqgk1...
          rewrite Heqgk1.
          (*  forall x : name * name,
  In x (domain g3) <->
  In x (domain ((a1, a2, vis, Chan lin out t) :: (b1, b2, vis, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1))) *)
           introv;
            erewrite <-sne_premises.in_removeEntry_cons_iff_2, split_domain_l_2...
            eapply split_domain_l_2... 
            eapply typeCheck_no_dup with (g := g3)...
          
          
          rewrite Heqgk1...
          simpl.
          assert (HIDP3: incl (secLabs (dPar p1 q1)) (domain (hid_proj g1)))...
          eapply typeCheck_hid_proj...
          simpl in HIDP3; eapply incl_app_inv in HIDP3 as [_ HIDP3].
          introv IN; simpl.
          assert (IN2:In a (domain (hid_proj  g1))).
          eapply HIDP3 in IN...
          assert (IN2' := IN2).
          eapply in_domain_in_g in IN2' as (ff &tt &IN2');
            repeat erewrite <-hid_proj_removeEntry; 
            try eapply in_g_in_domain, removeEntry_in...
          introv ABS; subst a.
          assert (ABS: flagOf g1 (a1, a2) hid).
          eapply hid_proj_flagOf...
          inv ABS.
          assert (ABS2: vis = hid /\ Chan lin io t = t0)...
          destruct ABS2; try discriminate.
          eapply removeEntry_in...
          introv ABS; subst a.
          assert (ABS: flagOf g1 (b1, b2) hid).
          eapply hid_proj_flagOf...
          eapply fsuper_vis in TSPLIT as [ABS2 _]...
          inv ABS; inv ABS2.
          assert (ABS2: vis = hid /\ t1 = t0)...
          destruct ABS2; try discriminate.
          
          
          remember ((a1, a2, vis, Chan lin inp t)
                      :: (b1, b2, vis, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) as gk1.
          assert (EQREM: removeEntry (a1, a2) (removeEntry (b1, b2) gk1) =
                           removeEntry (a1, a2) (removeEntry (b1, b2) g1)).
          rewrite Heqgk1.
          rewrite removeEntry_swap.
          unfold removeEntry at 2.
          assert (PEQ: pair_eq (a1, a2) (a1, a2) = true)...
          rewrite PEQ.
          unfold removeEntry at 1.
          assert (PEQ2: pair_eq (b1, b2) (b1, b2) = true)...
          rewrite PEQ2...
          eauto.

          assert (K10 : t = Top).
          inversion IHPREQ; subst.
          inversion TPLUS1; subst. 
          inversion TYP3...
          assert (K11: s4 = Top).
          rewrite K10 in TYP3; inversion TYP3; subst; inversion TPLUS1; inversion TPLUS1; subst...
          assert (K12: s3 = Top).
          rewrite K11 in TPLUS1; inversion TPLUS1; subst...

          assert (Heqk4:
                   k4 =  ((a1, a2, vis, Chan lin empty t)
                            :: (b1, b2, vis, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g4))).
          apply lts_lin_input_action with
            (p := q1) (p' := q2) (nd_pf := nd_pf4)
            (pol := inp) (s := s4); subst...
          (*rewrite <-Heqk4 in LININ.*)

          
          rewrite <-EQREM;eapply lts_type_plus_lin_in;
            try rewrite <-Heqk4; subst;
            try eassumption;
            try tauto.
          eauto.
          eauto.
          eauto.
          discriminate.

          (*forall x : name * name,
  In x (domain g4) <->
  In x (domain ((a1, a2, vis, Chan lin inp Top) :: (b1, b2, vis, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)))*)
           introv;
            erewrite <-sne_premises.in_removeEntry_cons_iff_2, split_domain_l_2...
            eapply split_domain_l_2... 
            eapply typeCheck_no_dup with (g := g4)...
          
          
          assert (TC := TCHECK); inv TC; try eapply typeCheck_no_dup with (pf := pf5);
            try assumption; try eapply no_dup_split_no_dup_r with (g := g1)...
          
          simpl.
          assert (HIDP3: incl (secLabs (dPar p1 q1)) (domain (hid_proj g1)))...
          eapply typeCheck_hid_proj...
          simpl in HIDP3; eapply incl_app_inv in HIDP3 as [HIDP3 _].
          introv IN; simpl.
          assert (IN2:In a (domain (hid_proj  g1))).
          eapply HIDP3 in IN...
          assert (IN2' := IN2).
          eapply in_domain_in_g in IN2' as (ff &tt &IN2');
            repeat erewrite <-hid_proj_removeEntry; 
            try eapply in_g_in_domain, removeEntry_in...
          introv ABS; subst a.
          assert (ABS: flagOf g1 (a1, a2) hid).
          eapply hid_proj_flagOf...
          inv ABS.
          assert (ABS2: vis = hid /\ Chan lin io Top = t)...
          destruct ABS2; try discriminate.
          eapply removeEntry_in...
          introv ABS; subst a.
          assert (ABS: flagOf g1 (b1, b2) hid).
          eapply hid_proj_flagOf...
          eapply fsuper_vis in TSPLIT as [ABS2 _]...
          inv ABS; inv ABS2.
          assert (ABS2: vis = hid /\ t0 = t)...
          destruct ABS2; try discriminate.
          
          all:try eassumption.
          eapply sl_pos_par_r...

          unfold is_unrestricted in ABS.
          destruct ABS as [ABS1 ABS2].
          destruct ABS1 as [p0 [t0 ABS1]];inversion ABS1...
          *** eauto.
      * eauto.
      * eauto.    
  - Case lclsL.
    intros.
    remember g3 as gg3; subst g3.
    inversion TCHECK; subst.
    remember pf0 as nd_pf; subst pf0.
    remember pf1 as nd_pf0; subst pf1.
    remember pf2 as nd_pf0'; subst pf2.
    remember pf4 as pf1; subst pf4.
    remember pf3 as pf2; subst pf3.
    remember pf5 as pf3; subst pf5.
    remember pf6 as pf4; subst pf6.

    assert (TSPLIT2 := H4); clear H4.
    
    assert (pfC : isMap ((a1, a2, vis, Chan lin out t) :: (b1, b2, hid, s) :: g0)).
    apply cons_removeEntry_app.
    eauto.
    apply nonRecActions2 in LTS1...

    + apply split_of_split with
        g3 g4 g1 g2 g pf3 pf4 pf1 pf2 pf
        in TSPLIT2 as TSPLIT3.
      destruct TSPLIT3 as [h [pfh TSPLIT3]].
      remember ((a1, a2, vis, Chan lin empty t)
                  :: removeEntry (a1, a2) h) as h1.
      assert (pfh1 : isMap h1).
      rewrite Heqh1. apply cons_removeEntry.
      apply no_dup_split_no_dup_r in TSPLIT3...

      assert (SPLITOUT: tEnv_split
                          g3
                          h1 
                          ((a1, a2, vis, Chan lin out t) :: (b1, b2, hid, s) :: g0)
                          pf3 pfh1 pfC).
      * assert (pf3' : isMap (removeEntry (a1, a2) g3)).
        apply isMap_removeEntry...
        assert (pfh' : isMap (removeEntry (a1, a2) h1)).
        apply isMap_removeEntry...
        assert (pfC' : isMap (
                           removeEntry (a1, a2)
                             (((a1, a2, vis, Chan lin out t)
                                 :: (b1, b2, hid, s)
                                 :: g0)))).
        apply isMap_removeEntry...
        apply SpLin with
          (n := (a1, a2)) (f := vis) (f' := vis) (g := vis)
          (p := out) (q := empty) (p' := out) (t := t)
          (g''' :=  removeEntry (a1, a2)
                      (((a1, a2, vis, Chan lin out t)
                          :: (b1, b2, hid, s)
                          :: g0)))
          (pf' := pf3')  (pf'' := pfh')  (pf''' := pfC').
        ** eauto.
        ** eauto.

           
        (* tEnv_split g3 g4 g1 pf3 pf4 pf1 *)
        (*  tEnv_split g3 h g pf3 pfh pf *)
        (* GOAL : In (a1, a2, vis, Chan lin out t) g3 *)
           
        ** specialize typeCheck_lts_out with
             g3
             ((a1, a2, vis, Chan lin out t) :: (b1, b2, hid, s) :: g0)
             pf3 p1  a1 a2 b1 b2
             ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, s1) :: g0)
             p2 nd_pf0 as TOUT.
           apply TOUT in H5 as TYP.
           destruct TYP as [m1 [t1 [TYP | TYP]]].
           apply tsuper_payload with
             g3 h g pf3 pfh pf a1 a2 vis lin io t
             in H0 as K0.
           destruct K0 as [pol2 TYP2].
           inversion TYP; inversion TYP2; subst.
           apply fsuper_vis with
             g3 h g pf3 pfh pf (a1, a2)  (Chan lin io t)
             in H0. inversion H0; inversion H3; subst. 
           assert (f = f0 /\ Chan m1 out t1 =  Chan lin pol2 t).
           apply in_isMap with (x := (a1, a2)) (g := g3)...
           inversion H9.  inversion H11; subst. 
           assert (f0 = vis /\ Chan lin out t = t0).
           apply in_isMap with (x := (a1, a2)) (g := g3)...
           inversion H10. subst...
           eauto. eauto.
           
           (* ABSURD: typeOf g3 (a1, a2) (Chan m1 io t1) *)
           specialize typeCheck_lts_in with
             g4
             ((a1, a2, vis, Chan lin inp t) :: (b1, b2, ill, s1) :: g0)
             pf4 q1  a1 a2 b1 b2
             ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, s) :: g0)
             q2 nd_pf0' as TIN.
           apply TIN in H6 as TYP2.
           destruct TYP2 as [m2 [t2 [TYP2 | TYP2]]].
           inversion TYP; inversion TYP2; subst.
           apply tsuper_payload with
             g3 h g pf3 pfh pf a1 a2 vis lin io t
             in H0 as K0.
           destruct K0 as [pol2 TYP3].
           inversion TYP3; subst.
           assert (f = f1 /\ Chan m1 io t1 =  Chan lin pol2 t).
           apply in_isMap with (x := (a1, a2)) (g := g3)...
           inversion H4. inversion H9; subst.
           apply tsub_io with
             g3 g4 g1 pf3 pf4 pf1 a1 a2 f1 lin t
             in H2 as K2. inversion K2; subst. 
           assert (ABS: pol_plus io inp io). 
           apply split_plus_lin with
             g3 g4 g1 pf3 pf4 pf1 a1 a2 t f1 f0 f.
           eauto.
           apply tsuper_payload_r with
             g3 g4 g1 pf3 pf4 pf1 a1 a2 f lin io t
             in H7 as K7. destruct K7 as [pol3 K7]; inversion K7; subst.
           assert (f0 =f2 /\  Chan m2 inp t2 = Chan lin pol3 t).
           apply in_isMap with (x := (a1, a2)) (g := g4)...
           inversion H11. inversion H13; subst...
           eauto. eauto. eauto. inversion ABS...
           eauto. eauto.

           inversion TYP; inversion TYP2; subst.
           apply tsuper_payload with
             g1 g2 g pf1 pf2 pf a1 a2 vis lin io t
             in H0 as K0.
           destruct K0 as [pol3 K0]; inversion K0; subst.
           apply tsuper_payload with
             g3 g4 g1 pf3 pf4 pf1 a1 a2 f1 lin pol3 t
             in H3 as K3.
           destruct K3 as [pol4 K3]; inversion K3; subst.
           assert (f = f2 /\ Chan m1 io t1 = Chan lin pol4 t).
           apply in_isMap with (x := (a1, a2)) (g := g3)...
           inversion H7. inversion H10; subst.
           assert (ABS: pol_plus io io io). 
           apply split_plus_lin with
             g3 g4 g1 pf3 pf4 pf1 a1 a2 t f2 f0 f1.
           eauto.
           apply tsuper_payload_r with
             g3 g4 g1 pf3 pf4 pf1 a1 a2 f1 lin pol3 t
             in H3 as K4.
           destruct K4 as [pol4 K4]; inversion K4; subst.
           assert (f0 = f /\ Chan m2 io t2 = Chan lin pol4 t).
           apply in_isMap with (x := (a1, a2)) (g := g4)...
           inversion H11.  inversion H13; subst...
           
           eauto.
           apply tsub_io with
             g3 g4 g1 pf3 pf4 pf1 a1 a2 f2 lin t
             in H2 as K2. inversion K2; subst.
           assert (f1 = f /\ Chan lin pol3 t = Chan lin io t).
           apply in_isMap with (x := (a1, a2)) (g := g1)...
           inversion H11. subst...
           eauto. 
           eauto.
           inversion ABS. 
           all:try eassumption.

        ** rewrite Heqh1...
        ** (* tEnv_split g3 h g pf3 pfh pf *)
          (* GOAL : tEnv_split (removeEntry (a1, a2) g3) (removeEntry (a1, a2) h1)
    (removeEntry (a1, a2) ((a1, a2, vis, Chan lin out t) :: (b1, b2, hid, s) :: g0)) pf3'
    pfh' pfC' *)
          revert dependent pf3'.
          revert dependent pfh'.
          revert dependent pfC'.
          rewrite Heqh1.
          subst g0.
          unfold removeEntry; assert (PEQ: pair_eq (a1,a2) (a1,a2)=true) by apply pairEq_eq_true.  rewrite PEQ.
          fold removeEntry.
          assert (SHIFT: ((b1, b2, hid, s) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)) = removeEntry (a1, a2) ((b1, b2, hid, s) :: (removeEntry (b1, b2) g))).
          apply removeEntry_shift.
          apply nonRecActions2 in LTS1...
          rewrite SHIFT.
          intros.
          clear IHLTS1 IHLTS2.
          assert (nd_pfD: NoDup (domain ((b1, b2, hid, s) :: removeEntry (b1, b2) g))).
          apply no_dup_cons_removeEntry.
          apply no_dup_split_no_dup with
            g1 g2 pf1 pf2 pf...
          apply no_dup_isMap in nd_pfD as pfD.
          apply split_remove with
            (pf1 := pf3) (pf2 := pfh) (pf3 := pfD).
          apply no_dup_split_no_dup_l with h g pf3 pfh pf...
          apply no_dup_split_no_dup_r with g3 g pf3 pfh pf...
          eauto. eauto.
        ** tauto. 
        ** eauto.
        ** eauto.
      * apply no_dup_split_no_dup_l in TSPLIT3 as nd_pf3.
        specialize IHLTS1 with (pf1 := pf3) (pf2 := pfh1) (pf := pfC) (nd_pf1 := nd_pf3).
        apply IHLTS1 in SPLITOUT.
        destruct SPLITOUT as [k1 LTSOUT].

        apply split_comm in TSPLIT2 as TSPLIT4. 
        apply split_of_split with
          g4 g3 g1 g2 g pf4 pf3 pf1 pf2 pf
          in TSPLIT4 as TSPLIT5.
        destruct TSPLIT5 as [w [pfw TSPLIT5]].
        (* TSPLIT5 : tEnv_split g4 w g pf4 pfw pf *)
        remember ((a1, a2, vis, Chan lin empty t) :: removeEntry (a1, a2) w) as w1.
        assert (pfw1 : isMap w1).
        rewrite Heqw1. apply cons_removeEntry.
        apply no_dup_split_no_dup_r in TSPLIT5...
        apply no_dup_isMap in  nd_pf0' as pfD.

        specialize IHLTS2 with (pf1 := pf4).
        
        
        assert (T3b : exists s3,
                   In (b1, b2, hid, s3) g3).
        assert (flagOf g3 (b1, b2) vis \/
                  flagOf g3 (b1, b2) hid).
        apply typeCheck_lts_out_payload with
          (g := ((a1, a2, vis, Chan lin out t) :: (b1, b2, hid, s) :: g0)) (pf1 := pf3) (p := p1) (a1 := a1) (a2 := a2)
          (g' := ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, s1) :: g0)) (p' := p2) (nd_pf := nd_pf0)...
        inversion H2.
        specialize flag_of_split_l with g3 h g pf3 pfh pf (b1, b2) as FSL. intuition.
        assert (vis = hid). apply flag_of_map with (g := g) (x := (b1,b2))... inversion H8.
        inversion H4; subst.
        eauto. inversion H3; subst.
        exists t0...
        
        
        destruct T3b as [s3 T3b].
        
        apply tsuper_payload with
          (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as K0.
        destruct K0 as [q' TYP']; inversion TYP'; subst.
        apply tsuper_payload with
          (pf1 := pf3) (pf2 := pf4) (pf := pf1) in H2 as K2.
        destruct K2 as [q'' TYP2]; inversion TYP2; subst.
        assert (LEM1:
                 exists r3,
                   type_remove s3 t r3)...
        assert (T4b : exists s4,
                   In (b1, b2, ill, s4) g4).
        specialize flag_of_split_l with g3 g4 g1 pf3 pf4 pf1 (b1, b2) as FSL. intuition.
        assert (F3: flagOf g3 (b1, b2) hid ).
        apply F_Entry in T3b...
        apply H7 in F3. destruct F3 as [ILL  UNUSED].
        inversion ILL.
        exists t0...
        
        destruct T4b as [s4 T4b].
        
        assert (TYPw : exists sw, In ((b1, b2), hid, sw) w /\
                                    type_plus s4 sw s).
        specialize split_type_plus with
          g4 w g pf4 pfw pf (b1, b2) s4 s as TP1.
        assert (TYP4: typeOf g4 (b1, b2) s4)...
        apply TP1 in TYP4. clear TP1.
        destruct TYP4 as [t2 [INw TP4]].

        inversion INw; subst.
        exists t2.
        specialize split_flag_plus with
          g4 w g pf4 pfw pf (b1, b2) ill hid as FYP.
        apply F_Entry in T4b as K4.
        apply FYP in K4. clear FYP.
        destruct K4 as [fw [INw' TPw]].
        inversion TPw; subst. inversion INw'. subst.
        assert (hid = f1 /\ t0 = t2).
        apply in_isMap with (x := (b1, b2)) (g := w)...
        destruct H8; subst...
        eauto. eauto. eauto. eauto. 
        destruct TYPw as [sw [TYPw TPw]].
        
        assert (nd_pf4 : NoDup(domain g4)).
        apply no_dup_split_no_dup_l with
          (pf1 := pf4) (pf2 := pfw) (pf := pf)
          in nd_pf as nd_pf4...
        specialize split_type_plus_r with
          g4 g3 g1 pf4 pf3 pf1 (b1, b2) s4 s3 as TP1...
        assert (TYP4: typeOf g4 (b1, b2) s4)...
        apply TP1 in TYP4. clear TP1.
        destruct TYP4 as [s' [IN1 TPLUS1]].
        assert (TYP3: type_sub t s3).
        destruct LEM1 as [r3 TREM].
        assert (TREM2 := TREM); inversion TREM2...
        assert (TYP1 : type_sub s' s)...
        
        assert (IHPREQ : exists r2, type_plus s4 r2 s1).
        apply type_plus_exists with
          (s := s) (t := t) (s3 := s3) (s' := s')...
        destruct IHPREQ as [r2 IHPREQ].
        remember ((a1, a2, vis, Chan lin empty t)
                    :: (b1, b2, ill, r2)
                    :: removeEntry (a1, a2) (removeEntry (b1, b2) w)) as w2. 
        assert (pfw2 : isMap w2). rewrite Heqw2. 
        apply cons_removeEntry_app;
          try eapply no_dup_split_no_dup_r in nd_pf...
        remember ((a1, a2, vis, Chan lin empty t)
                    :: (b1, b2, ill, s4)
                    :: removeEntry (a1, a2) (removeEntry (b1, b2) w)) as w3. 
        assert (pfw3 : isMap w3). rewrite Heqw3. 
        apply cons_removeEntry_app;
          try eapply no_dup_split_no_dup_r in nd_pf...
        assert (pf0' :
                 isMap ((a1, a2, vis, Chan lin inp t) :: (b1, b2, ill, s1) :: g0)).
        apply cons_removeEntry_app...
        assert (IHTSPLIT:
                 (~is_unrestricted r2 /\ tEnv_split g4 w2 ((a1, a2, vis, Chan lin inp t) :: (b1, b2, ill, s1) :: g0) pf4 pfw2 pf0') \/ 
                   (is_unrestricted r2 /\ tEnv_split g4 w3 ((a1, a2, vis, Chan lin inp t) :: (b1, b2, ill, s1) :: g0) pf4 pfw3 pf0')).
        destruct s1. inversion IHPREQ. subst.
        assert (pf' : isMap (removeEntry (b1, b2) g4)).
        apply isMap_removeEntry...
        assert (pf'' : isMap (removeEntry (b1, b2) ((a1, a2, vis, Chan lin empty t)
                                                      :: (b1, b2, ill, Chan lin p3 s1) :: removeEntry (a1, a2) (removeEntry (b1, b2) w)))).
        apply isMap_removeEntry...
        assert (pf''' : isMap (removeEntry (b1, b2) ((a1, a2, vis, Chan lin inp t) :: (b1, b2, ill, Chan lin p s1) :: g0))).
        apply isMap_removeEntry...

        left.
        split. unfold is_unrestricted. intro ABS.
        destruct ABS as [p9 [t9 ABS]]; inversion ABS.
        apply SpLin with
          (n := (b1, b2)) (f := ill) (g := ill) (f' := ill)
          (p := p0) (q := p3) (p' := p) (t := s1)
          (pf' := pf') (pf'' := pf'') (pf''' := pf''').
        eauto. eauto. eauto. eauto.
        
        apply split_remove with
          (pf1 :=  pf4) (pf2 := pfw2) (pf3 := pf0').
        eauto.
        apply no_dup_cons_removeEntry_app;
          try eapply no_dup_split_no_dup_r in nd_pf...
        subst g0.   apply no_dup_cons_removeEntry_app...
        apply split_new_lin_lin with
          (pf1 := pf4) (pf2 := pfw) (pf := pf)
          (f1 := vis) (p1 := inp) (h1 := ill) (q1 := p0).
        eauto. eauto. 
        specialize typeCheck_lts_in with
          g4 ((a1, a2, vis, Chan lin inp t) :: (b1, b2, ill, Chan lin p s1) :: g0) pf4 q1 a1 a2 b1 b2
          ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, s) :: g0) q2 nd_pf0' as TYP1a.
        apply TYP1a in H6 as TYP1a'.
        clear TYP1a.
        destruct TYP1a' as [m [u TYP1a']].
        specialize typeCheck_lts_out with
          g3 ((a1, a2, vis, Chan lin out t) :: (b1, b2, hid, s) :: g0) pf3 p1 a1 a2 b1 b2
          ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, Chan lin p s1) :: g0) p2 nd_pf0 as TYP2a.
        apply TYP2a in H5 as TYP2a'.
        clear TYP2a.
        destruct TYP2a' as [m' [u' TYP2a']].
        assert (In (a1, a2, vis, Chan lin inp t) g4 /\
                  In (a1, a2, vis, Chan lin out t) g3).
        apply split_lin_capab with
          (pf1 := pf4) (pf2 := pf3) (pf := pf1)
          (m1 := m) (m2 := m') (t1 := u) (t2 := u') (p := q').
        eauto. eauto. inversion TYP'. subst.
        move g1 at top.
        apply fsuper_vis
          with (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as [K1 K2].
        inversion K1; subst. 
        assert (vis = f1 /\ t0 =  Chan lin q' t).
        apply in_isMap with (x := (a1, a2)) (g := g1)...
        destruct H7; inversion H8; subst...
        eauto. eauto. destruct H4... 
        all:try eassumption; try tauto.
        eauto.
        eauto.
        eauto.
        eapply nonRecActions2...
        eauto.
        eauto.
        
        right. split. unfold is_unrestricted.
        exists p3. exists s1...
        assert (ISUNS: is_unrestricted s).
        subst.  inversion TPLUS1. subst. inversion TYP1...
        subst. 
        inversion H. destruct H7 as [TPS ISUN].
        apply ISUN in ISUNS as ISUN2. subst s. clear ISUN.
        apply tsuper_payload with
          (pf1 := pf1) (pf2 := pf2) (pf := pf) in H1 as K1.
        apply tsuper_payload_r with
          (pf1 := pf1) (pf2 := pf2) (pf := pf) in H1 as K2.
        destruct K1 as [pol1 TB1]. destruct K2 as [pol2 TB2].
        inversion TB1. inversion TB2. subst.
        assert (pol1 = pol2 /\ pol2 = (pol_cup p0 p3)).
        apply split_plus_un with
          (pf1 := pf1) (pf2 := pf2) (pf3 := pf)
          (b1 := b1) (b2 := b2) (t := s1)
          (f1 := f1) (f2 := f2) (f3 := hid)...
        destruct H8; subst.
        apply tsuper_payload_r with
          (pf1 := pf4) (pf2 := pf3) (pf := pf1) in H7 as K7.
        destruct K7 as [pol7 TB3]. inversion TB3; subst. 
        assert (p0 = pol7 /\ pol7 = (pol_cup p0 p3)).
        apply split_plus_un with
          (pf1 := pf4) (pf2 := pf3) (pf3 := pf1)
          (b1 := b1) (b2 := b2) (t := s1)
          (f1 := ill) (f2 := f3) (f3 := f1).
        all:try eassumption. 
        destruct H9. assert (POLEQ: p0 = pol_cup p0 p3).
        transitivity pol7...
        revert dependent pf0'.
        rewrite <-POLEQ.
        intros.
        assert (pf' : isMap (removeEntry (b1, b2) g4)).
        apply isMap_removeEntry...
        assert (pf'' : isMap (removeEntry (b1, b2) ((a1, a2, vis, Chan lin empty t)
                                                      :: (b1, b2, ill, Chan un p0 s1) :: removeEntry (a1, a2) (removeEntry (b1, b2) w)))).
        apply isMap_removeEntry...
        assert (pf''' : isMap (removeEntry (b1, b2) ((a1, a2, vis, Chan lin inp t) :: (b1, b2, ill, Chan un p0 s1) :: g0))).
        apply isMap_removeEntry...
        apply SpUn with
          (n := (b1, b2)) (f := ill) (g := ill) (f' := ill)
          (p := p0) (t := s1)
          (pf' := pf') (pf'' := pf'') (pf''' := pf''').
        all:try eassumption.
        eauto.
        eauto.
        
        (*tEnv_split (removeEntry (b1, b2) g4)
    (removeEntry (b1, b2)
       ((a1, a2, vis, Chan lin empty t)
        :: (b1, b2, ill, Chan un p0 s1) :: removeEntry (a1, a2) (removeEntry (b1, b2) w)))
    (removeEntry (b1, b2)
       ((a1, a2, vis, Chan lin inp t) :: (b1, b2, ill, Chan un p0 s1) :: g0)) pf' pf'' pf'''*)
        assert (pf0'' : isMap
                          (((a1, a2, vis, Chan lin inp t) :: (b1, b2, ill, Chan un p0 s1) :: g0))).
        subst g0...
        apply split_remove with
          (pf1 :=  pf4) (pf2 := pfw3) (pf3 := pf0'').
        eauto.
        apply no_dup_cons_removeEntry_app;
          try eapply no_dup_split_no_dup_r in nd_pf...
        eauto. 
        (*tEnv_split g4
    ((a1, a2, vis, Chan lin empty t)
     :: (b1, b2, ill, Chan un p0 s1) :: removeEntry (a1, a2) (removeEntry (b1, b2) w))
    ((a1, a2, vis, Chan lin inp t) :: (b1, b2, ill, Chan un p0 s1) :: g0) pf4 pfw3 pf0''*)
        apply split_new_lin_un with
          (pf1 := pf4) (pf2 := pfw) (pf := pf)
          (f1 := vis) (p1 := inp) (h1 := ill) (q := p0).
        eauto. eauto.
        specialize typeCheck_lts_in with
          g4 ((a1, a2, vis, Chan lin inp t) :: (b1, b2, ill, Chan un (pol_cup p0 p3) s1) :: g0) pf4 q1 a1 a2 b1 b2
          ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, Chan un (pol_cup p0 p3) s1) :: g0) q2 nd_pf0' as TYP1a.
        apply TYP1a in H6 as TYP1a'.
        clear TYP1a.
        destruct TYP1a' as [m [u TYP1a']].
        specialize typeCheck_lts_out with
          g3  ((a1, a2, vis, Chan lin out t)
                 :: (b1, b2, hid, Chan un (pol_cup p0 p3) s1) :: g0) pf3 p1 a1 a2 b1 b2
          ((a1, a2, vis, Chan lin empty t)
             :: (b1, b2, vis, Chan un (pol_cup p0 p3) s1) :: g0) p2 nd_pf0 as TYP2a.
        apply TYP2a in H5 as TYP2a'.
        clear TYP2a.
        destruct TYP2a' as [m' [u' TYP2a']].
        assert (In (a1, a2, vis, Chan lin inp t) g4 /\
                  In (a1, a2, vis, Chan lin out t) g3).
        apply split_lin_capab with
          (pf1 := pf4) (pf2 := pf3) (pf := pf1)
          (m1 := m) (m2 := m') (t1 := u) (t2 := u') (p := q').
        eauto. eauto. inversion TYP'. subst.
        move g1 at top.
        apply fsuper_vis
          with (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as [K1 K2].
        inversion K1; subst. 
        assert (vis = f4 /\ t0 =  Chan lin q' t).
        apply in_isMap with (x := (a1, a2)) (g := g1)...
        destruct H9; inversion H10; subst...
        eauto. eauto. 
        destruct H12 as [CAP1 CAP2]...

        all:try eassumption; try tauto.
        eauto.
        eauto.
        eauto.
        eapply nonRecActions2...
        eauto.
        eauto.
        
        left. split. 
        unfold is_unrestricted. intro ABS.
        inversion IHPREQ; subst. 
        destruct ABS as [p9 [t9 ABS]]; inversion ABS.
        inversion IHPREQ; subst.
        assert (pf' : isMap (removeEntry (b1, b2) g4)).
        apply isMap_removeEntry...
        assert (pf'' : isMap (removeEntry (b1, b2) ((a1, a2, vis, Chan lin empty t)
                                                      :: (b1, b2, ill, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) w)))).
        apply isMap_removeEntry...
        assert (pf''' : isMap (removeEntry (b1, b2) ((a1, a2, vis, Chan lin inp t) :: (b1, b2, ill, Top) :: g0))).
        apply isMap_removeEntry...
        apply SpTop with
          (n := (b1, b2)) (f := ill) (g := ill) (f' := ill)
          
          (pf' := pf') (pf'' := pf'') (pf''' := pf''').
        all:try eassumption.
        eauto.
        eauto.
        
        (*tEnv_split (removeEntry (b1, b2) g4)
    (removeEntry (b1, b2)
       ((a1, a2, vis, Chan lin empty t)
        :: (b1, b2, ill, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) w)))
    (removeEntry (b1, b2) ((a1, a2, vis, Chan lin inp t) :: (b1, b2, ill, Top) :: g0)) pf'
    pf'' pf''*)
        assert (pf0'' : isMap
                          (((a1, a2, vis, Chan lin inp t) :: (b1, b2, ill, Top) :: g0))).
        subst g0...
        apply split_remove with
          (pf1 :=  pf4) (pf2 := pfw3) (pf3 := pf0'').
        eauto.
        apply no_dup_cons_removeEntry_app;
          try eapply no_dup_split_no_dup_r in nd_pf...
        subst g0.  apply no_dup_cons_removeEntry_app...
        apply split_new_lin_top with
          (pf1 := pf4) (pf2 := pfw) (pf := pf)
          (f1 := vis) (p1 := inp) (h1 := ill).
        eauto. eauto.
        specialize typeCheck_lts_in with
          g4 ((a1, a2, vis, Chan lin inp t) :: (b1, b2, ill, Top) :: g0) pf4 q1 a1 a2 b1 b2
          ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, s) :: g0) q2 nd_pf0' as TYP1a.
        apply TYP1a in H6 as TYP1a'.
        clear TYP1a.
        destruct TYP1a' as [m [u TYP1a']].
        specialize typeCheck_lts_out with
          g3  ((a1, a2, vis, Chan lin out t)
                 :: (b1, b2, hid, s) :: g0) pf3 p1 a1 a2 b1 b2
          ((a1, a2, vis, Chan lin empty t)
             :: (b1, b2, vis, Top) :: g0) p2 nd_pf0 as TYP2a.
        apply TYP2a in H5 as TYP2a'.
        clear TYP2a.
        destruct TYP2a' as [m' [u' TYP2a']].
        assert (In (a1, a2, vis, Chan lin inp t) g4 /\
                  In (a1, a2, vis, Chan lin out t) g3).
        apply split_lin_capab with
          (pf1 := pf4) (pf2 := pf3) (pf := pf1)
          (m1 := m) (m2 := m') (t1 := u) (t2 := u') (p := q').
        eauto. eauto. inversion TYP'. subst.
        move g1 at top.
        apply fsuper_vis
          with (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as [K1 K2].
        inversion K1; subst. 
        assert (vis = f1 /\ t0 =  Chan lin q' t).
        apply in_isMap with (x := (a1, a2)) (g := g1)...
        destruct H7; inversion H8; subst...
        eauto. eauto. 
        destruct H4 as [CAP1 CAP2]...

        all:try eassumption; try tauto.
        eauto.
        eauto.
        eauto.
        eapply nonRecActions2...
        eauto.
        eauto.
        
        destruct r2.
        ***
          destruct m.
          (*  ~ is_unrestricted (Chan lin p r2) *)
          ****
            assert (G4IN: exists (m : mode) (t : piType),
                       typeOf g4 (a1, a2) (Chan m inp t) \/ typeOf g4 (a1, a2) (Chan m io t)).
            apply typeCheck_lts_in with
              ((a1, a2, vis, Chan lin inp t) :: (b1, b2, ill, s1) :: g0) pf4 q1 b1 b2
              ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, s) :: g0) q2 nd_pf0'...
            destruct G4IN as [m4 [t4 TYP4]].
            assert (G4OUT: exists (m : mode) (t : piType),
                       typeOf g3 (a1, a2) (Chan m out t) \/ typeOf g3 (a1, a2) (Chan m io t)).
            apply typeCheck_lts_out with
              ((a1, a2, vis, Chan lin out t) :: (b1, b2, hid, s) :: g0) pf3 p1 b1 b2
              ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, s1) :: g0) p2 nd_pf0...
            destruct G4OUT as [m4' [t4' TYP4']].
            move g1 at top. apply fsuper_vis with
              (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as K0. destruct K0 as [K1 K2].
            inversion K1; subst.
            assert (vis = f /\ t0 = Chan lin q' t).
            apply in_isMap with (x := (a1, a2)) (g := g1)...
            destruct H7; subst.
            assert (CAP: In (a1, a2, vis, Chan lin inp t) g4 /\
                           In (a1, a2, vis, Chan lin out t) g3).
            
            apply split_lin_capab with
              (pf1 := pf4) (pf2 := pf3) (pf := pf1)
              (m1 := m4) (m2 := m4') (t1 := t4) (t2 := t4')
              (p := q')...
            destruct CAP as [CAP1 CAP2]...
            assert (TP4 : exists t2 : piType, typeOf g1 (a1, a2) t2 /\ type_plus ( Chan lin inp t) ( Chan lin out t) t2).
            apply split_type_plus_r with
              (pf1 := pf4) (pf2 := pf3) (pf := pf1)...
            destruct TP4 as [u1 [TYPa1 TPP]].
            inversion TPP; subst. inversion H11; subst.
            inversion TYPa1; subst.
            assert (f = vis /\ Chan lin io t = Chan lin q' t).
            apply in_isMap with (x := (a1, a2)) (g := g1)...
            destruct H8; subst. assert (CAP3 := H7).
            clear H7 H9 K1 K2.
            
            destruct IHTSPLIT as
              [[NOTUN IHTSPLIT] | ABS].
            specialize IHLTS2 with
              (nd_pf1 := nd_pf4) (pf2 := pfw2) (pf := pf0').
            
            apply IHLTS2 in IHTSPLIT.
            destruct IHTSPLIT as [k4 LTSIN].
            
            assert (LEM2:
                     exists r4,
                       type_plus s4 t r4).
            apply plus_sub_exists with
              (s := s3) (r := s')...
            
            destruct LEM1 as [r3 TREM].
            destruct LEM2 as [r4 TPLUS].

            specialize split_exists_remove_l with
              g3 g4 g1 pf3 pf4 pf1 b1 b2 hid t s3 r3 as EXREM.
            apply EXREM in T3b as TYP3'.
            destruct TYP3' as [s'' [r'' [TYP1' TREM1]]].

            assert(nd_pfw1 :
                    NoDup(domain
                            ((a1, a2, vis, Chan lin out t)
                               :: (b1, b2, hid, s'')
                               :: removeEntry (a1, a2)
                               (removeEntry (b1, b2) g1)))).
            apply no_dup_cons_removeEntry_app...
            assert (nd_pfw2 :
                     NoDup(domain
                             ((a1, a2, vis, Chan lin inp t)
                                :: (b1, b2, ill, r'')
                                :: removeEntry (a1, a2)
                                (removeEntry (b1, b2) g1)))).
            apply no_dup_cons_removeEntry_app...
            
            exists (((a1, a2), vis, Chan lin empty t)
                      :: ((b1, b2), hid, s'')
                      :: removeEntry (a1, a2)
                      (removeEntry (b1, b2) g1)).
            apply lclsL with
              (s1 := r'') (pf1 := nd_pfw1) (pf2 := nd_pfw2).
            eauto.
            eauto.
            
            inversion TYP1'; subst.
            apply fsub_hid with (pf1 := pf3) (pf2 := pf4) (pf := pf1) in T3b as FYP. inversion FYP; subst. 
            assert (hid = f /\ t0 = s'').
            apply in_isMap with (x := (b1, b2)) (g := g1)...
            destruct H9; subst...
            eauto.
            

            remember ((a1, a2, vis, Chan lin out t)
                        :: (b1, b2, hid, s'') :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) as gk1.
            assert (EQREM: removeEntry (a1, a2) (removeEntry (b1, b2) gk1) =
                             removeEntry (a1, a2) (removeEntry (b1, b2) g1)).
            rewrite Heqgk1.
            rewrite removeEntry_swap.
            unfold removeEntry at 2.
            assert (PEQ: pair_eq (a1, a2) (a1, a2) = true)...
            rewrite PEQ.
            unfold removeEntry at 1.
            assert (PEQ2: pair_eq (b1, b2) (b1, b2) = true)...
            rewrite PEQ2...
            eauto.
            specialize lts_type_remove_lin_out with
              (a1 := a1) (a2 := a2) (t := t) (b1 := b1) (b2 := b2)
              (f := hid) (f1 := vis) (g1 := gk1)
              (s01 := r'') (s := s3) (s1 := r3) (s0 := s'')
              (g0 := g3) (p1 := p1) (p2 := p2)
              (pf0 := nd_pf3) (pf1 := nd_pfw1)
              as LINOUT.
            rewrite <-EQREM.
            assert (Heqk1:
                     k1 =  ((a1, a2, vis, Chan lin empty t)
                              :: (b1, b2, vis, r3) :: removeEntry (a1, a2) (removeEntry (b1, b2) g3))).

            apply lts_lin_output_action with
              (p := p1) (p' := p2) (nd_pf := nd_pf3)
              (pol := out) (s := s3)...
            
            rewrite <-Heqk1 in LINOUT.

            apply LINOUT in LTSOUT as IH.
            eauto.
            eauto.
            eauto.
            eauto.
            rewrite Heqgk1...
            rewrite Heqgk1...
            rewrite Heqgk1.
            (*forall x : name * name,
  In x (domain g3) <->
  In x (domain ((a1, a2, vis, Chan lin out t) :: (b1, b2, hid, s'') :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)))*)
             introv;
            erewrite <-sne_premises.in_removeEntry_cons_iff_2, split_domain_l_2...
            eapply split_domain_l_2... 
            eapply typeCheck_no_dup with (g := g3)...
            
            subst gk1. simpl.
            assert (HIDP3: incl (secLabs p1) (domain (hid_proj g3))).
            eapply typeCheck_hid_proj...
            assert (HIDP1: incl (domain (hid_proj g3)) (domain (hid_proj g1))).
            eapply split_incl_hid_proj...
            assert (HID: incl(secLabs p1)  (domain (hid_proj g1))).
            eapply incl_tran...
            introv IN; try eapply HID in IN.
            case_eq (pair_eq a (b1, b2));
              introv PEQ; try rewrite <-pairEq_eq in PEQ; try subst a.
            left...
            right.
            assert (IN' :=IN). eapply in_domain_in_g in IN' as (ff &tt &IN').
            repeat erewrite <-hid_proj_removeEntry; 
              try eapply in_g_in_domain, removeEntry_in...
            introv ABS; subst a.
            assert (ABS: flagOf g1 (a1, a2) hid).
            eapply hid_proj_flagOf...
            inv ABS.
            assert (ABS2: vis = hid /\ Chan lin io t = t0)...
            destruct ABS2; try discriminate.
            eapply removeEntry_in...
            eapply pairEq_neq...

            all:try eassumption.

            
            
            (* as above by using lts_lin_input_action *)
            remember ((a1, a2, vis, Chan lin inp t)
                        :: (b1, b2, ill, r'') :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) as gk1.
            assert (EQREM: removeEntry (a1, a2) (removeEntry (b1, b2) gk1) =
                             removeEntry (a1, a2) (removeEntry (b1, b2) g1)).
            rewrite Heqgk1.
            rewrite removeEntry_swap.
            unfold removeEntry at 2.
            assert (PEQ: pair_eq (a1, a2) (a1, a2) = true)...
            rewrite PEQ.
            unfold removeEntry at 1.
            assert (PEQ2: pair_eq (b1, b2) (b1, b2) = true)...
            rewrite PEQ2...
            eauto.

            rewrite <-EQREM.
            assert (Heqk4:
                     k4 =  ((a1, a2, vis, Chan lin empty t)
                              :: (b1, b2, vis, r4) :: removeEntry (a1, a2) (removeEntry (b1, b2) g4))).
            apply lts_lin_input_action with
              (p := q1) (p' := q2) (nd_pf := nd_pf4)
              (pol := inp) (s := s4)...
            (*rewrite <-Heqk4 in LININ.*)

            
            eapply lts_type_plus_lin_in;
              try rewrite <-Heqk4; subst gk1;
              try eassumption;
              try tauto.
            eauto.
            eauto.
            
            inverts TREM1 as [TP _]; eapply type_plus_comm...
            discriminate.

            (*forall x : name * name,
  In x (domain g4) <->
  In x (domain ((a1, a2, vis, Chan lin inp t) :: (b1, b2, ill, r'') :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)))*)
             introv;
            erewrite <-sne_premises.in_removeEntry_cons_iff_2, split_domain_l_2...
            eapply split_domain_l_2... 
            eapply typeCheck_no_dup with (g := g4)...

            assert (TC := TCHECK);
             inv TC; try eapply typeCheck_no_dup with (pf := pf5);
              try assumption; try eapply no_dup_split_no_dup_r with (g := g1)...
            
            simpl.
            assert (IN: In (b1, b2) (fn p1) \/ In (b1, b2) (secLabs p1)).
            eapply payload_occurs...
            destruct IN as [ABS | INSL].
            eapply tc_dep_relabel_premises.typeCheck_is_vis in H5 as (tt& ABS2)...
            assert (ABS3: hid = vis /\ s3 = tt)...
            destruct ABS3; try discriminate.
            assert (NIN: ~In (b1, b2) (secLabs q1)).
            intros ABS.
            assert (ND: NoDup (secLabs  (dPar p1 q1))).
            eapply typeCheck_no_dup with (pf := pf1)...
            simpl in ND; eapply no_dup_iff in ND as (ND1 &ND2 &DIS).
            eapply disjoint_absurd...
            assert (HIDP3: incl (secLabs (dPar p1 q1)) (domain (hid_proj g1)))...
            eapply typeCheck_hid_proj...
            simpl in HIDP3; eapply incl_app_inv in HIDP3 as [HIDP3 _].
            introv IN; simpl.
            assert (IN2:In a (domain (hid_proj  g1))).
            eapply HIDP3 in IN...
            assert (IN2' := IN2).
            eapply in_domain_in_g in IN2' as (ff &tt &IN2');
              repeat erewrite <-hid_proj_removeEntry; 
              try eapply in_g_in_domain, removeEntry_in...
            introv ABS; subst a.
            assert (ABS: flagOf g1 (a1, a2) hid).
            eapply hid_proj_flagOf...
            inv ABS.
            assert (ABS2: vis = hid /\ Chan lin io t = t0)...
            destruct ABS2; try discriminate.

            eapply removeEntry_in...
            introv ABS; subst a; try contradiction.

            eapply sl_pos_par_r...
            
            unfold is_unrestricted in ABS.
            destruct ABS as [ABS1 ABS2].
            destruct ABS1 as [p0 [t0 ABS1]];inversion ABS1...
          ****
            destruct IHTSPLIT as
              [[ABS UNUSED] | [UN IHTSPLIT]].
            unfold is_unrestricted in ABS.
            elim ABS. exists p. exists r2...
            
            assert (G4IN: exists (m : mode) (t : piType),
                       typeOf g4 (a1, a2) (Chan m inp t) \/ typeOf g4 (a1, a2) (Chan m io t)).
            apply typeCheck_lts_in with
              ((a1, a2, vis, Chan lin inp t) :: (b1, b2, ill, s1) :: g0) pf4 q1 b1 b2
              ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, s) :: g0) q2 nd_pf0'...
            destruct G4IN as [m4 [t4 TYP4]].
            assert (G4OUT: exists (m : mode) (t : piType),
                       typeOf g3 (a1, a2) (Chan m out t) \/ typeOf g3 (a1, a2) (Chan m io t)).
            apply typeCheck_lts_out with
              ((a1, a2, vis, Chan lin out t) :: (b1, b2, hid, s) :: g0) pf3 p1 b1 b2
              ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, s1) :: g0) p2 nd_pf0...
            destruct G4OUT as [m4' [t4' TYP4']].
            move g1 at top. apply fsuper_vis with
              (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as K0. destruct K0 as [K1 K2].
            inversion K1; subst.
            assert (vis = f /\ t0 = Chan lin q' t).
            apply in_isMap with (x := (a1, a2)) (g := g1)...
            destruct H7; subst.
            assert (CAP: In (a1, a2, vis, Chan lin inp t) g4 /\
                           In (a1, a2, vis, Chan lin out t) g3).
            
            apply split_lin_capab with
              (pf1 := pf4) (pf2 := pf3) (pf := pf1)
              (m1 := m4) (m2 := m4') (t1 := t4) (t2 := t4')
              (p := q')...
            destruct CAP as [CAP1 CAP2]...
            assert (TP4 : exists t2 : piType, typeOf g1 (a1, a2) t2 /\ type_plus ( Chan lin inp t) ( Chan lin out t) t2).
            apply split_type_plus_r with
              (pf1 := pf4) (pf2 := pf3) (pf := pf1)...
            destruct TP4 as [u1 [TYPa1 TPP]].
            inversion TPP; subst. inversion H11; subst.
            inversion TYPa1; subst.
            assert (f = vis /\ Chan lin io t = Chan lin q' t).
            apply in_isMap with (x := (a1, a2)) (g := g1)...
            destruct H8; subst. assert (CAP3 := H7).
            clear H7 H9 K1 K2.

            specialize IHLTS2 with
              (nd_pf1 := nd_pf4) (pf2 := pfw3) (pf := pf0').
            
            apply IHLTS2 in IHTSPLIT.
            destruct IHTSPLIT as [k4 LTSIN].

            assert (LEM2:
                     exists r4,
                       type_plus s4 t r4).
            
            apply plus_sub_exists with (s := s3) (r := s')...

            destruct LEM1 as [r3 TREM].
            destruct LEM2 as [r4 TPLUS].

            specialize split_exists_remove_l with
              g3 g4 g1 pf3 pf4 pf1 b1 b2 hid t s3 r3 as EXREM.
            apply EXREM in T3b as TYP3'.
            destruct TYP3' as [s'' [r'' [TYP1' TREM1]]].

            assert(nd_pfw1 :
                    NoDup(domain
                            ((a1, a2, vis, Chan lin out t)
                               :: (b1, b2, hid, s'')
                               :: removeEntry (a1, a2)
                               (removeEntry (b1, b2) g1)))).
            apply no_dup_cons_removeEntry_app...
            assert (nd_pfw2 :
                     NoDup(domain
                             ((a1, a2, vis, Chan lin inp t)
                                :: (b1, b2, ill, r'')
                                :: removeEntry (a1, a2)
                                (removeEntry (b1, b2) g1)))).
            apply no_dup_cons_removeEntry_app...
            exists (((a1, a2), vis, Chan lin empty t)
                      :: ((b1, b2), hid, s'')
                      :: removeEntry (a1, a2)
                      (removeEntry (b1, b2) g1)).
            apply lclsL with
              (s1 := r'') (pf1 := nd_pfw1) (pf2 := nd_pfw2).
            eauto.
            eauto.
            inversion TYP1'; subst.
            apply fsub_hid with (pf1 := pf3) (pf2 := pf4) (pf := pf1) in T3b as FYP. inversion FYP; subst. 
            assert (hid = f /\ t0 = s'').
            apply in_isMap with (x := (b1, b2)) (g := g1)...
            destruct H9; subst...
            eauto.

            remember ((a1, a2, vis, Chan lin out t)
                        :: (b1, b2, hid, s'') :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) as gk1.
            assert (EQREM: removeEntry (a1, a2) (removeEntry (b1, b2) gk1) =
                             removeEntry (a1, a2) (removeEntry (b1, b2) g1)).
            rewrite Heqgk1...
            specialize lts_type_remove_lin_out with
              (a1 := a1) (a2 := a2) (t := t) (b1 := b1) (b2 := b2)
              (f := hid) (f1 := vis) (g1 := gk1)
              (s01 := r'') (s := s3) (s1 := r3) (s0 := s'')
              (g0 := g3) (p1 := p1) (p2 := p2)
              (pf0 := nd_pf3) (pf1 := nd_pfw1)
              as LINOUT.
            rewrite <-EQREM.
            assert (Heqk1:
                     k1 =  ((a1, a2, vis, Chan lin empty t)
                              :: (b1, b2, vis, r3) :: removeEntry (a1, a2) (removeEntry (b1, b2) g3))).
            apply lts_lin_output_action with
              (p := p1) (p' := p2) (nd_pf := nd_pf3) (pol := out) (s := s3)...
            rewrite <-Heqk1 in LINOUT.

            apply LINOUT in LTSOUT as IH.
            eauto.
            eauto. 
            eauto.
            eauto.
            rewrite Heqgk1...
            rewrite Heqgk1...
            rewrite Heqgk1.
            (* forall x : name * name,
  In x (domain g3) <->
  In x (domain ((a1, a2, vis, Chan lin out t) :: (b1, b2, hid, s'') :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)))*)
             introv;
            erewrite <-sne_premises.in_removeEntry_cons_iff_2, split_domain_l_2...
            eapply split_domain_l_2... 
            eapply typeCheck_no_dup with (g := g3)...
            

(*            inv TCHECK; try eapply typeCheck_no_dup with (pf := pf0);
              try assumption; try eapply no_dup_split_no_dup_l with (g := g1)...
*)            
            rewrite Heqgk1; simpl.
            assert (HIDP3: incl (secLabs (dPar p1 q1)) (domain (hid_proj g1)))...
            eapply typeCheck_hid_proj...
            simpl in HIDP3; eapply incl_app_inv in HIDP3 as [_ HIDP3].
            introv IN; simpl.
            case_eq (pair_eq a (b1, b2)); intros PEQ; try rewrite <-pairEq_eq in PEQ;
              try subst a.
            left...
            right.
            assert (IN2:In a (domain (hid_proj  g1))).
            eapply HIDP3 in IN...
            assert (IN2' := IN2).
            eapply in_domain_in_g in IN2' as (ff &tt &IN2');
              repeat erewrite <-hid_proj_removeEntry; 
              try eapply in_g_in_domain, removeEntry_in...
            introv ABS; subst a.
            assert (ABS: flagOf g1 (a1, a2) hid).
            eapply hid_proj_flagOf...
            inv ABS.
            assert (ABS2: vis = hid /\ Chan lin io t = t0)...
            destruct ABS2; try discriminate.

            eapply removeEntry_in...
            introv ABS; subst a; try eapply pairEq_neq in PEQ;
              try contradiction.
            
            
            (* as above by using lts_lin_input_action *)
            
            remember ((a1, a2, vis, Chan lin inp t)
                        :: (b1, b2, ill, r'') :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) as gk1.
            assert (EQREM: removeEntry (a1, a2) (removeEntry (b1, b2) gk1) =
                             removeEntry (a1, a2) (removeEntry (b1, b2) g1)).
            rewrite Heqgk1.
            rewrite removeEntry_swap.
            unfold removeEntry at 2.
            assert (PEQ: pair_eq (a1, a2) (a1, a2) = true)...
            rewrite PEQ.
            unfold removeEntry at 1.
            assert (PEQ2: pair_eq (b1, b2) (b1, b2) = true)...
            rewrite PEQ2...
            eauto.

             rewrite <-EQREM.
            assert (Heqk4:
                     k4 =  ((a1, a2, vis, Chan lin empty t)
                              :: (b1, b2, vis, r4) :: removeEntry (a1, a2) (removeEntry (b1, b2) g4))).
            apply lts_lin_input_action with
              (p := q1) (p' := q2) (nd_pf := nd_pf4)
              (pol := inp) (s := s4)...
            (*rewrite <-Heqk4 in LININ.*)

            
            eapply lts_type_plus_lin_in;
              try rewrite <-Heqk4; subst gk1;
              try eassumption; try tauto.
            eauto.
            eauto.
            inverts TREM1 as [TP _]; eapply type_plus_comm...
            discriminate.

            (*forall x : name * name,
  In x (domain g4) <->
  In x (domain ((a1, a2, vis, Chan lin inp t) :: (b1, b2, ill, r'') :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)))*)
             introv;
            erewrite <-sne_premises.in_removeEntry_cons_iff_2, split_domain_l_2...
            eapply split_domain_l_2... 
            eapply typeCheck_no_dup with (g := g4)...

            (*inv TCHECK; try eapply typeCheck_no_dup with (pf := pf5);
              try assumption; try eapply no_dup_split_no_dup_r with (g := g1)...*)
            
            simpl.
            assert (IN: In (b1, b2) (fn p1) \/ In (b1, b2) (secLabs p1)).
            eapply payload_occurs...
            destruct IN as [ABS | INSL].
            eapply tc_dep_relabel_premises.typeCheck_is_vis in H5 as (tt& ABS2)...
            assert (ABS3: hid = vis /\ s3 = tt)...
            destruct ABS3; try discriminate.
            assert (NIN: ~In (b1, b2) (secLabs q1)).
            intros ABS.
            assert (ND: NoDup (secLabs  (dPar p1 q1))).
            eapply typeCheck_no_dup with (pf := pf1)...
            simpl in ND; eapply no_dup_iff in ND as (ND1 &ND2 &DIS).
            eapply disjoint_absurd...
            assert (HIDP3: incl (secLabs (dPar p1 q1)) (domain (hid_proj g1)))...
            eapply typeCheck_hid_proj...
            simpl in HIDP3; eapply incl_app_inv in HIDP3 as [HIDP3 _].
            introv IN; simpl.
            assert (IN2:In a (domain (hid_proj  g1))).
            eapply HIDP3 in IN...
            assert (IN2' := IN2).
            eapply in_domain_in_g in IN2' as (ff &tt &IN2');
              repeat erewrite <-hid_proj_removeEntry; 
              try eapply in_g_in_domain, removeEntry_in...
            introv ABS; subst a.
            assert (ABS: flagOf g1 (a1, a2) hid).
            eapply hid_proj_flagOf...
            inv ABS.
            assert (ABS2: vis = hid /\ Chan lin io t = t0)...
            destruct ABS2; try discriminate.

            eapply removeEntry_in...
            introv ABS; subst a; try contradiction.

            all:try eassumption.
            eapply sl_pos_par_r...

        ***
          destruct IHTSPLIT as
            [[NOTUN IHTSPLIT] | ABS].
          specialize IHLTS2 with
            (nd_pf1 := nd_pf4) (pf2 := pfw2) (pf := pf0').

          assert (G4IN: exists (m : mode) (t : piType),
                     typeOf g4 (a1, a2) (Chan m inp t) \/ typeOf g4 (a1, a2) (Chan m io t)).
          apply typeCheck_lts_in with
            ((a1, a2, vis, Chan lin inp t) :: (b1, b2, ill, s1) :: g0) pf4 q1 b1 b2
            ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, s) :: g0) q2 nd_pf0'...
          destruct G4IN as [m4 [t4 TYP4]].
          assert (G4OUT: exists (m : mode) (t : piType),
                     typeOf g3 (a1, a2) (Chan m out t) \/ typeOf g3 (a1, a2) (Chan m io t)).
          apply typeCheck_lts_out with
            ((a1, a2, vis, Chan lin out t) :: (b1, b2, hid, s) :: g0) pf3 p1 b1 b2
            ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, s1) :: g0) p2 nd_pf0...
          destruct G4OUT as [m4' [t4' TYP4']].
          move g1 at top. apply fsuper_vis with
            (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as K0. destruct K0 as [K1 K2].
          inversion K1; subst.
          assert (vis = f /\ t0 = Chan lin q' t).
          apply in_isMap with (x := (a1, a2)) (g := g1)...
          destruct H7; subst.
          assert (CAP: In (a1, a2, vis, Chan lin inp t) g4 /\
                         In (a1, a2, vis, Chan lin out t) g3).
          
          apply split_lin_capab with
            (pf1 := pf4) (pf2 := pf3) (pf := pf1)
            (m1 := m4) (m2 := m4') (t1 := t4) (t2 := t4')
            (p := q')...
          destruct CAP as [CAP1 CAP2]...
          assert (TP4 : exists t2 : piType, typeOf g1 (a1, a2) t2 /\ type_plus ( Chan lin inp t) ( Chan lin out t) t2).
          apply split_type_plus_r with
            (pf1 := pf4) (pf2 := pf3) (pf := pf1)...
          destruct TP4 as [u1 [TYPa1 TPP]].
          inversion TPP; subst. inversion H11; subst.
          inversion TYPa1; subst.
          assert (f = vis /\ Chan lin io t = Chan lin q' t).
          apply in_isMap with (x := (a1, a2)) (g := g1)...
          destruct H8; subst. assert (CAP3 := H7).
          clear H7 H9 K1 K2.
          assert (TOP: s = Top /\ t = Top /\ s1 = Top /\ s3 = Top /\ s4 = Top /\ s' = Top).
          inversion IHPREQ; subst.
          inversion TPLUS1; subst.
          inversion TYP3; subst.
          inversion TYP1; subst. intuition.
          
          apply IHLTS2 in IHTSPLIT.
          destruct IHTSPLIT as [k4 LTSIN].
          assert(nd_pfw1 :
                  NoDup(domain
                          ((a1, a2, vis, Chan lin out t)
                             :: (b1, b2, hid, Top)
                             :: removeEntry (a1, a2)
                             (removeEntry (b1, b2) g1)))).
          apply no_dup_cons_removeEntry_app...
          assert (nd_pfw2 :
                   NoDup(domain
                           ((a1, a2, vis, Chan lin inp t)
                              :: (b1, b2, ill, Top)
                              :: removeEntry (a1, a2)
                              (removeEntry (b1, b2) g1)))).
          apply no_dup_cons_removeEntry_app...
          exists (((a1, a2), vis, Chan lin empty t)
                    :: ((b1, b2), hid, Top)
                    :: removeEntry (a1, a2)
                    (removeEntry (b1, b2) g1)).
          apply lclsL with
            (s1 := Top) (pf1 := nd_pfw1) (pf2 := nd_pfw2).

          intuition.
          eauto.
          inversion IN1.
          subst.
          apply fsub_hid with (pf1 := pf3) (pf2 := pf4) (pf := pf1) in T3b as FYP. inversion FYP; subst. 
          assert (hid = f /\ t0 = s').
          apply in_isMap with (x := (b1, b2)) (g := g1)...
          destruct H9; subst.
          intuition; subst...
          eauto.
          
          remember ((a1, a2, vis, Chan lin out t)
                      :: (b1, b2, hid, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) as gk1.
          assert (EQREM: removeEntry (a1, a2) (removeEntry (b1, b2) gk1) =
                           removeEntry (a1, a2) (removeEntry (b1, b2) g1)).
          rewrite Heqgk1...
          specialize lts_type_remove_lin_out with
            (a1 := a1) (a2 := a2) (t := t) (b1 := b1) (b2 := b2)
            (f := hid) (f1 := vis) (g1 := gk1)
            (s01 := Top) (s := Top) (s1 := Top) (s0 := Top)
            (g0 := g3) (p1 := p1) (p2 := p2)
            (pf0 := nd_pf3) (pf1 := nd_pfw1)
            as LINOUT.
          rewrite <-EQREM.
          assert (Heqk1:
                   k1 =  ((a1, a2, vis, Chan lin empty t)
                            :: (b1, b2, vis, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g3))).
          apply lts_lin_output_action with
            (p := p1) (p' := p2) (nd_pf := nd_pf3) (pol := out) (s := Top).
          eauto. eauto. intuition; subst...
          intuition; subst...

          rewrite <-Heqk1 in LINOUT.

          apply LINOUT in LTSOUT as IH.
          eauto.
          eauto.
          intuition; subst...
          intuition; subst...
          rewrite Heqgk1...
          rewrite Heqgk1...
          rewrite Heqgk1.
          (* forall x : name * name,
  In x (domain g3) <->
  In x (domain ((a1, a2, vis, Chan lin out t) :: (b1, b2, hid, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1))) *)
           introv;
            erewrite <-sne_premises.in_removeEntry_cons_iff_2, split_domain_l_2...
            eapply split_domain_l_2... 
            eapply typeCheck_no_dup with (g := g3)...

          (*inv TCHECK.
          try eapply typeCheck_no_dup with (pf := pf0);
             try assumption; try eapply no_dup_split_no_dup_l with (g := g1)...*)
           
            rewrite Heqgk1; simpl.
            assert (HIDP3: incl (secLabs (dPar p1 q1)) (domain (hid_proj g1)))...
            eapply typeCheck_hid_proj...
            simpl in HIDP3; eapply incl_app_inv in HIDP3 as [_ HIDP3].
            introv IN; simpl.
            assert (IN2:In a (domain (hid_proj  g1))).
            eapply HIDP3 in IN...
            
            case_eq (pair_eq a (b1, b2)); intros PEQ; try rewrite <-pairEq_eq in PEQ;
              try subst a.
            left...
            right.
            assert (IN2' := IN2).
            eapply in_domain_in_g in IN2' as (ff &tt &IN2');
              repeat erewrite <-hid_proj_removeEntry; 
              try eapply in_g_in_domain, removeEntry_in...
            introv ABS; subst a.
            assert (ABS: flagOf g1 (a1, a2) hid).
            eapply hid_proj_flagOf...
            inv ABS.
            assert (ABS2: vis = hid /\ Chan lin io t = t0)...
            destruct ABS2; try discriminate.

            eapply removeEntry_in...
            introv ABS; subst a; try eapply pairEq_neq in PEQ; try contradiction.

            all:try eassumption.
          
          (* as above by using lts_lin_input_action *)
          
          remember ((a1, a2, vis, Chan lin inp t)
                      :: (b1, b2, ill, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) as gk1.
          assert (EQREM: removeEntry (a1, a2) (removeEntry (b1, b2) gk1) =
                           removeEntry (a1, a2) (removeEntry (b1, b2) g1)).
          rewrite Heqgk1.
          rewrite removeEntry_swap.
          unfold removeEntry at 2.
          assert (PEQ: pair_eq (a1, a2) (a1, a2) = true)...
          rewrite PEQ.
          unfold removeEntry at 1.
          assert (PEQ2: pair_eq (b1, b2) (b1, b2) = true)...
          rewrite PEQ2...
          eauto.

          assert (K10 : t = Top).
          inversion IHPREQ; subst.
          inversion TPLUS1; subst. 
          inversion TYP3...
          assert (K11: s4 = Top).
          rewrite K10 in TYP3; inversion TYP3; subst; inversion TPLUS1; inversion TPLUS1; subst...
          assert (K12: s3 = Top).
          rewrite K11 in TPLUS1; inversion TPLUS1; subst...

             rewrite <-EQREM.
            assert (Heqk4:
                     k4 =  ((a1, a2, vis, Chan lin empty t)
                              :: (b1, b2, vis, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g4))).
            apply lts_lin_input_action with
              (p := q1) (p' := q2) (nd_pf := nd_pf4)
              (pol := inp) (s := s4); subst...
            (*rewrite <-Heqk4 in LININ.*)

            
             eapply lts_type_plus_lin_in;
               try rewrite <-Heqk4; subst;
               try eassumption; try tauto.
             eauto.
             eauto.
             eauto.
             discriminate.

            (*forall x : name * name,
  In x (domain g4) <->
  In x (domain ((a1, a2, vis, Chan lin inp t) :: (b1, b2, ill, r'') :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)))*)
              introv;
            erewrite <-sne_premises.in_removeEntry_cons_iff_2, split_domain_l_2...
            eapply split_domain_l_2... 
            eapply typeCheck_no_dup with (g := g4)...
            
            simpl.
            assert (IN: In (b1, b2) (fn p1) \/ In (b1, b2) (secLabs p1)).
            eapply payload_occurs...
            destruct IN as [ABS | INSL].
            eapply tc_dep_relabel_premises.typeCheck_is_vis in H5 as (tt& ABS2)...
            assert (ABS3: hid = vis /\ Top = tt)...
            destruct ABS3; try discriminate.
            assert (NIN: ~In (b1, b2) (secLabs q1)).
            intros ABS.
            assert (ND: NoDup (secLabs  (dPar p1 q1))).
            eapply typeCheck_no_dup with (pf := pf1)...
            simpl in ND; eapply no_dup_iff in ND as (ND1 &ND2 &DIS).
            eapply disjoint_absurd...
            assert (HIDP3: incl (secLabs (dPar p1 q1)) (domain (hid_proj g1)))...
            eapply typeCheck_hid_proj...
            simpl in HIDP3; eapply incl_app_inv in HIDP3 as [HIDP3 _].
            introv IN; simpl.
            assert (IN2:In a (domain (hid_proj  g1))).
            eapply HIDP3 in IN...
            assert (IN2' := IN2).
            eapply in_domain_in_g in IN2' as (ff &tt &IN2');
              repeat erewrite <-hid_proj_removeEntry; 
              try eapply in_g_in_domain, removeEntry_in...
            introv ABS; subst a.
            assert (ABS: flagOf g1 (a1, a2) hid).
            eapply hid_proj_flagOf...
            inv ABS.
            assert (ABS2: vis = hid /\ Chan lin q' Top = t)...
            destruct ABS2; try discriminate.

            eapply removeEntry_in...
            introv ABS; subst a; try contradiction.

            eapply sl_pos_par_r...

          
          unfold is_unrestricted in ABS.
          destruct ABS as [ABS1 ABS2].
          destruct ABS1 as [p0 [t0 ABS1]];inversion ABS1...
        *** eauto.
        ***  eapply sl_pos_par_l...
      * eauto.
      * eauto.  
  - Case ucomL.
    intros.
    remember g3 as gg3; subst g3.
    inversion TCHECK; subst.
    remember pf0 as nd_pf; subst pf0.
    remember pf1 as nd_pf0; subst pf1.
    remember pf2 as nd_pf0'; subst pf2.
    remember pf4 as pf1; subst pf4.
    remember pf3 as pf2; subst pf3.
    remember pf5 as pf3; subst pf5.
    remember pf6 as pf4; subst pf6.
    
    assert (TSPLIT2 := H6); clear H6.
    
    

    apply split_of_split with
      g3 g4 g1 g2 g pf3 pf4 pf1 pf2 pf
      in TSPLIT2 as TSPLIT3.
    destruct TSPLIT3 as [h [pfh TSPLIT3]].
    
    * apply no_dup_split_no_dup_l in TSPLIT3 as nd_pf3.
      specialize IHLTS1 with (pf1 := pf3) (pf2 := pfh) (pf := pf) (nd_pf1 := nd_pf3).
      apply IHLTS1 in TSPLIT3 as SPLITOUT.
      destruct SPLITOUT as [k1 LTSOUT].

      apply split_comm in TSPLIT2 as TSPLIT4. 
      apply split_of_split with
        g4 g3 g1 g2 g pf4 pf3 pf1 pf2 pf
        in TSPLIT4 as TSPLIT5.
      destruct TSPLIT5 as [w [pfw TSPLIT5]].
      (* TSPLIT5 : tEnv_split g4 w g pf4 pfw pf *)

      specialize IHLTS2 with (pf1 := pf4).
      
      
      assert (T3b : exists s3,
                 In (b1, b2, vis, s3) g3).
      specialize fsuper_vis with g3 h g pf3 pfh pf (b1, b2) s as FVIS.
      
      apply FVIS in TSPLIT3 as FVIS3.
      destruct FVIS3 as [FVIS3 FVISW].
      destruct s.
      apply tsuper_payload with
        (pf1 := pf3) (pf2 := pfh) (pf := pf) in H1 as T1b.
      destruct T1b as [pq1 T1b]. exists (Chan m pq1 s).
      inversion T1b. inversion FVIS3. subst.
      assert (f = vis /\ Chan m pq1 s = t1).
      apply in_isMap with (x := (b1, b2)) (g := g3)...
      destruct H5; subst...
      eauto.
      apply tsuper_top with
        (pf1 := pf3) (pf2 := pfh) (pf := pf) in H1 as T1b.
      exists Top.
      inversion FVIS3. inversion T1b. subst.
      assert (f0 = vis /\ Top = t0).
      apply in_isMap with (x := (b1, b2)) (g := g3)...
      destruct H5; subst...
      eauto.
      eauto.
      destruct T3b as [s3 T3b].
      
      apply tsuper_payload with
        (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as K0.
      destruct K0 as [q' TYP']; inversion TYP'; subst.
      apply tsuper_payload with
        (pf1 := pf3) (pf2 := pf4) (pf := pf1) in H4 as K2.
      destruct K2 as [q'' TYP2]; inversion TYP2; subst.
      assert (LEM1:
               exists r3,
                 type_remove s3 t r3)...
      assert (T4b : exists s4,
                 In (b1, b2, vis, s4) g4).
      specialize fsuper_vis with g4 w g pf4 pfw pf (b1, b2) s as FVIS.
      
      apply FVIS in TSPLIT5 as FVIS3.
      destruct FVIS3 as [FVIS3 FVISW].
      destruct s.
      apply tsuper_payload with
        (pf1 := pf4) (pf2 := pfw) (pf := pf) in H1 as T1b.
      destruct T1b as [pq1 T1b]. exists (Chan m pq1 s).
      inversion T1b. inversion FVIS3. subst.
      assert (f1 = vis /\ Chan m pq1 s = t1).
      apply in_isMap with (x := (b1, b2)) (g := g4)...
      destruct H9; subst...
      eauto.
      apply tsuper_top with
        (pf1 := pf4) (pf2 := pfw) (pf := pf) in H1 as T1b.
      exists Top.
      inversion FVIS3. inversion T1b. subst.
      assert (f2 = vis /\ Top = t0).
      apply in_isMap with (x := (b1, b2)) (g := g4)...
      destruct H9; subst...
      eauto.
      eauto.
      
      destruct T4b as [s4 T4b].
      
      assert (TYPw : exists sw, In ((b1, b2), vis, sw) w /\
                                  type_plus s4 sw s).
      specialize split_type_plus with
        g4 w g pf4 pfw pf (b1, b2) s4 s as TP1.
      assert (TYP4: typeOf g4 (b1, b2) s4)...
      apply TP1 in TYP4. clear TP1.
      destruct TYP4 as [t2 [INw TP4]].
      exists t2.
      inversion INw; subst.
      apply fsub_vis with
        (pf1 := pf4) (pf2 := pfw) (pf := pf) in T4b as FYP.
      inversion FYP; subst.
      apply fsuper_vis with
        (pf1 := pf4) (pf2 := pfw) (pf := pf) in H1 as FYP2.
      destruct FYP2 as [FYP4 FYPw]; inversion FYPw; subst.
      assert (f1 = vis /\ t2 = t1).
      apply in_isMap with (x := (b1, b2)) (g := w)...
      destruct H11; subst...
      all:try eassumption.
      eauto.
      
      
      assert (nd_pf4 : NoDup(domain g4)).
      apply no_dup_split_no_dup_l with
        (pf1 := pf4) (pf2 := pfw) (pf := pf)
        in nd_pf as nd_pf4...
      specialize split_type_plus_r with
        g4 g3 g1 pf4 pf3 pf1 (b1, b2) s4 s3 as TP1...
      assert (TYP4: typeOf g4 (b1, b2) s4)...
      apply TP1 in TYP4. clear TP1.
      destruct TYP4 as [s' [IN1 TPLUS1]].
      assert (TYP3: type_sub t s3).
      destruct LEM1 as [r3 TREM].
      assert (TREM2 := TREM); inversion TREM2...
      assert (TYP1 : type_sub s' s)...
      
      assert (IHPREQ : exists r2, type_plus s4 r2 s1).
      apply type_plus_exists with
        (s := s) (t := t) (s3 := s3) (s' := s')...
      destruct IHPREQ as [r2 IHPREQ].
      remember ( (b1, b2, vis, r2)
                   :: removeEntry (b1, b2) w) as w2. 
      assert (pfw2 : isMap w2). rewrite Heqw2.
      apply cons_removeEntry;
        try eapply no_dup_split_no_dup_r in nd_pf...
      remember ((b1, b2, vis, s4)
                  :: removeEntry (b1, b2) w) as w3. 
      assert (pfw3 : isMap w3). rewrite Heqw3. 
      apply cons_removeEntry;
        try eapply no_dup_split_no_dup_r in nd_pf...
      assert (pf0' :
               isMap ( (b1, b2, vis, s1) :: g0)).
      apply cons_removeEntry...
      assert (IHTSPLIT:
               (~is_unrestricted r2 /\ tEnv_split g4 w2 ((b1, b2, vis, s1) :: g0) pf4 pfw2 pf0') \/ 
                 (is_unrestricted r2 /\ tEnv_split g4 w3 ((b1, b2, vis, s1) :: g0) pf4 pfw3 pf0')).
      destruct s1. inversion IHPREQ. subst.
      assert (pf' : isMap (removeEntry (b1, b2) g4)).
      apply isMap_removeEntry...
      assert (pf'' : isMap (removeEntry (b1, b2) ( (b1, b2, vis, Chan lin p3 s1) ::  (removeEntry (b1, b2) w)))).
      apply isMap_removeEntry...
      assert (pf''' : isMap (removeEntry (b1, b2) ((b1, b2, vis, Chan lin p s1) :: g0))).
      apply isMap_removeEntry...

      left.
      split. unfold is_unrestricted. intro ABS.
      destruct ABS as [p9 [t9 ABS]]; inversion ABS.
      apply SpLin with
        (n := (b1, b2)) (f := vis) (g := vis) (f' := vis)
        (p := p0) (q := p3) (p' := p) (t := s1)
        (pf' := pf') (pf'' := pf'') (pf''' := pf''').
      all:try eassumption.
      eauto.
      eauto.
      
      (* tEnv_split (removeEntry (b1, b2) g4)
    (removeEntry (b1, b2)
       ((a1, a2, vis, Chan lin empty t)
        :: (b1, b2, vis, Chan lin p3 s1) :: removeEntry (a1, a2) (removeEntry (b1, b2) w)))
    (removeEntry (b1, b2) ((a1, a2, vis, Chan lin inp t) :: (b1, b2, vis, Chan lin p s1) :: g0))
    pf' pf'' pf''' *)
      apply split_remove with
        (pf1 :=  pf4) (pf2 := pfw2) (pf3 := pf0').
      eauto. 
      apply no_dup_cons_removeEntry;
        try eapply no_dup_split_no_dup_r in nd_pf...
      subst g0. apply no_dup_cons_removeEntry...
      apply split_new_un_lin with
        (pf1 := pf4) (pf2 := pfw) (pf := pf)
        (a1 := a1) (a2 := a2) (t := t)
        (f := vis) (p := io) (h1 := vis) (q1 := p0).
      eauto. eauto.
      inversion TYP2; subst. 
      apply tsuper_payload with
        (pf1 := pf4) (pf2 := pfw) (pf := pf) in H0 as K0.
      destruct K0 as [q4 TYP4]. inversion TYP4; subst.
      inversion TYP'; subst. 
      assert (q4 = q'' /\ q'' = q').
      apply split_plus_un with
        (pf1 := pf4) (pf2 := pf3) (pf3 := pf1) (b1 := a1) (b2 := a2) (t := t) (f1 := f2) (f2 := f1) (f3 := f3)...
      destruct H12; subst.
      apply tsuper_payload_r with
        (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as K0.
      destruct K0 as [q'' TYP2']. inversion TYP2'; subst.
      assert (q' = q'' /\ q'' = io).
      apply split_plus_un with
        (pf1 := pf1) (pf2 := pf2) (pf3 := pf) (b1 := a1) (b2 := a2) (t := t) (f1 := f3) (f2 := f4) (f3 := vis)...
      destruct H13; subst.
      
      move g2 at top.
      apply fsuper_vis
        with (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as [K1 K2].
      inversion K1; subst. 
      assert (vis = f3 /\ t0 =  Chan un io t).
      apply in_isMap with (x := (a1, a2)) (g := g1)...
      destruct H13; subst.
      apply fsuper_vis
        with (pf1 := pf4) (pf2 := pf3) (pf := pf1) in H0 as [K3 K4].
      inversion K3; subst.
      assert (vis = f2 /\ t0 = Chan un io t).
      apply in_isMap with (x := (a1, a2)) (g := g4)...
      destruct H13; subst...
      all:try eassumption.

      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      
      
      right. split. unfold is_unrestricted.
      exists p3. exists s1...
      assert (ISUNS: is_unrestricted s).
      subst.  inversion TPLUS1. subst. inversion TYP1...
      subst. 
      inversion H. destruct H9 as [TPS ISUN].
      apply ISUN in ISUNS as ISUN2. subst s. clear ISUN.
      apply tsuper_payload with
        (pf1 := pf1) (pf2 := pf2) (pf := pf) in H1 as K1.
      apply tsuper_payload_r with
        (pf1 := pf1) (pf2 := pf2) (pf := pf) in H1 as K2.
      destruct K1 as [pol1 TB1]. destruct K2 as [pol2 TB2].
      inversion TB1. inversion TB2. subst.
      assert (pol1 = pol2 /\ pol2 = (pol_cup p0 p3)).
      apply split_plus_un with
        (pf1 := pf1) (pf2 := pf2) (pf3 := pf)
        (b1 := b1) (b2 := b2) (t := s1)
        (f1 := f1) (f2 := f2) (f3 := vis)...
      destruct H10; subst.
      apply tsuper_payload_r with
        (pf1 := pf4) (pf2 := pf3) (pf := pf1) in H9 as K7.
      destruct K7 as [pol7 TB3]. inversion TB3; subst. 
      assert (p0 = pol7 /\ pol7 = (pol_cup p0 p3)).
      apply split_plus_un with
        (pf1 := pf4) (pf2 := pf3) (pf3 := pf1)
        (b1 := b1) (b2 := b2) (t := s1)
        (f1 := vis) (f2 := f3) (f3 := f1)...
      destruct H11. assert (POLEQ: p0 = pol_cup p0 p3).
      transitivity pol7...
      revert dependent pf0'.
      rewrite <-POLEQ.
      intros.
      assert (pf' : isMap (removeEntry (b1, b2) g4)).
      apply isMap_removeEntry...
      assert (pf'' : isMap (removeEntry (b1, b2) ( (b1, b2, vis, Chan un p0 s1) ::  (removeEntry (b1, b2) w)))).
      apply isMap_removeEntry...
      assert (pf''' : isMap (removeEntry (b1, b2) ( (b1, b2, vis, Chan un p0 s1) :: g0))).
      apply isMap_removeEntry...
      apply SpUn with
        (n := (b1, b2)) (f := vis) (g := vis) (f' := vis)
        (p := p0) (t := s1)
        (pf' := pf') (pf'' := pf'') (pf''' := pf''').
      eauto.
      eauto.
      eauto.
      (*tEnv_split (removeEntry (b1, b2) g4)
    (removeEntry (b1, b2) ((b1, b2, vis, Chan un p0 s1) :: removeEntry (b1, b2) w))
    (removeEntry (b1, b2) ((b1, b2, vis, Chan un p0 s1) :: g0)) pf' pf'' pf'''*)
      assert (pf0'' : isMap
                        ((b1, b2, vis, Chan un p0 s1) :: g0)).
      subst...
      apply split_remove with
        (pf1 :=  pf4) (pf2 := pfw3) (pf3 := pf0'').
      eauto. 
      apply no_dup_cons_removeEntry;
        try eapply no_dup_split_no_dup_r in nd_pf...
      subst g0. apply no_dup_cons_removeEntry...
      (*tEnv_split g4
    ((a1, a2, vis, Chan lin empty t)
     :: (b1, b2, vis, Chan un p0 s1) :: removeEntry (a1, a2) (removeEntry (b1, b2) w))
    ((a1, a2, vis, Chan lin inp t) :: (b1, b2, vis, Chan un p0 s1) :: g0) pf4 pfw3 pf0''*)
      apply split_new_un_un with
        (pf1 := pf4) (pf2 := pfw) (pf := pf)
        (a1 := a1) (a2 := a2) (t := t)
        (f := vis) (p := io) (h1 := vis) (q := p0).
      eauto. eauto.
      

      inversion TYP2; subst.
      apply tsuper_payload with
        (pf1 := pf4) (pf2 := pfw) (pf := pf) in H0 as K0.
      destruct K0 as [q4 TYP4]. inversion TYP4; subst.
      inversion TYP'; subst. 
      assert (q4 = q'' /\ q'' = q').
      apply split_plus_un with
        (pf1 := pf4) (pf2 := pf3) (pf3 := pf1) (b1 := a1) (b2 := a2) (t := t) (f1 := f5) (f2 := f4) (f3 := f6)...
      destruct H16; subst.
      apply tsuper_payload_r with
        (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as K0.
      destruct K0 as [q'' TYP2']. inversion TYP2'; subst.
      assert (q' = q'' /\ q'' = io).
      apply split_plus_un with
        (pf1 := pf1) (pf2 := pf2) (pf3 := pf) (b1 := a1) (b2 := a2) (t := t) (f1 := f6) (f2 := f7) (f3 := vis)...
      destruct H17; subst.
      
      move g2 at top.
      apply fsuper_vis
        with (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as [K1 K2].
      inversion K1; subst. 
      assert (vis = f6 /\ t0 =  Chan un io t).
      apply in_isMap with (x := (a1, a2)) (g := g1)...
      destruct H17; subst.
      apply fsuper_vis
        with (pf1 := pf4) (pf2 := pf3) (pf := pf1) in H0 as [K3 K4].
      inversion K3; subst.
      assert (vis = f5 /\ t0 =  Chan un io t).
      apply in_isMap with (x := (a1, a2)) (g := g4)...
      destruct H17; subst...
      all:try eassumption.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      
      left. split. 
      unfold is_unrestricted. intro ABS.
      inversion IHPREQ; subst. 
      destruct ABS as [p9 [t9 ABS]]; inversion ABS.
      inversion IHPREQ; subst.
      assert (pf' : isMap (removeEntry (b1, b2) g4)).
      apply isMap_removeEntry...
      assert (pf'' : isMap (removeEntry (b1, b2) ((b1, b2, vis, Top) :: (removeEntry (b1, b2) w)))).
      apply isMap_removeEntry...
      assert (pf''' : isMap (removeEntry (b1, b2) ( (b1, b2, vis, Top) :: g0))).
      apply isMap_removeEntry...
      apply SpTop with
        (n := (b1, b2)) (f := vis) (g := vis) (f' := vis)
        
        (pf' := pf') (pf'' := pf'') (pf''' := pf''').
      all:try eassumption.
      eauto.
      eauto.
      
      (*tEnv_split (removeEntry (b1, b2) g4)
    (removeEntry (b1, b2) ((b1, b2, vis, Top) :: removeEntry (b1, b2) w))
    (removeEntry (b1, b2) ((b1, b2, vis, Top) :: g0)) pf' pf'' pf'''*)
      assert (pf0'' : isMap
                        (( (b1, b2, vis, Top) :: g0))).
      subst...
      apply split_remove with
        (pf1 :=  pf4) (pf2 := pfw3) (pf3 := pf0'').
      eauto. 
      apply no_dup_cons_removeEntry;
        try eapply no_dup_split_no_dup_r in nd_pf...
      subst g0. apply no_dup_cons_removeEntry...
      apply split_new_un_top with
        (pf1 := pf4) (pf2 := pfw) (pf := pf)
        (a1 := a1) (a2 := a2) (t := t)
        (f := vis) (p := io) (h1 := vis).
      eauto. eauto.

      inversion TYP2; subst.
      apply tsuper_payload with
        (pf1 := pf4) (pf2 := pfw) (pf := pf) in H0 as K0.
      destruct K0 as [q4 TYP4]. inversion TYP4; subst.
      inversion TYP'; subst. 
      assert (q4 = q'' /\ q'' = q').
      apply split_plus_un with
        (pf1 := pf4) (pf2 := pf3) (pf3 := pf1) (b1 := a1) (b2 := a2) (t := t) (f1 := f2) (f2 := f1) (f3 := f3)...
      destruct H11; subst.
      apply tsuper_payload_r with
        (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as K0.
      destruct K0 as [q'' TYP2']. inversion TYP2'; subst.
      assert (q' = q'' /\ q'' = io).
      apply split_plus_un with
        (pf1 := pf1) (pf2 := pf2) (pf3 := pf) (b1 := a1) (b2 := a2) (t := t) (f1 := f3) (f2 := f4) (f3 := vis)...
      destruct H12; subst.
      
      move g2 at top.
      apply fsuper_vis
        with (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as [K1 K2].
      inversion K1; subst. 
      assert (vis = f3 /\ t0 =  Chan un io t).
      apply in_isMap with (x := (a1, a2)) (g := g1)...
      destruct H12; subst.
      apply fsuper_vis
        with (pf1 := pf4) (pf2 := pf3) (pf := pf1) in H0 as [K3 K4].
      inversion K3; subst.
      assert (vis = f2 /\ t0 =  Chan un io t).
      apply in_isMap with (x := (a1, a2)) (g := g4)...
      destruct H12; subst...
      all:try eassumption.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.

      
      destruct r2.
      ***
        destruct m.
        (*  ~ is_unrestricted (Chan lin p r2) *)
        ****
          assert (TYPa := H0).
          inversion TYP2; subst.
          apply tsuper_payload with
            (pf1 := pf4) (pf2 := pfw) (pf := pf) in H0 as K0.
          destruct K0 as [q4 TYP4]. inversion TYP4; subst.
          inversion TYP'; subst. 
          assert (q4 = q'' /\ q'' = q').
          apply split_plus_un with
            (pf1 := pf4) (pf2 := pf3) (pf3 := pf1) (b1 := a1) (b2 := a2) (t := t) (f1 := f2) (f2 := f1) (f3 := f3)...
          destruct H11; subst.
          apply tsuper_payload_r with
            (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as K0.
          destruct K0 as [q'' TYP2']. inversion TYP2'; subst.
          assert (q' = q'' /\ q'' = io).
          apply split_plus_un with
            (pf1 := pf1) (pf2 := pf2) (pf3 := pf) (b1 := a1) (b2 := a2) (t := t) (f1 := f3) (f2 := f4) (f3 := vis)...
          destruct H12; subst.
          
          move g2 at top.
          apply fsuper_vis
            with (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as [K1 K2].
          inversion K1; subst. 
          assert (vis = f3 /\ t0 =  Chan un io t).
          apply in_isMap with (x := (a1, a2)) (g := g1)...
          destruct H12; subst.
          apply fsuper_vis
            with (pf1 := pf4) (pf2 := pf3) (pf := pf1) in H0 as [K3 K4].
          inversion K3; subst.
          assert (vis = f2 /\ t0 =  Chan un io t).
          apply in_isMap with (x := (a1, a2)) (g := g4)...
          destruct H12; subst...
          inversion K4; subst.
          assert (vis = f1 /\ t0 =  Chan un io t).
          apply in_isMap with (x := (a1, a2)) (g := g3)...
          destruct H13; subst.
          all:try eassumption.
          
          
          destruct IHTSPLIT as
            [[NOTUN IHTSPLIT] | ABS].
          specialize IHLTS2 with
            (nd_pf1 := nd_pf4) (pf2 := pfw2) (pf := pf0').
          
          apply IHLTS2 in IHTSPLIT.
          destruct IHTSPLIT as [k4 LTSIN].
          
          assert (LEM2:
                   exists r4,
                     type_plus s4 t r4).
          apply plus_sub_exists with
            (s := s3) (r := s')...
          
          destruct LEM1 as [r3 TREM].
          destruct LEM2 as [r4 TPLUS].

          specialize split_exists_remove_l with
            g3 g4 g1 pf3 pf4 pf1 b1 b2 vis t s3 r3 as EXREM.
          apply EXREM in T3b as TYP3'. clear EXREM.
          destruct TYP3' as [s'' [r'' [TYP1' TREM1]]].
          inversion TYP1'; subst.
          apply fsuper_vis with (pf1 := pf1) (pf2 := pf2) (pf := pf) in H1 as K5.
          destruct K5 as [K5 K6].
          inversion K5; subst.
          assert (vis = f1 /\ t0 = s'').
          apply in_isMap with (x := (b1, b2)) (g := g1)...
          destruct H15; subst.
          move LTS2 at bottom.
          apply lts_un_input_action
            with (pol := io) (t := t) (s := s1) (r := s)
            in LTS2 as Heqgg3.
          destruct Heqgg3 as (kk3 &DIS2 &Heqgg3).
          rewrite Heqgg3 in LTS2.
          
          assert (nd_pfw2 :
                   NoDup(domain
                           ((b1, b2, vis, r'')
                              ::    (removeEntry (b1, b2) g1)))).
          apply no_dup_cons_removeEntry...
          
          unfold g' in LTS2. unfold g0 in LTS2.
          apply lts_type_plus_un_in with
            (a1 := a1) (a2 := a2) (t := t) (b1 := b1) (b2 := b2)
            (f := vis) (f1 := vis) (pol := io)
            (s01 := r'') (s := s) (s1 := s1) (s0 := s'')
            (pf1 := nd_pfw2)
            in LTS2 as UNIN.
          destruct UNIN as [kk1 UNIN].

          
          exists (kk1 ++
                    (b1, b2, vis, s'')
                    :: removeEntry (b1, b2) ((b1, b2, vis, r'') :: removeEntry (b1, b2) g1)).
          apply ucomL with
            (s1 := r'') (s := s'') (t := t)(pf1 := nd_pf1) (pf2 := nd_pfw2).
          eauto.
          eauto.
          eauto.            
          
          specialize lts_type_remove_un_out with
            (a1 := a1) (a2 := a2) (t := t) (b1 := b1) (b2 := b2)
            (f := vis) (f1 := vis)
            (s01 := r'') (s := s3) (s1 := r3) (s0 := s'')
            (pol := io)
            (pf := nd_pf3) (pf1 := nd_pf1)
            as UNOUT.
          
          assert (Heqk1:
                   k1 =  ( (b1, b2, vis, r3) :: (removeEntry (b1, b2) g3))).

          apply lts_un_output_action with
            (p := p1) (p' := p2) (nd_pf := nd_pf3)
            (pol := io) (s := s3)
            (a1 := a1) (a2 := a2) (t:= t)...
          
          rewrite <-Heqk1 in UNOUT.

          apply UNOUT in LTSOUT as IH.
          eauto.
          eauto.
          eauto.
          eauto.
          eauto.
          eauto.
          eauto.

          eapply typeCheck_no_dup with (pf := pf3)...
          assert (INCL: incl (secLabs p1) (domain (hid_proj g3))).
          eapply typeCheck_hid_proj with (pf := pf3)...
          assert (INCL2: incl (domain (hid_proj g3))(domain (hid_proj g1))).
          eapply split_incl_hid_proj...
          eapply incl_tran...
          eauto.
          
          apply in_app_iff with (l := kk1).
          right.
          apply in_app_iff with (l := (b1, b2, vis, s'') :: nil).
          right.
          apply removeEntry_in.
          eauto.
          apply in_app_iff with (l := (b1, b2, vis, r'') :: nil).
          right.
          apply removeEntry_in...
          apply in_app_iff with (l := kk1). right...
          apply in_app_iff with (l := (b1, b2, vis, s1) :: nil).
          right. apply removeEntry_in...
          eauto.
          
          inversion TREM1.
          destruct H16 as [TP ISUN]; apply type_plus_comm...
          discriminate.
          apply in_app_iff with (l := (b1, b2, vis, r'') :: nil).
          right. apply removeEntry_in...
          eauto.
          
          apply split_removeEntry_domain_2 with
            (pf1 := pf1) (pf2 := pf2) (pf := pf)...
          assert (In (a1, a2, vis, (Chan un io t)) g').
          unfold g'. unfold g0.
          apply in_app_iff with (l := (b1, b2, vis, s1) :: nil).
          right. apply removeEntry_in...
          eauto.
          unfold g'...

          eapply typeCheck_no_dup with (pf := pf4)...
          simpl.
          introv IN.
          assert (a <> (b1, b2)).
          intros ABS; subst a.
          eapply type_checking_0.typeCheck_hid with (n := (b1, b2)) in H8 as (tt &K).
          assert (ABS: vis = hid /\ s4 = tt)...
          destruct ABS; try discriminate...
          assumption.
          rewrite <-hid_proj_removeEntry.
          assert (INCL: incl (secLabs q1) (domain (hid_proj g4))).
          eapply typeCheck_hid_proj with (pf := pf4)...
          assert (INCL2: incl (domain (hid_proj g4))(domain (hid_proj g1))).
          eapply split_incl_hid_proj...
          eapply INCL,INCL2,in_domain_in_g in IN.
          destruct IN as (ff &tt &IN).
          eapply in_g_in_domain,removeEntry_in...
          
          eauto.
          eauto.
          subst g' g0; econstructor; right; try eapply removeEntry_in...
          subst g' g0; econstructor...

          inversion H. destruct H16 as [TPLUSS ISUN]; apply type_plus_comm...
          all:try eassumption.
          eapply sl_pos_par_r...

          subst g' g0; try  erewrite <-max_removeEntry_cons;
            try eapply in_g_in_domain;
            try eapply incl_preserves_max...
          assert (IN4: incl (secLabs q1) (domain g4)).
          try eapply typeCheck_no_dup with (pf := pf4)...
          introv IN';erewrite <-split_domain_l...

           eapply sl_pos_par_r...
          
          unfold is_unrestricted in ABS.
          destruct ABS as [ABS1 ABS2].
          destruct ABS1 as [p0 [t0 ABS1]];inversion ABS1...
        ****
          assert (TYPa := H0).
          inversion TYP2; subst.
          apply tsuper_payload with
            (pf1 := pf4) (pf2 := pfw) (pf := pf) in H0 as K0.
          destruct K0 as [q4 TYP4]. inversion TYP4; subst.
          inversion TYP'; subst. 
          assert (q4 = q'' /\ q'' = q').
          apply split_plus_un with
            (pf1 := pf4) (pf2 := pf3) (pf3 := pf1) (b1 := a1) (b2 := a2) (t := t) (f1 := f2) (f2 := f1) (f3 := f3)...
          destruct H11; subst.
          apply tsuper_payload_r with
            (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as K0.
          destruct K0 as [q'' TYP2']. inversion TYP2'; subst.
          assert (q' = q'' /\ q'' = io).
          apply split_plus_un with
            (pf1 := pf1) (pf2 := pf2) (pf3 := pf) (b1 := a1) (b2 := a2) (t := t) (f1 := f3) (f2 := f4) (f3 := vis)...
          destruct H12; subst.
          
          move g2 at top.
          apply fsuper_vis
            with (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as [K1 K2].
          inversion K1; subst. 
          assert (vis = f3 /\ t0 =  Chan un io t).
          apply in_isMap with (x := (a1, a2)) (g := g1)...
          destruct H12; subst.
          apply fsuper_vis
            with (pf1 := pf4) (pf2 := pf3) (pf := pf1) in H0 as [K3 K4].
          inversion K3; subst.
          assert (vis = f2 /\ t0 =  Chan un io t).
          apply in_isMap with (x := (a1, a2)) (g := g4)...
          destruct H12; subst...
          inversion K4; subst.
          assert (vis = f1 /\ t0 =  Chan un io t).
          apply in_isMap with (x := (a1, a2)) (g := g3)...
          destruct H13; subst.
          all:try eassumption.
          
          
          destruct IHTSPLIT as
            [[ABS UNUSED] | [UN IHTSPLIT]].
          unfold is_unrestricted in ABS.
          elim ABS. exists p. exists r2...

          

          specialize IHLTS2 with
            (nd_pf1 := nd_pf4) (pf2 := pfw3) (pf := pf0').
          
          apply IHLTS2 in IHTSPLIT.
          destruct IHTSPLIT as [k4 LTSIN].

          assert (LEM2:
                   exists r4,
                     type_plus s4 t r4).
          
          apply plus_sub_exists with (s := s3) (r := s')...

          destruct LEM1 as [r3 TREM].
          destruct LEM2 as [r4 TPLUS].

          specialize split_exists_remove_l with
            g3 g4 g1 pf3 pf4 pf1 b1 b2 vis t s3 r3 as EXREM.
          apply EXREM in T3b as TYP3'. clear EXREM.
          destruct TYP3' as [s'' [r'' [TYP1' TREM1]]].
          inversion TYP1'; subst.
          apply fsuper_vis with (pf1 := pf1) (pf2 := pf2) (pf := pf) in H1 as Q1.
          destruct Q1 as [Q1 Q2]; inversion Q1; subst.
          assert (vis = f1 /\ t0 =s'').
          apply in_isMap with (x := (b1, b2)) (g := g1)...
          destruct H15; subst. 
          assert(nd_pfw1 :
                  NoDup(domain
                          ( (b1, b2, vis, s'') ::
                              (removeEntry (b1, b2) g1)))).
          apply no_dup_cons_removeEntry...
          assert (nd_pfw2 :
                   NoDup(domain
                           ( (b1, b2, vis, r'')
                               :: 
                               (removeEntry (b1, b2) g1)))).
          apply no_dup_cons_removeEntry...

          move LTS2 at bottom.
          apply lts_un_input_action
            with (pol := io) (t := t) (s := s1) (r := s)
            in LTS2 as Heqgg3.
          destruct Heqgg3 as (kk3 &DIS3  &Heqgg3).
          rewrite Heqgg3 in LTS2.
          
          unfold g' in LTS2. unfold g0 in LTS2.
          apply lts_type_plus_un_in with
            (a1 := a1) (a2 := a2) (t := t) (b1 := b1) (b2 := b2)
            (f := vis) (f1 := vis) (pol := io)
            (s01 := r'') (s := s) (s1 := s1) (s0 := s'')
            (pf1 := nd_pfw2)
            in LTS2 as UNIN.
          destruct UNIN as [kk1 UNIN].

          
          exists (kk1 ++
                    (b1, b2, vis, s'')
                    :: removeEntry (b1, b2) ((b1, b2, vis, r'') :: removeEntry (b1, b2) g1)).
          apply ucomL with
            (s1 := r'') (s := s'') (t := t)(pf1 := nd_pf1) (pf2 := nd_pfw2).
          
          eauto.
          eauto.
          eauto.            
          
          specialize lts_type_remove_un_out with
            (a1 := a1) (a2 := a2) (t := t) (b1 := b1) (b2 := b2)
            (f := vis) (f1 := vis)
            (s01 := r'') (s := s3) (s1 := r3) (s0 := s'')
            (pol := io)
            (pf := nd_pf3) (pf1 := nd_pf1)
            as UNOUT.
          
          assert (Heqk1:
                   k1 =  ( (b1, b2, vis, r3) :: (removeEntry (b1, b2) g3))).

          apply lts_un_output_action with
            (p := p1) (p' := p2) (nd_pf := nd_pf3)
            (pol := io) (s := s3)
            (a1 := a1) (a2 := a2) (t:= t)...
          
          rewrite <-Heqk1 in UNOUT.

          apply UNOUT in LTSOUT as IH.
          eauto.
          eauto.
          eauto.
          eauto.
          eauto.
          eauto.
          eauto.

           eapply typeCheck_no_dup with (pf := pf3)...
          assert (INCL: incl (secLabs p1) (domain (hid_proj g3))).
          eapply typeCheck_hid_proj with (pf := pf3)...
          assert (INCL2: incl (domain (hid_proj g3))(domain (hid_proj g1))).
          eapply split_incl_hid_proj...
          eapply incl_tran...
          eauto.

          apply in_app_iff with (l := kk1).
          right.
          apply in_app_iff with (l := (b1, b2, vis, s'') :: nil).
          right.
          apply removeEntry_in.
          eauto.
          apply in_app_iff with (l := (b1, b2, vis, r'') :: nil).
          right.
          apply removeEntry_in...
          apply in_app_iff with (l := kk1). right...
          apply in_app_iff with (l := (b1, b2, vis, s1) :: nil).
          right. apply removeEntry_in...
          eauto.
          eauto.
          inversion TREM1.
          destruct H16 as [TP ISUN]; apply type_plus_comm...
          discriminate.
          apply in_app_iff with (l := (b1, b2, vis, r'') :: nil).
          right. apply removeEntry_in...
          eauto.
          
          apply split_removeEntry_domain_2 with
            (pf1 := pf1) (pf2 := pf2) (pf := pf)...

          eapply typeCheck_no_dup with (pf := pf4)...
          simpl.
          introv IN.
          assert (a <> (b1, b2)).
          intros ABS; subst a.
          eapply type_checking_0.typeCheck_hid with (n := (b1, b2)) in H8 as (tt &K).
          assert (ABS: vis = hid /\ s4 = tt)...
          destruct ABS; try discriminate...
          assumption.
          rewrite <-hid_proj_removeEntry.
          assert (INCL: incl (secLabs q1) (domain (hid_proj g4))).
          eapply typeCheck_hid_proj with (pf := pf4)...
          assert (INCL2: incl (domain (hid_proj g4))(domain (hid_proj g1))).
          eapply split_incl_hid_proj...
          eapply INCL,INCL2,in_domain_in_g in IN.
          destruct IN as (ff &tt &IN).
          eapply in_g_in_domain,removeEntry_in...

          
          assert (In (a1, a2, vis, (Chan un io t)) g').
          unfold g'. unfold g0.
          apply in_app_iff with (l := (b1, b2, vis, s1) :: nil).
          right. apply removeEntry_in...
          eauto.
          eauto.
          subst g' g0; econstructor; right; eapply removeEntry_in...
          subst g' g0; econstructor...
          inversion H. destruct H16 as [TPLUSS ISUN]; apply type_plus_comm...
          all:try eassumption.
           eapply sl_pos_par_r...

          subst g' g0; try  erewrite <-max_removeEntry_cons;
            try eapply in_g_in_domain;
            try eapply incl_preserves_max...
          assert (IN4: incl (secLabs q1) (domain g4)).
          try eapply typeCheck_no_dup with (pf := pf4)...
          introv IN';erewrite <-split_domain_l...

           eapply sl_pos_par_r...
      ***
        assert (TOP: s = Top /\ t = Top /\ s1 = Top /\ s3 = Top /\ s4 = Top /\ s' = Top).
        inversion IHPREQ; subst.
        inversion TPLUS1; subst.
        inversion TYP3; subst.
        inversion TYP1; subst. intuition.
        
        assert (TYPa := H0).
        inversion TYP2; subst.
        apply tsuper_payload with
          (pf1 := pf4) (pf2 := pfw) (pf := pf) in H0 as K0.
        destruct K0 as [q4 TYP4]. inversion TYP4; subst.
        inversion TYP'; subst. 
        assert (q4 = q'' /\ q'' = q').
        apply split_plus_un with
          (pf1 := pf4) (pf2 := pf3) (pf3 := pf1) (b1 := a1) (b2 := a2) (t := t) (f1 := f2) (f2 := f1) (f3 := f3)...
        destruct H11; subst.
        apply tsuper_payload_r with
          (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as K0.
        destruct K0 as [q'' TYP2']. inversion TYP2'; subst.
        assert (q' = q'' /\ q'' = io).
        apply split_plus_un with
          (pf1 := pf1) (pf2 := pf2) (pf3 := pf) (b1 := a1) (b2 := a2) (t := t) (f1 := f3) (f2 := f4) (f3 := vis)...
        destruct H12; subst.
        
        move g2 at top.
        apply fsuper_vis
          with (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as [K1 K2].
        inversion K1; subst. 
        assert (vis = f3 /\ t0 =  Chan un io t).
        apply in_isMap with (x := (a1, a2)) (g := g1)...
        destruct H12; subst.
        apply fsuper_vis
          with (pf1 := pf4) (pf2 := pf3) (pf := pf1) in H0 as [K3 K4].
        inversion K3; subst.
        assert (vis = f2 /\ t0 =  Chan un io t).
        apply in_isMap with (x := (a1, a2)) (g := g4)...
        destruct H12; subst...
        inversion K4; subst.
        assert (vis = f1 /\ t0 =  Chan un io t).
        apply in_isMap with (x := (a1, a2)) (g := g3)...
        destruct H13; subst.
        all:try eassumption.

        destruct IHTSPLIT as
          [[NOTUN IHTSPLIT] | ABS].
        specialize IHLTS2 with
          (nd_pf1 := nd_pf4) (pf2 := pfw2) (pf := pf0').
        apply IHLTS2 in IHTSPLIT.
        destruct IHTSPLIT as [k4 LTSIN].
        
        assert(nd_pfw1 :
                NoDup(domain
                        ( (b1, b2, vis, Top)
                            :: 
                            (removeEntry (b1, b2) g1)))).
        apply no_dup_cons_removeEntry...
        assert (nd_pfw2 :
                 NoDup(domain
                         ( (b1, b2, vis, Top)
                             :: 
                             (removeEntry (b1, b2) g1)))).
        apply no_dup_cons_removeEntry...

        apply lts_un_input_action
          with (pol := io) (t := t) (s := s1) (r := s)
          in LTS2 as Heqgg3.
        destruct Heqgg3 as (kk3 &DIS3  &Heqgg3).
        rewrite Heqgg3 in LTS2.

        
        
        unfold g' in LTS2. unfold g0 in LTS2.
        apply lts_type_plus_un_in with
          (a1 := a1) (a2 := a2) (t := t) (b1 := b1) (b2 := b2)
          (f := vis) (f1 := vis) (pol := io)
          (s01 := Top) (s := s) (s1 := s1) (s0 := Top)
          (pf1 := nd_pfw2)
          in LTS2 as UNIN.
        destruct UNIN as [kk1 UNIN].

        
        exists (kk1 ++
                  (b1, b2, vis, Top)
                  :: removeEntry (b1, b2) ((b1, b2, vis, Top) :: removeEntry (b1, b2) g1)).
        apply ucomL with
          (s1 := Top) (s := Top) (t := t)(pf1 := nd_pf1) (pf2 := nd_pfw2).
        intuition; subst...
        eauto.
        inversion IN1; subst.
        apply fsuper_vis with (pf1 := pf1) (pf2 := pf2) (pf := pf) in H1 as Q1.
        destruct Q1 as [Q1 Q2]; inversion Q1; subst.
        assert (vis = f1 /\ t0 = s').
        apply in_isMap with (x := (b1, b2)) (g := g1)...
        destruct H15; subst.
        intuition; subst...
        eauto.            
        
        specialize lts_type_remove_un_out with
          (a1 := a1) (a2 := a2) (t := t) (b1 := b1) (b2 := b2)
          (f := vis) (f1 := vis)
          (s01 := Top) (s := s3) (s1 := Top) (s0 := Top)
          (pol := io)
          (pf := nd_pf3) (pf1 := nd_pf1)
          as UNOUT.
        
        assert (Heqk1:
                 k1 =  ( (b1, b2, vis, Top) :: (removeEntry (b1, b2) g3))).

        apply lts_un_output_action with
          (p := p1) (p' := p2) (nd_pf := nd_pf3)
          (pol := io) (s := s3)
          (a1 := a1) (a2 := a2) (t:= t)...
        intuition; subst...
        
        rewrite <-Heqk1 in UNOUT.

        apply UNOUT in LTSOUT as IH.
        eauto.
        eauto.
        eauto.
        intuition; subst...
        eauto.
        inversion IN1; subst.
        apply fsuper_vis with (pf1 := pf1) (pf2 := pf2) (pf := pf) in H1 as Q1.
        destruct Q1 as [Q1 Q2]; inversion Q1; subst.
        assert (vis = f1 /\ t0 = s').
        apply in_isMap with (x := (b1, b2)) (g := g1)...
        destruct H15; subst.
        intuition; subst...
        eauto.  
        eauto.

          eapply typeCheck_no_dup with (pf := pf3)...
          simpl.
          introv IN.
 
          assert (INCL: incl (secLabs p1) (domain (hid_proj g3))).
          eapply typeCheck_hid_proj with (pf := pf3)...
          assert (INCL2: incl (domain (hid_proj g3))(domain (hid_proj g1))).
          eapply split_incl_hid_proj...
          eauto.
          eauto.

        
        apply in_app_iff with (l := kk1).
        right.
        apply in_app_iff with (l := (b1, b2, vis, Top) :: nil).
        right.
        apply removeEntry_in.
        eauto.
        apply in_app_iff with (l := (b1, b2, vis, Top) :: nil).
        right.
        apply removeEntry_in...
        apply in_app_iff with (l := kk1). right...
        apply in_app_iff with (l := (b1, b2, vis, s1) :: nil).
        right. apply removeEntry_in...
        eauto.
        intuition; subst...
        discriminate.
        apply in_app_iff with (l := (b1, b2, vis, Top) :: nil).
        right. apply removeEntry_in...
        eauto.
        
        apply split_removeEntry_domain_2 with
          (pf1 := pf1) (pf2 := pf2) (pf := pf)...
        assert (In (a1, a2, vis, (Chan un io t)) g').
        unfold g'. unfold g0.
        apply in_app_iff with (l := (b1, b2, vis, s1) :: nil).
        right. apply removeEntry_in...

          eapply typeCheck_no_dup with (pf := pf4)...
          simpl.
          introv IN.
          assert (a <> (b1, b2)).
          intros ABS; subst a.
          eapply type_checking_0.typeCheck_hid with (n := (b1, b2)) in H8 as (tt &K).
          assert (ABS: vis = hid /\ s4 = tt)...
          destruct ABS; try discriminate...
          assumption.
          rewrite <-hid_proj_removeEntry.
          assert (INCL: incl (secLabs q1) (domain (hid_proj g4))).
          eapply typeCheck_hid_proj with (pf := pf4)...
          assert (INCL2: incl (domain (hid_proj g4))(domain (hid_proj g1))).
          eapply split_incl_hid_proj...
          eapply INCL,INCL2,in_domain_in_g in IN.
          destruct IN as (ff &tt &IN).
          eapply in_g_in_domain,removeEntry_in...
        
          eauto.
          eauto.
        subst g' g0; econstructor;  right; try eapply removeEntry_in...
        subst g' g0; econstructor...
        inversion H. destruct H14 as [TPLUSS ISUN]; apply type_plus_comm...
        all:try eassumption.
         eapply sl_pos_par_r...

         subst g' g0; try  erewrite <-max_removeEntry_cons;
            try eapply in_g_in_domain;
            try eapply incl_preserves_max...
          assert (IN4: incl (secLabs q1) (domain g4)).
          try eapply typeCheck_no_dup with (pf := pf4)...
          introv IN';erewrite <-split_domain_l...

           eapply sl_pos_par_r...
        
        unfold is_unrestricted in ABS.
        destruct ABS as [ABS1 ABS2].
        destruct ABS1 as [p0 [t0 ABS1]];inversion ABS1...
      *** eauto.
      ***  eapply sl_pos_par_l...
    * eauto.
    * eauto.    

      
  - Case uclsL.
    intros.
    remember g3 as gg3; subst g3.
    inversion TCHECK; subst.
    remember pf0 as nd_pf; subst pf0.
    remember pf1 as nd_pf0; subst pf1.
    remember pf2 as nd_pf0'; subst pf2.
    remember pf4 as pf1; subst pf4.
    remember pf3 as pf2; subst pf3.
    remember pf5 as pf3; subst pf5.
    remember pf6 as pf4; subst pf6.
    
    assert (TSPLIT2 := H6); clear H6.
    

    apply split_of_split with
      g3 g4 g1 g2 g pf3 pf4 pf1 pf2 pf
      in TSPLIT2 as TSPLIT3.
    destruct TSPLIT3 as [h [pfh TSPLIT3]].
    
    * apply no_dup_split_no_dup_l in TSPLIT3 as nd_pf3.
      specialize IHLTS1 with (pf1 := pf3) (pf2 := pfh) (pf := pf) (nd_pf1 := nd_pf3).
      apply IHLTS1 in TSPLIT3 as SPLITOUT.
      destruct SPLITOUT as [k1 LTSOUT].

      apply split_comm in TSPLIT2 as TSPLIT4. 
      apply split_of_split with
        g4 g3 g1 g2 g pf4 pf3 pf1 pf2 pf
        in TSPLIT4 as TSPLIT5.
      destruct TSPLIT5 as [w [pfw TSPLIT5]].
      (* TSPLIT5 : tEnv_split g4 w g pf4 pfw pf *)

      specialize IHLTS2 with (pf1 := pf4).
      
      
      assert (T3b : exists s3,
                 In (b1, b2, hid, s3) g3).
      specialize fsuper_hid with g3 h g pf3 pfh pf (b1, b2) s as FVIS.
      
      
      apply FVIS in TSPLIT3 as FVIS3. clear FVIS.
      assert (FHIDVIS3 : flagOf g3 (b1, b2) vis \/
                           flagOf g3 (b1, b2) hid).
      apply typeCheck_lts_out_payload with
        (pf1 := pf3) (nd_pf := nd_pf3)
        (a1 := a1) (a2 := a2) (b1 := b1) (b2 := b2)
        (g' := k1) (p:= p1) (p' := p2)...
      specialize flag_of_split_l with g3 h g pf3 pfh pf (b1, b2) as FSL.
      apply FSL in TSPLIT3 as [FHID [FVIS FILL]]. clear FSL.
      destruct FVIS3 as [FHID3 | ABS].
      destruct FHID3. inversion H4; subst.
      exists t0...
      destruct ABS. intuition.
      inversion H11. subst. 
      assert (ill = hid /\ t0 = s).
      apply in_isMap with (x := (b1, b2)) (g := g)...
      destruct H14; discriminate.
      inversion H13. subst. 
      assert (vis = hid /\ t0 = s).
      apply in_isMap with (x := (b1, b2)) (g := g)...
      destruct H14; discriminate.
      inversion H6; exists t0...
      inversion H6; exists t0...
      eauto.
      
      
      destruct T3b as [s3 T3b].
      
      apply tsuper_payload with
        (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as K0.
      destruct K0 as [q' TYP']; inversion TYP'; subst.
      apply tsuper_payload with
        (pf1 := pf3) (pf2 := pf4) (pf := pf1) in H4 as K2.
      destruct K2 as [q'' TYP2]; inversion TYP2; subst.
      assert (LEM1:
               exists r3,
                 type_remove s3 t r3)...
      assert (T4b : exists s4,
                 In (b1, b2, ill, s4) g4).
      specialize flag_of_split_l with g3 g4 g1 pf3 pf4 pf1 (b1, b2) as FSL. intuition.
      assert (F3: flagOf g3 (b1, b2) hid ).
      apply F_Entry in T3b...
      apply H9 in F3. destruct F3 as [ILL  UNUSED].
      inversion ILL.
      exists t0...

      
      
      destruct T4b as [s4 T4b].
      
      assert (TYPw : exists sw, In ((b1, b2), hid, sw) w /\
                                  type_plus s4 sw s).
      specialize split_type_plus with
        g4 w g pf4 pfw pf (b1, b2) s4 s as TP1.
      assert (TYP4: typeOf g4 (b1, b2) s4)...
      apply TP1 in TYP4. clear TP1.
      destruct TYP4 as [t2 [INw TP4]].
      exists t2.
      inversion INw; subst.
      apply fsub_ill with
        (pf1 := pf4) (pf2 := pfw) (pf := pf) in T4b as FYP.
      inversion FYP; subst.
      apply fsuper_hid with
        (pf1 := pf4) (pf2 := pfw) (pf := pf) in H1 as FYP2.
      destruct FYP2 as [ABS | [FYP4 FYPw]].
      destruct ABS as [ABS UNUSED].
      inversion ABS; subst. 
      assert (hid = ill /\ t0 = s4).
      apply in_isMap with (x := (b1, b2)) (g := g4)...
      inversion H11; discriminate.
      inversion FYPw; subst.
      assert (f1 = hid /\ t2 = t0).
      apply in_isMap with (x := (b1, b2)) (g := w)...
      destruct H11; subst...
      eauto.

      apply fsuper_hid with
        (pf1 := pf4) (pf2 := pfw) (pf := pf) in H1 as FYP2.
      destruct FYP2 as [ABS | [FYP4 FYPw]].
      destruct ABS as [ABS UNUSED].
      inversion ABS; subst. 
      assert (hid = ill /\ t0 = s4).
      apply in_isMap with (x := (b1, b2)) (g := g4)...
      inversion H11; discriminate.
      inversion FYPw; subst.
      assert (f1 = hid /\ t2 = t0).
      apply in_isMap with (x := (b1, b2)) (g := w)...
      destruct H11; subst...
      all:try eassumption.
      eauto.
      
      
      assert (nd_pf4 : NoDup(domain g4)).
      apply no_dup_split_no_dup_l with
        (pf1 := pf4) (pf2 := pfw) (pf := pf)
        in nd_pf as nd_pf4...
      specialize split_type_plus_r with
        g4 g3 g1 pf4 pf3 pf1 (b1, b2) s4 s3 as TP1...
      assert (TYP4: typeOf g4 (b1, b2) s4)...
      apply TP1 in TYP4. clear TP1.
      destruct TYP4 as [s' [IN1 TPLUS1]].
      assert (TYP3: type_sub t s3).
      destruct LEM1 as [r3 TREM].
      assert (TREM2 := TREM); inversion TREM2...
      assert (TYP1 : type_sub s' s)...
      
      assert (IHPREQ : exists r2, type_plus s4 r2 s1).
      apply type_plus_exists with
        (s := s) (t := t) (s3 := s3) (s' := s')...
      destruct IHPREQ as [r2 IHPREQ].
      remember ( (b1, b2, ill, r2)
                   :: removeEntry (b1, b2) w) as w2. 
      assert (pfw2 : isMap w2). rewrite Heqw2.
      apply cons_removeEntry;
        try eapply no_dup_split_no_dup_r in nd_pf...
      remember ((b1, b2, ill, s4)
                  :: removeEntry (b1, b2) w) as w3. 
      assert (pfw3 : isMap w3). rewrite Heqw3. 
      apply cons_removeEntry;
        try eapply no_dup_split_no_dup_r in nd_pf...
      assert (pf0' :
               isMap ( (b1, b2, ill, s1) :: g0)).
      apply cons_removeEntry...
      assert (IHTSPLIT:
               (~is_unrestricted r2 /\ tEnv_split g4 w2 ((b1, b2, ill, s1) :: g0) pf4 pfw2 pf0') \/ 
                 (is_unrestricted r2 /\ tEnv_split g4 w3 ((b1, b2, ill, s1) :: g0) pf4 pfw3 pf0')).
      destruct s1. inversion IHPREQ. subst.
      assert (pf' : isMap (removeEntry (b1, b2) g4)).
      apply isMap_removeEntry...
      assert (pf'' : isMap (removeEntry (b1, b2) ( (b1, b2, ill, Chan lin p3 s1) ::  (removeEntry (b1, b2) w)))).
      apply isMap_removeEntry...
      assert (pf''' : isMap (removeEntry (b1, b2) ((b1, b2, ill, Chan lin p s1) :: g0))).
      apply isMap_removeEntry...

      left.
      split. unfold is_unrestricted. intro ABS.
      destruct ABS as [p9 [t9 ABS]]; inversion ABS.
      apply SpLin with
        (n := (b1, b2)) (f := ill) (g := ill) (f' := ill)
        (p := p0) (q := p3) (p' := p) (t := s1)
        (pf' := pf') (pf'' := pf'') (pf''' := pf''').
      all:try eassumption.
      eauto.
      eauto.
      
      (*  tEnv_split (removeEntry (b1, b2) g4)
    (removeEntry (b1, b2) ((b1, b2, ill, Chan lin p3 s1) :: removeEntry (b1, b2) w))
    (removeEntry (b1, b2) ((b1, b2, ill, Chan lin p s1) :: g0)) pf' pf'' pf''' *)
      apply split_remove with
        (pf1 :=  pf4) (pf2 := pfw2) (pf3 := pf0').
      eauto. 
      apply no_dup_cons_removeEntry;
        try eapply no_dup_split_no_dup_r in nd_pf...
      subst g0. apply no_dup_cons_removeEntry...
      apply split_new_un_lin with
        (pf1 := pf4) (pf2 := pfw) (pf := pf)
        (a1 := a1) (a2 := a2) (t := t)
        (f := vis) (p := io) (h1 := ill) (q1 := p0).
      eauto. eauto.
      inversion TYP2; subst. 
      apply tsuper_payload with
        (pf1 := pf4) (pf2 := pfw) (pf := pf) in H0 as K0.
      destruct K0 as [q4 TYP4]. inversion TYP4; subst.
      inversion TYP'; subst. 
      assert (q4 = q'' /\ q'' = q').
      apply split_plus_un with
        (pf1 := pf4) (pf2 := pf3) (pf3 := pf1) (b1 := a1) (b2 := a2) (t := t) (f1 := f2) (f2 := f1) (f3 := f3)...
      destruct H12; subst.
      apply tsuper_payload_r with
        (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as K0.
      destruct K0 as [q'' TYP2']. inversion TYP2'; subst.
      assert (q' = q'' /\ q'' = io).
      apply split_plus_un with
        (pf1 := pf1) (pf2 := pf2) (pf3 := pf) (b1 := a1) (b2 := a2) (t := t) (f1 := f3) (f2 := f4) (f3 := vis)...
      destruct H13; subst.
      
      move g2 at top.
      apply fsuper_vis
        with (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as [K1 K2].
      inversion K1; subst. 
      assert (vis = f3 /\ t0 =  Chan un io t).
      apply in_isMap with (x := (a1, a2)) (g := g1)...
      destruct H13; subst.
      apply fsuper_vis
        with (pf1 := pf4) (pf2 := pf3) (pf := pf1) in H0 as [K3 K4].
      inversion K3; subst.
      assert (vis = f2 /\ t0 = Chan un io t).
      apply in_isMap with (x := (a1, a2)) (g := g4)...
      destruct H13; subst...
      all:try eassumption.
      eauto.
      eauto.
      tauto.
      eauto.
      eauto.
      
      right. split. unfold is_unrestricted.
      exists p3. exists s1...
      assert (ISUNS: is_unrestricted s).
      subst.  inversion TPLUS1. subst. inversion TYP1...
      subst. 
      inversion H. destruct H9 as [TPS ISUN].
      apply ISUN in ISUNS as ISUN2. subst s. clear ISUN.
      apply tsuper_payload with
        (pf1 := pf1) (pf2 := pf2) (pf := pf) in H1 as K1.
      apply tsuper_payload_r with
        (pf1 := pf1) (pf2 := pf2) (pf := pf) in H1 as K2.
      destruct K1 as [pol1 TB1]. destruct K2 as [pol2 TB2].
      inversion TB1. inversion TB2. subst.
      assert (pol1 = pol2 /\ pol2 = (pol_cup p0 p3)).
      apply split_plus_un with
        (pf1 := pf1) (pf2 := pf2) (pf3 := pf)
        (b1 := b1) (b2 := b2) (t := s1)
        (f1 := f1) (f2 := f2) (f3 := hid)...
      destruct H10; subst.
      apply tsuper_payload_r with
        (pf1 := pf4) (pf2 := pf3) (pf := pf1) in H9 as K7.
      destruct K7 as [pol7 TB3]. inversion TB3; subst. 
      assert (p0 = pol7 /\ pol7 = (pol_cup p0 p3)).
      apply split_plus_un with
        (pf1 := pf4) (pf2 := pf3) (pf3 := pf1)
        (b1 := b1) (b2 := b2) (t := s1)
        (f1 := ill) (f2 := f3) (f3 := f1)...
      destruct H11. assert (POLEQ: p0 = pol_cup p0 p3).
      transitivity pol7...
      revert dependent pf0'.
      rewrite <-POLEQ.
      intros.
      assert (pf' : isMap (removeEntry (b1, b2) g4)).
      apply isMap_removeEntry...
      assert (pf'' : isMap (removeEntry (b1, b2) ( (b1, b2, ill, Chan un p0 s1) ::  (removeEntry (b1, b2) w)))).
      apply isMap_removeEntry...
      assert (pf''' : isMap (removeEntry (b1, b2) ( (b1, b2, ill, Chan un p0 s1) :: g0))).
      apply isMap_removeEntry...
      apply SpUn with
        (n := (b1, b2)) (f := ill) (g := ill) (f' := ill)
        (p := p0) (t := s1)
        (pf' := pf') (pf'' := pf'') (pf''' := pf''').
      eauto.
      eauto.
      eauto.
      (*tEnv_split (removeEntry (b1, b2) g4)
    (removeEntry (b1, b2) ((b1, b2, ill, Chan un p0 s1) :: removeEntry (b1, b2) w))
    (removeEntry (b1, b2) ((b1, b2, ill, Chan un p0 s1) :: g0)) pf' pf'' pf'''*)
      assert (pf0'' : isMap
                        ((b1, b2, ill, Chan un p0 s1) :: g0)).
      subst...
      apply split_remove with
        (pf1 :=  pf4) (pf2 := pfw3) (pf3 := pf0'').
      eauto.  apply no_dup_cons_removeEntry;
        try eapply no_dup_split_no_dup_r in nd_pf...
      subst g0. apply no_dup_cons_removeEntry...
      (* tEnv_split g4 ((b1, b2, ill, Chan un p0 s1) :: removeEntry (b1, b2) w)
    ((b1, b2, ill, Chan un p0 s1) :: g0) pf4 pfw3 pf0''*)
      apply split_new_un_un with
        (pf1 := pf4) (pf2 := pfw) (pf := pf)
        (a1 := a1) (a2 := a2) (t := t)
        (f := vis) (p := io) (h1 := ill) (q := p0).
      eauto. eauto.
      
      inversion TYP2; subst.
      apply tsuper_payload with
        (pf1 := pf4) (pf2 := pfw) (pf := pf) in H0 as K0.
      destruct K0 as [q4 TYP4]. inversion TYP4; subst.
      inversion TYP'; subst. 
      assert (q4 = q'' /\ q'' = q').
      apply split_plus_un with
        (pf1 := pf4) (pf2 := pf3) (pf3 := pf1) (b1 := a1) (b2 := a2) (t := t) (f1 := f5) (f2 := f4) (f3 := f6)...
      destruct H16; subst.
      apply tsuper_payload_r with
        (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as K0.
      destruct K0 as [q'' TYP2']. inversion TYP2'; subst.
      assert (q' = q'' /\ q'' = io).
      apply split_plus_un with
        (pf1 := pf1) (pf2 := pf2) (pf3 := pf) (b1 := a1) (b2 := a2) (t := t) (f1 := f6) (f2 := f7) (f3 := vis)...
      destruct H17; subst.
      
      move g2 at top.
      apply fsuper_vis
        with (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as [K1 K2].
      inversion K1; subst. 
      assert (vis = f6 /\ t0 =  Chan un io t).
      apply in_isMap with (x := (a1, a2)) (g := g1)...
      destruct H17; subst.
      apply fsuper_vis
        with (pf1 := pf4) (pf2 := pf3) (pf := pf1) in H0 as [K3 K4].
      inversion K3; subst.
      assert (vis = f5 /\ t0 =  Chan un io t).
      apply in_isMap with (x := (a1, a2)) (g := g4)...
      destruct H17; subst...
      all:try eassumption.
      eauto.
      eauto.
      tauto.
      eauto.
      eauto.
      
      left. split. 
      unfold is_unrestricted. intro ABS.
      inversion IHPREQ; subst. 
      destruct ABS as [p9 [t9 ABS]]; inversion ABS.
      inversion IHPREQ; subst.
      assert (pf' : isMap (removeEntry (b1, b2) g4)).
      apply isMap_removeEntry...
      assert (pf'' : isMap (removeEntry (b1, b2) ((b1, b2, ill, Top) :: (removeEntry (b1, b2) w)))).
      apply isMap_removeEntry...
      assert (pf''' : isMap (removeEntry (b1, b2) ( (b1, b2, ill, Top) :: g0))).
      apply isMap_removeEntry...
      apply SpTop with
        (n := (b1, b2)) (f := ill) (g := ill) (f' := ill)
        
        (pf' := pf') (pf'' := pf'') (pf''' := pf''').
      all:try eassumption.
      eauto.
      eauto.
      
      (*tEnv_split (removeEntry (b1, b2) g4)
    (removeEntry (b1, b2) ((b1, b2, ill, Top) :: removeEntry (b1, b2) w))
    (removeEntry (b1, b2) ((b1, b2, ill, Top) :: g0)) pf' pf'' pf'''*)
      assert (pf0'' : isMap
                        (( (b1, b2, ill, Top) :: g0))).
      subst...
      apply split_remove with
        (pf1 :=  pf4) (pf2 := pfw3) (pf3 := pf0'').
      eauto. 
      apply no_dup_cons_removeEntry;
        try eapply no_dup_split_no_dup_r in nd_pf...
      subst g0. apply no_dup_cons_removeEntry...
      
      apply split_new_un_top with
        (pf1 := pf4) (pf2 := pfw) (pf := pf)
        (a1 := a1) (a2 := a2) (t := t)
        (f := vis) (p := io) (h1 := ill).
      eauto. eauto.

      inversion TYP2; subst.
      apply tsuper_payload with
        (pf1 := pf4) (pf2 := pfw) (pf := pf) in H0 as K0.
      destruct K0 as [q4 TYP4]. inversion TYP4; subst.
      inversion TYP'; subst. 
      assert (q4 = q'' /\ q'' = q').
      apply split_plus_un with
        (pf1 := pf4) (pf2 := pf3) (pf3 := pf1) (b1 := a1) (b2 := a2) (t := t) (f1 := f2) (f2 := f1) (f3 := f3)...
      destruct H11; subst.
      apply tsuper_payload_r with
        (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as K0.
      destruct K0 as [q'' TYP2']. inversion TYP2'; subst.
      assert (q' = q'' /\ q'' = io).
      apply split_plus_un with
        (pf1 := pf1) (pf2 := pf2) (pf3 := pf) (b1 := a1) (b2 := a2) (t := t) (f1 := f3) (f2 := f4) (f3 := vis)...
      destruct H12; subst.
      
      move g2 at top.
      apply fsuper_vis
        with (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as [K1 K2].
      inversion K1; subst. 
      assert (vis = f3 /\ t0 =  Chan un io t).
      apply in_isMap with (x := (a1, a2)) (g := g1)...
      destruct H12; subst.
      apply fsuper_vis
        with (pf1 := pf4) (pf2 := pf3) (pf := pf1) in H0 as [K3 K4].
      inversion K3; subst.
      assert (vis = f2 /\ t0 =  Chan un io t).
      apply in_isMap with (x := (a1, a2)) (g := g4)...
      destruct H12; subst...
      all:try eassumption.
      eauto.
      eauto.
      tauto.
      eauto.
      eauto.

      
      destruct r2.
      ***
        destruct m.
        (*  ~ is_unrestricted (Chan lin p r2) *)
        ****
          assert (TYPa := H0).
          inversion TYP2; subst.
          apply tsuper_payload with
            (pf1 := pf4) (pf2 := pfw) (pf := pf) in H0 as K0.
          destruct K0 as [q4 TYP4]. inversion TYP4; subst.
          inversion TYP'; subst. 
          assert (q4 = q'' /\ q'' = q').
          apply split_plus_un with
            (pf1 := pf4) (pf2 := pf3) (pf3 := pf1) (b1 := a1) (b2 := a2) (t := t) (f1 := f2) (f2 := f1) (f3 := f3)...
          destruct H11; subst.
          apply tsuper_payload_r with
            (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as K0.
          destruct K0 as [q'' TYP2']. inversion TYP2'; subst.
          assert (q' = q'' /\ q'' = io).
          apply split_plus_un with
            (pf1 := pf1) (pf2 := pf2) (pf3 := pf) (b1 := a1) (b2 := a2) (t := t) (f1 := f3) (f2 := f4) (f3 := vis)...
          destruct H12; subst.
          
          move g2 at top.
          apply fsuper_vis
            with (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as [K1 K2].
          inversion K1; subst. 
          assert (vis = f3 /\ t0 =  Chan un io t).
          apply in_isMap with (x := (a1, a2)) (g := g1)...
          destruct H12; subst.
          apply fsuper_vis
            with (pf1 := pf4) (pf2 := pf3) (pf := pf1) in H0 as [K3 K4].
          inversion K3; subst.
          assert (vis = f2 /\ t0 =  Chan un io t).
          apply in_isMap with (x := (a1, a2)) (g := g4)...
          destruct H12; subst...
          inversion K4; subst.
          assert (vis = f1 /\ t0 =  Chan un io t).
          apply in_isMap with (x := (a1, a2)) (g := g3)...
          destruct H13; subst.
          all:try eassumption.
          
          
          
          destruct IHTSPLIT as
            [[NOTUN IHTSPLIT] | ABS].
          specialize IHLTS2 with
            (nd_pf1 := nd_pf4) (pf2 := pfw2) (pf := pf0').
          
          apply IHLTS2 in IHTSPLIT.
          destruct IHTSPLIT as [k4 LTSIN].
          
          assert (LEM2:
                   exists r4,
                     type_plus s4 t r4).
          apply plus_sub_exists with
            (s := s3) (r := s')...
          
          destruct LEM1 as [r3 TREM].
          destruct LEM2 as [r4 TPLUS].

          specialize split_exists_remove_l with
            g3 g4 g1 pf3 pf4 pf1 b1 b2 hid t s3 r3 as EXREM.
          apply EXREM in T3b as TYP3'. clear EXREM.
          destruct TYP3' as [s'' [r'' [TYP1' TREM1]]].
          inversion TYP1'; subst.
          apply fsuper_hid with (pf1 := pf1) (pf2 := pf2) (pf := pf) in H1 as K5.
          destruct K5 as [[K5 K6] | ABS].
          inversion K5; subst.
          assert (hid = f1 /\ t0 = s'').
          apply in_isMap with (x := (b1, b2)) (g := g1)...
          destruct H15; subst.
          apply lts_un_input_action
            with (pol := io) (t := t) (s := s1) (r := s)
            in LTS2 as Heqgg3.
          destruct Heqgg3 as (kk3 &DIS3  &Heqgg3).
          rewrite Heqgg3 in LTS2.
          
          assert (nd_pfw2 :
                   NoDup(domain
                           ((b1, b2, ill, r'')
                              ::    (removeEntry (b1, b2) g1)))).
          apply no_dup_cons_removeEntry...
          (*specialize  lts_type_plus_un_in with
               (a1 := a1) (a2 := a2) (t := t) (b1 := b1) (b2 := b2)
               (f := vis) (f1 := vis) (pol := io)
               (q1 :=q1 )(q2 :=q2)
                (s01 := s'') (s := s) (s1 := r4) (s0 := r'')
                (pf1 := nd_pfw2) 
                (pf := nd_pf0') (k := kk3)
               as LININ.*)
          unfold g' in LTS2. unfold g0 in LTS2.
          apply lts_type_plus_un_in with
            (a1 := a1) (a2 := a2) (t := t) (b1 := b1) (b2 := b2)
            (f := ill) (f1 := ill) (pol := io)
            (s01 := r'') (s := s) (s1 := s1) (s0 := s'')
            (pf1 := nd_pfw2)
            in LTS2 as UNIN.
          destruct UNIN as [kk1 UNIN].
          move UNIN at bottom.
          

          
          move LTS1 at bottom.
          remember (kk1 ++
                      (b1, b2, vis, s'')
                      :: removeEntry (b1, b2) ((b1, b2, ill, r'') :: removeEntry (b1, b2) g1)) as gk1.
          exists (((b1, b2), hid, s'') :: removeEntry (b1, b2) gk1).
          apply uclsL with
            (s1 := r'') (s := s'') (t := t)(pf1 := nd_pf1) (pf2 := nd_pfw2).
          eauto.
          eauto.
          eauto.

          simple eapply lts_rewrite_pf.
          simple eapply lts_type_remove_un_out.
          exact TYPa.
          exact H1.
          exact LTS1.
          exact TREM1.
          exact H10.
          exact H14.
          
          eauto.

            eapply typeCheck_no_dup with (pf := pf3)...
          simpl.
          introv IN.
 
          assert (INCL: incl (secLabs p1) (domain (hid_proj g3))).
          eapply typeCheck_hid_proj with (pf := pf3)...
          assert (INCL2: incl (domain (hid_proj g3))(domain (hid_proj g1))).
          eapply split_incl_hid_proj...
          eauto.
          eauto.
          
          rewrite   Heqgk1.
          apply in_app_iff with (l := kk1).
          right.
          apply in_app_iff with (l := (b1, b2, vis, s'') :: nil).
          right.
          apply removeEntry_in.
          eauto.
          apply in_app_iff with (l := (b1, b2, ill, r'') :: nil).
          right.
          apply removeEntry_in...
          rewrite   Heqgk1.
          apply in_app_iff with (l := kk1)...
          apply in_app_iff with (l := (b1, b2, ill, s1) :: nil).
          right.
          apply removeEntry_in...
          eauto.
          inversion TREM1.
          destruct H16 as [TP ISUN]; apply type_plus_comm...
          discriminate.
          apply in_app_iff with (l := (b1, b2, ill, r'') :: nil).
          right. apply removeEntry_in...
          eauto.
          
          apply split_removeEntry_domain_2 with
            (pf1 := pf1) (pf2 := pf2) (pf := pf)...
          assert (In (a1, a2, vis, (Chan un io t)) g').
          unfold g'. unfold g0.
          apply in_app_iff with (l := (b1, b2, ill, s1) :: nil).
          right. apply removeEntry_in...

            eapply typeCheck_no_dup with (pf := pf4)...
          simpl.
          introv IN.
 
          assert (INCL: incl (secLabs q1) (domain (hid_proj g4))).
          eapply typeCheck_hid_proj with (pf := pf4)...
          assert (INCL2: incl (domain (hid_proj g4))(domain (hid_proj g1))).
          eapply split_incl_hid_proj...

          assert (IN' := IN).
          assert (INSL: In (b1, b2) (fn p1) \/ In (b1, b2) (secLabs p1)).
            eapply payload_occurs...
            destruct INSL as [ABS | INSL].
            eapply tc_dep_relabel_premises.typeCheck_is_vis in H7 as (tt& ABS2)...
            assert (ABS3: hid = vis /\ s3 = tt)...
            destruct ABS3; try discriminate.
            assert (NIN: ~In (b1, b2) (secLabs q1)).
            intros ABS.
            assert (ND: NoDup (secLabs  (dPar p1 q1))).
            eapply typeCheck_no_dup with (pf := pf1)...
            simpl in ND; eapply no_dup_iff in ND as (ND1 &ND2 &DIS).
            eapply disjoint_absurd...

          assert (a <> (b1, b2)).
          intros ABS; subst a; try contradiction.
          eapply INCL,INCL2 in IN.
          rewrite <-hid_proj_removeEntry...
          eapply in_domain_in_g in IN as (ff &tt &IN);
            try eapply in_g_in_domain, removeEntry_in...

          eauto.

          subst g' g0; econstructor; right; try eapply removeEntry_in...
          subst g' g0; econstructor...
          inversion H. destruct H16 as [TPLUSS ISUN]; apply type_plus_comm...
          all:try eassumption.
           eapply sl_pos_par_r...

           subst g' g0; try  erewrite <-max_removeEntry_cons;
            try eapply in_g_in_domain;
            try eapply incl_preserves_max...
          assert (IN4: incl (secLabs q1) (domain g4)).
          try eapply typeCheck_no_dup with (pf := pf4)...
          introv IN';erewrite <-split_domain_l...

           inversion ABS.
             apply fsub_hid_r with
                 (pf1 := pf4) (pf2 := pf3) (pf := pf1) in T3b as K3b.
             inversion K3b; inversion H14; subst. 
             specialize flag_of_map with g1 (b1, b2) hid ill as ABS2. intuition. discriminate.
             eauto.
              eapply sl_pos_par_r...
          
          unfold is_unrestricted in ABS.
          destruct ABS as [ABS1 ABS2].
          destruct ABS1 as [p0 [t0 ABS1]];inversion ABS1...
        ****
          assert (TYPa := H0).
          inversion TYP2; subst.
          apply tsuper_payload with
            (pf1 := pf4) (pf2 := pfw) (pf := pf) in H0 as K0.
          destruct K0 as [q4 TYP4]. inversion TYP4; subst.
          inversion TYP'; subst. 
          assert (q4 = q'' /\ q'' = q').
          apply split_plus_un with
            (pf1 := pf4) (pf2 := pf3) (pf3 := pf1) (b1 := a1) (b2 := a2) (t := t) (f1 := f2) (f2 := f1) (f3 := f3)...
          destruct H11; subst.
          apply tsuper_payload_r with
            (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as K0.
          destruct K0 as [q'' TYP2']. inversion TYP2'; subst.
          assert (q' = q'' /\ q'' = io).
          apply split_plus_un with
            (pf1 := pf1) (pf2 := pf2) (pf3 := pf) (b1 := a1) (b2 := a2) (t := t) (f1 := f3) (f2 := f4) (f3 := vis)...
          destruct H12; subst.
          
          move g2 at top.
          apply fsuper_vis
            with (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as [K1 K2].
          inversion K1; subst. 
          assert (vis = f3 /\ t0 =  Chan un io t).
          apply in_isMap with (x := (a1, a2)) (g := g1)...
          destruct H12; subst.
          apply fsuper_vis
            with (pf1 := pf4) (pf2 := pf3) (pf := pf1) in H0 as [K3 K4].
          inversion K3; subst.
          assert (vis = f2 /\ t0 =  Chan un io t).
          apply in_isMap with (x := (a1, a2)) (g := g4)...
          destruct H12; subst...
          inversion K4; subst.
          assert (vis = f1 /\ t0 =  Chan un io t).
          apply in_isMap with (x := (a1, a2)) (g := g3)...
          destruct H13; subst.
          all:try eassumption.
          
          
          destruct IHTSPLIT as
            [[ABS UNUSED] | [UN IHTSPLIT]].
          unfold is_unrestricted in ABS.
          elim ABS. exists p. exists r2...

          

          specialize IHLTS2 with
            (nd_pf1 := nd_pf4) (pf2 := pfw3) (pf := pf0').
          
          apply IHLTS2 in IHTSPLIT.
          destruct IHTSPLIT as [k4 LTSIN].

          assert (LEM2:
                   exists r4,
                     type_plus s4 t r4).
          
          apply plus_sub_exists with (s := s3) (r := s')...

          destruct LEM1 as [r3 TREM].
          destruct LEM2 as [r4 TPLUS].

          specialize split_exists_remove_l with
            g3 g4 g1 pf3 pf4 pf1 b1 b2 hid t s3 r3 as EXREM.
          apply EXREM in T3b as TYP3'. clear EXREM.
          destruct TYP3' as [s'' [r'' [TYP1' TREM1]]].
          inversion TYP1'; subst.
          apply fsuper_hid with (pf1 := pf1) (pf2 := pf2) (pf := pf) in H1 as Q1.
          destruct Q1 as [[Q1 Q2] | ABS]. inversion Q1; subst.
          assert (hid = f1 /\ t0 =s'').
          apply in_isMap with (x := (b1, b2)) (g := g1)...
          destruct H15; subst.

          assert (nd_pfw2 :
                   NoDup(domain
                           ( (b1, b2, ill, r'')
                               :: 
                               (removeEntry (b1, b2) g1)))).
          apply no_dup_cons_removeEntry...

          apply lts_un_input_action
            with (pol := io) (t := t) (s := s1) (r := s)
            in LTS2 as Heqgg3.
          destruct Heqgg3 as (kk3 &DIS3  &Heqgg3).
          rewrite Heqgg3 in LTS2.
          
          unfold g' in LTS2. unfold g0 in LTS2.
          apply lts_type_plus_un_in with
            (a1 := a1) (a2 := a2) (t := t) (b1 := b1) (b2 := b2)
            (f := ill) (f1 := ill) (pol := io)
            (s01 := r'') (s := s) (s1 := s1) (s0 := s'')
            (pf1 := nd_pfw2)
            in LTS2 as UNIN.
          destruct UNIN as [kk1 UNIN].


          remember (kk1 ++
                      (b1, b2, vis, s'')
                      :: removeEntry (b1, b2) ((b1, b2, ill, r'') :: removeEntry (b1, b2) g1)) as gk1.
          exists (((b1, b2), hid, s'') :: removeEntry (b1, b2) gk1).
          apply uclsL with
            (s1 := r'') (s := s'') (t := t)(pf1 := nd_pf1) (pf2 := nd_pfw2).
          eauto.
          eauto.
          eauto.            

           simple eapply lts_rewrite_pf.
          simple eapply lts_type_remove_un_out.
          exact TYPa.
          exact H1.
          exact LTS1.
          exact TREM1.
          exact H10.
          exact H14.

          eauto.
          
             eapply typeCheck_no_dup with (pf := pf3)...
          simpl.
          introv IN.
 
          assert (INCL: incl (secLabs p1) (domain (hid_proj g3))).
          eapply typeCheck_hid_proj with (pf := pf3)...
          assert (INCL2: incl (domain (hid_proj g3))(domain (hid_proj g1))).
          eapply split_incl_hid_proj...
          eauto.
          eauto.
          
          rewrite   Heqgk1.
          apply in_app_iff with (l := kk1).
          right.
          apply in_app_iff with (l := (b1, b2, vis, s'') :: nil).
          right.
          apply removeEntry_in.
          eauto.
          apply in_app_iff with (l := (b1, b2, ill, r'') :: nil).
          right.
          apply removeEntry_in...
          rewrite   Heqgk1.
          apply in_app_iff with (l := kk1)...
          apply in_app_iff with (l := (b1, b2, ill, s1) :: nil).
          right.
          apply removeEntry_in...
          eauto.
          inversion TREM1.
          destruct H16 as [TP ISUN]; apply type_plus_comm...
          discriminate.
          apply in_app_iff with (l := (b1, b2, ill, r'') :: nil).
          right. apply removeEntry_in...
          eauto.
          
          apply split_removeEntry_domain_2 with
            (pf1 := pf1) (pf2 := pf2) (pf := pf)...

             eapply typeCheck_no_dup with (pf := pf4)...
          simpl.
          introv IN.
 
          assert (INCL: incl (secLabs q1) (domain (hid_proj g4))).
          eapply typeCheck_hid_proj with (pf := pf4)...
          assert (INCL2: incl (domain (hid_proj g4))(domain (hid_proj g1))).
          eapply split_incl_hid_proj...

          assert (IN' := IN).
          assert (INSL: In (b1, b2) (fn p1) \/ In (b1, b2) (secLabs p1)).
            eapply payload_occurs...
            destruct INSL as [ABS | INSL].
            eapply tc_dep_relabel_premises.typeCheck_is_vis in H7 as (tt& ABS2)...
            assert (ABS3: hid = vis /\ s3 = tt)...
            destruct ABS3; try discriminate.
            assert (NIN: ~In (b1, b2) (secLabs q1)).
            intros ABS.
            assert (ND: NoDup (secLabs  (dPar p1 q1))).
            eapply typeCheck_no_dup with (pf := pf1)...
            simpl in ND; eapply no_dup_iff in ND as (ND1 &ND2 &DIS).
            eapply disjoint_absurd...

          assert (a <> (b1, b2)).
          intros ABS; subst a; try contradiction.
          eapply INCL,INCL2 in IN.
          rewrite <-hid_proj_removeEntry...
          eapply in_domain_in_g in IN as (ff &tt &IN);
            try eapply in_g_in_domain, removeEntry_in...
          
          assert (In (a1, a2, vis, (Chan un io t)) g').
          unfold g'. unfold g0.
          apply in_app_iff with (l := (b1, b2, ill, s1) :: nil).
          right. apply removeEntry_in...
          eauto.

          subst g' g0; econstructor; right; try eapply removeEntry_in...
          subst g' g0; econstructor...
          inversion H. destruct H16 as [TPLUSS ISUN]; apply type_plus_comm...
          all:try eassumption.
           eapply sl_pos_par_r...

            subst g' g0; try  erewrite <-max_removeEntry_cons;
            try eapply in_g_in_domain;
            try eapply incl_preserves_max...
          assert (IN4: incl (secLabs q1) (domain g4)).
          try eapply typeCheck_no_dup with (pf := pf4)...
          introv IN';erewrite <-split_domain_l...

          inversion ABS.
          apply fsub_hid_r with
            (pf1 := pf4) (pf2 := pf3) (pf := pf1) in T3b as K3b.
          inversion K3b; inversion H14; subst. 
          specialize flag_of_map with g1 (b1, b2) hid ill as ABS2. intuition. discriminate.
          all:try eassumption.
           eapply sl_pos_par_r...

          
      ***
        assert (TOP: s = Top /\ t = Top /\ s1 = Top /\ s3 = Top /\ s4 = Top /\ s' = Top).
        inversion IHPREQ; subst.
        inversion TPLUS1; subst.
        inversion TYP3; subst.
        inversion TYP1; subst. intuition.
        
        assert (TYPa := H0).
        inversion TYP2; subst.
        apply tsuper_payload with
          (pf1 := pf4) (pf2 := pfw) (pf := pf) in H0 as K0.
        destruct K0 as [q4 TYP4]. inversion TYP4; subst.
        inversion TYP'; subst. 
        assert (q4 = q'' /\ q'' = q').
        apply split_plus_un with
          (pf1 := pf4) (pf2 := pf3) (pf3 := pf1) (b1 := a1) (b2 := a2) (t := t) (f1 := f2) (f2 := f1) (f3 := f3)...
        destruct H11; subst.
        apply tsuper_payload_r with
          (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as K0.
        destruct K0 as [q'' TYP2']. inversion TYP2'; subst.
        assert (q' = q'' /\ q'' = io).
        apply split_plus_un with
          (pf1 := pf1) (pf2 := pf2) (pf3 := pf) (b1 := a1) (b2 := a2) (t := t) (f1 := f3) (f2 := f4) (f3 := vis)...
        destruct H12; subst.
        
        move g2 at top.
        apply fsuper_vis
          with (pf1 := pf1) (pf2 := pf2) (pf := pf) in H0 as [K1 K2].
        inversion K1; subst. 
        assert (vis = f3 /\ t0 =  Chan un io t).
        apply in_isMap with (x := (a1, a2)) (g := g1)...
        destruct H12; subst.
        apply fsuper_vis
          with (pf1 := pf4) (pf2 := pf3) (pf := pf1) in H0 as [K3 K4].
        inversion K3; subst.
        assert (vis = f2 /\ t0 =  Chan un io t).
        apply in_isMap with (x := (a1, a2)) (g := g4)...
        destruct H12; subst...
        inversion K4; subst.
        assert (vis = f1 /\ t0 =  Chan un io t).
        apply in_isMap with (x := (a1, a2)) (g := g3)...
        destruct H13; subst.
        all:try eassumption.

        destruct IHTSPLIT as
          [[NOTUN IHTSPLIT] | ABS].
        specialize IHLTS2 with
          (nd_pf1 := nd_pf4) (pf2 := pfw2) (pf := pf0').
        apply IHLTS2 in IHTSPLIT.
        destruct IHTSPLIT as [k4 LTSIN].
        
        
        assert (nd_pfw2 :
                 NoDup(domain
                         ( (b1, b2, ill, Top)
                             :: 
                             (removeEntry (b1, b2) g1)))).
        apply no_dup_cons_removeEntry...

        apply lts_un_input_action
          with (pol := io) (t := t) (s := s1) (r := s)
          in LTS2 as Heqgg3.
        destruct Heqgg3 as (kk3 &DIS3  &Heqgg3).
        rewrite Heqgg3 in LTS2.

        
        
        unfold g' in LTS2. unfold g0 in LTS2.
        apply lts_type_plus_un_in with
          (a1 := a1) (a2 := a2) (t := t) (b1 := b1) (b2 := b2)
          (f := ill) (f1 := ill) (pol := io)
          (s01 := Top) (s := s) (s1 := s1) (s0 := Top)
          (pf1 := nd_pfw2)
          in LTS2 as UNIN.
        destruct UNIN as [kk1 UNIN].

        remember (kk1 ++
                    (b1, b2, vis, Top)
                    :: removeEntry (b1, b2) ((b1, b2, ill, Top) :: removeEntry (b1, b2) g1)) as gk1.
        exists (((b1, b2), hid, Top) :: removeEntry (b1, b2) gk1).
        apply uclsL with
          (s1 := Top) (s := Top) (t := t)(pf1 := nd_pf1) (pf2 := nd_pfw2).
        intuition; subst...
        eauto.
        inversion IN1; subst.
        apply fsub_hid_r with (pf1 := pf4) (pf2 := pf3) (pf := pf1) in T3b as K3b.
        inversion K3b; subst.
        assert (hid = f1 /\ t0 = s').
        apply in_isMap with (x := (b1, b2)) (g := g1)...
        destruct H15; subst.
        intuition; subst...
        eauto.
        apply lts_type_remove_un_out with
          (pol := io) (t := t) (f := hid) (s := s)
          (s1 := s') (s0 := Top) (pf := nd_pf).
        eauto. eauto. intuition; subst...
        intuition; subst...
        eauto.
        inversion IN1; subst.
        apply fsub_hid_r with (pf1 := pf4) (pf2 := pf3) (pf := pf1) in T3b as K3b.
        inversion K3b; subst.
        assert (hid = f1 /\ t0 = s').
        apply in_isMap with (x := (b1, b2)) (g := g1)...
        destruct H15; subst.
        intuition; subst...
        eauto.
        eauto.

           eapply typeCheck_no_dup with (pf := pf3)...
          simpl.
          introv IN.
 
          assert (INCL: incl (secLabs p1) (domain (hid_proj g3))).
          eapply typeCheck_hid_proj with (pf := pf3)...
          assert (INCL2: incl (domain (hid_proj g3))(domain (hid_proj g1))).
          eapply split_incl_hid_proj...
          eauto.
          eauto.

        rewrite   Heqgk1.
        apply in_app_iff with (l := kk1).
        right.
        apply in_app_iff with (l := (b1, b2, vis, Top) :: nil).
        right.
        apply removeEntry_in.
        eauto.
        apply in_app_iff with (l := (b1, b2, ill, Top) :: nil).
        right.
        apply removeEntry_in...
        rewrite   Heqgk1.
        apply in_app_iff with (l := kk1)...
        apply in_app_iff with (l := (b1, b2, ill, s1) :: nil).
        right.
        apply removeEntry_in...
        eauto.
        intuition; subst...
        discriminate.
        apply in_app_iff with (l := (b1, b2, ill, Top) :: nil).
        right. apply removeEntry_in...
        eauto.
        
        apply split_removeEntry_domain_2 with
          (pf1 := pf1) (pf2 := pf2) (pf := pf)...
        assert (In (a1, a2, vis, (Chan un io t)) g').
        unfold g'. unfold g0.
        apply in_app_iff with (l := (b1, b2, ill, s1) :: nil).
        right. apply removeEntry_in...

           eapply typeCheck_no_dup with (pf := pf4)...
          simpl.
          introv IN.
 
          assert (INCL: incl (secLabs q1) (domain (hid_proj g4))).
          eapply typeCheck_hid_proj with (pf := pf4)...
          assert (INCL2: incl (domain (hid_proj g4))(domain (hid_proj g1))).
          eapply split_incl_hid_proj...

          assert (IN' := IN).
          assert (INSL: In (b1, b2) (fn p1) \/ In (b1, b2) (secLabs p1)).
            eapply payload_occurs...
            destruct INSL as [ABS | INSL].
            eapply tc_dep_relabel_premises.typeCheck_is_vis in H7 as (tt& ABS2)...
            assert (ABS3: hid = vis /\ s3 = tt)...
            destruct ABS3; try discriminate.
            assert (NIN: ~In (b1, b2) (secLabs q1)).
            intros ABS.
            assert (ND: NoDup (secLabs  (dPar p1 q1))).
            eapply typeCheck_no_dup with (pf := pf1)...
            simpl in ND; eapply no_dup_iff in ND as (ND1 &ND2 &DIS).
            eapply disjoint_absurd...

          assert (a <> (b1, b2)).
          intros ABS; subst a; try contradiction.
          eapply INCL,INCL2 in IN.
          rewrite <-hid_proj_removeEntry...
          eapply in_domain_in_g in IN as (ff &tt &IN);
            try eapply in_g_in_domain, removeEntry_in...
        
        eauto.
        subst g' g0; econstructor; right; try eapply removeEntry_in...
        subst g' g0; econstructor...
        inversion H. destruct H14 as [TPLUSS ISUN]; apply type_plus_comm...
        all:try eassumption.
         eapply sl_pos_par_r...

                subst g' g0; try  erewrite <-max_removeEntry_cons;
            try eapply in_g_in_domain;
            try eapply incl_preserves_max...
          assert (IN4: incl (secLabs q1) (domain g4)).
          try eapply typeCheck_no_dup with (pf := pf4)...
          introv IN';erewrite <-split_domain_l...
           eapply sl_pos_par_r...

        destruct ABS as [ABS UNUSED]. inversion ABS.
        destruct H13 as [t' ABS2]; inversion ABS2.
      *** eauto.
      ***  eapply sl_pos_par_l...
    * eauto.
    * eauto.

  - Case open.
    intros. 
    inversion TCHECK.  destruct n. simpl in H0. simpl in H1.
    subst n n0 p0. simpl.
    remember pf0 as nd_pf; subst pf0.
    remember pf1 as nd_pf0; subst pf1.
    remember pf3 as pf1; subst pf3.
    
    specialize IHLTS with (pf1 := pf4).
    assert (T2b: exists t2,
               typeOf g2 (b1, b2) t2 /\
                 type_plus t0 t2 t).
    apply split_type_plus with (pf1 := pf1) (pf2 := pf2) (pf := pf)...
    destruct T2b as [t2 [T2b TP2]].
    inversion T2b; subst.
    apply fsuper_hid with (pf1 := pf1) (pf2 := pf2) (pf := pf) in H as K.
    destruct K as [[F1 F2] | ABS].
    inversion F2; subst.
    assert (f = ill /\ t2 = t1).
    apply in_isMap with (x := (b1, b2)) (g := g2)...
    destruct H3. subst t1.
    assert (pf2' : isMap (((b1, b2, vis, t2) :: removeEntry (b1, b2) g2))).
    apply cons_removeEntry;
      try eapply no_dup_split_no_dup_r in nd_pf...
    assert (pf' : isMap ((b1, b2, vis, t) :: removeEntry (b1, b2) g))...
    assert (IHREQ: tEnv_split ((b1, b2, vis, t0) :: removeEntry (b1, b2) g1) ((b1, b2, vis, t2) :: removeEntry (b1, b2) g2)
                     ((b1, b2, vis, t) :: removeEntry (b1, b2) g) pf4 pf2' pf').
    apply split_cons_remove with
      (pf1 := pf1) (pf2 := pf2) (pf3 := pf)
      (f1 := hid) (f2 := ill) (f3 := hid); try assumption.
      eapply no_dup_split_no_dup_r in TSPLIT...

    assert (nd_pf1' : NoDup (domain ((b1, b2, vis, t0) :: removeEntry (b1, b2) g1))).
    apply no_dup_cons_removeEntry...
    specialize IHLTS with (pf := pf') (pf2 := pf2') (nd_pf1 := nd_pf1').
    apply IHLTS in IHREQ as LTSOUT.
    destruct LTSOUT as [k1 LTSOUT].
    exists k1.
    apply open with (t := t0) (pf1 := nd_pf1')...
    eauto.
    eauto.
    inversion ABS. inversion H1. subst. 
    assert (hid = ill /\ t0 = t1).
    apply in_isMap with (x := (b1, b2)) (g := g1)...
    destruct H6; discriminate. eauto.

    
  - Case hide.


    
    introv TS TC; inv TC;
      assert (IN := TS);
      eapply fsuper_hid with (n := n) in IN as [(EQ1 &EQ2) | (ABS &_)];
      destruct n as [c1 c2]; simpl in *;
      try eapply in_app_iff; try right...
    2:{ inv ABS. assert (ill =hid).
        eapply flag_of_map with (g := g1)... discriminate. }

    assert (SLP2 := SLP). eapply sl_pos_nu in SLP2.
    assert (TC := H5).
    eapply typeCheck_no_dup in H5 as (INCL &NDSL)...
    
    (*assert (CONCL: lts (h1 ++ (c1, c2, hid, t) :: h2) (dNu c1 c2 p) a (h' ++ (c1, c2, hid, t') :: h'') (dNu c1 c2 p') pf0)...*)
    
    inv EQ1; inv EQ2.
    move LTS at bottom.
    assert (t0 =t1)... subst t0.

    
    assert (nd_pf :
    NoDup(domain((c1,c2,vis,t1)
    ::removeEntry(c1,c2) g1))).
    eapply no_dup_cons_removeEntry...
    eapply sl_pos_nu in SLP;
      eapply IHLTS with (nd_pf1 := nd_pf)
      in SLP as (k1 &IH); clear IHLTS;
      try eassumption.
   


    eapply in_split in H3 as (l1 &l2 &EQ); subst g1.
    
    
    assert (EQ: ((c1, c2, vis, t1)
    :: removeEntry (c1, c2)
         (l1 ++ (c1, c2, hid, t1) :: l2))=
         (c1, c2, vis, t1) :: l1 ++ l2).
    erewrite removeEntry_app_shift; simpl;
      try erewrite pairEq_eq_true; try introv ABS...
    assert (ND:= nd_pf1); rewrite domain_distr in ND;
      simpl in ND; eapply no_dup_iff in ND as (_&_&DIS);
      eapply disjoint_absurd...
         gen nd_pf. rewrite EQ in *; introv IH. clear EQ.

          assert (MAX:  max (secLabs p) <= max (domain ((c1, c2, vis, t1) :: l1 ++ l2))).
    eapply incl_preserves_max...
   

    
    move LTS at bottom.
    
    assert (GGOAL: exists s, In (c1, c2, vis, s) k1).
    eapply lts_flagOf_vis_entry in IH...
    inv IH. exists t0...
    
   
    
    
     destruct GGOAL as (s &IN);
      eapply in_split in IN as (m1 &m2 &EQ2); subst k1.
      assert (nd_pf' :  NoDup (domain (l1 ++ (c1, c2, vis, t1) :: l2))).
     rewrite domain_distr in *; simpl in *...

     
     assert (IH' :
              exists k1 (pfk1 : NoDup (domain k1)),
                lts (l1 ++ (c1, c2, vis, t1) :: l2) p a k1 p' nd_pf' /\
            (forall x : name * name * flag * piType, In x  (m1 ++ (c1, c2, vis, s) :: m2) <-> In x k1 )).
     eapply lts_iff
       with (pf1 := nd_pf)
            (g2 := (l1 ++ (c1, c2, vis, t1) :: l2));
       try assumption.
     eapply lts_no_dup.lts_no_dup...
     eapply incl_incl2...
     (*  forall x : name * name * flag * piType,
  In x ((c1, c2, vis, t1) :: l1 ++ l2) <-> In x (l1 ++ (c1, c2, vis, t1) :: l2)*)
      assert (P0: Permutation ((c1, c2, vis, t1) :: l1 ++ l2)(l1 ++ (c1, c2, vis, t1) :: l2)).
     specialize Permutation_cons_append with (l := l1) (x :=  (c1, c2, vis, t1)) as P1.
     assert (EQ2: ((c1, c2, vis, t1) :: l1 ++ l2 =
                   ((c1, c2, vis, t1) :: l1 )++l2))...
     assert (EQ3: l1 ++ (c1, c2, vis, t1) :: l2 =
                  (l1 ++ (c1, c2, vis, t1) :: nil) ++ l2).
     erewrite cons_app,<-app_assoc...
     erewrite EQ2,EQ3;
       eapply Permutation_app...
     intros; split; try eapply Permutation_in...
     try eapply Permutation_sym...

     destruct IH' as (k1 &pfk1 &IH' &IFF).
     assert (FYP: flagOf k1 (c1, c2) vis).
     eapply lts_flagOf_vis_entry.
     eauto.
     econstructor; eapply in_app_iff; right...
        try inverts FYP as IN.
       try eapply in_split in IN as (k' &k'' &IH''); subst.
     
     exists ((k' ++ (c1, c2, hid, t0) :: k''));
       try eapply hide...


    
    (* tEnv_split ((c1, c2, vis, t1) :: removeEntry (c1, c2) g1) ?g2
    (h1 ++ (c1, c2, vis, t) :: h2) pf4 ?pf2 ?pf15*)
     instantiate (3 := (c1, c2, vis, t2)
                         :: removeEntry (c1, c2) g2).
     assert (ADD:
         forall pff2 pff3,
           tEnv_split ((c1, c2, vis, t1) :: removeEntry (c1, c2) g1)
             ((c1, c2, vis, t2) :: removeEntry (c1, c2) g2) ( (c1, c2, vis, t) :: removeEntry (c1, c2) (h1 ++ (c1, c2, hid, t) :: h2)) pf4 pff2 pff3).
     assert (TP2 :  type_plus t1 t2 t).
     eapply split_type_plus with (a := (c1, c2)) (t := t)in TS as (tt2 &TYP2 &TYP); try econstructor...
    assert (tt2 = t2).
    inv TYP2; eapply in_isMap with (g := g2)...
    subst...
    eapply in_app_iff; right...
    
    intros; eapply tEnv_split_add_vis; try eassumption.
    introv ISUN; destruct ISUN as (mm &pp &ISUN); subst t;
      try inv TP2.
    assert (EQ: p1 = p2 /\ p2 = (pol_cup p1 p2)).
    eapply split_plus_un with (pf3 := pf)...
    eapply in_app_iff; right...
    destruct EQ as [EQ1 EQ2]; subst; try rewrite <-EQ2; intuition.

    eapply split_iff; try eapply ADD...
    introv; rewrite removeEntry_app_shift;
      unfold removeEntry;
      try rewrite pairEq_eq_true.

     assert (P0: Permutation ((c1, c2, vis, t) :: h1 ++ h2)(h1 ++ (c1, c2, vis, t) :: h2)).
     specialize Permutation_cons_append with (l := h1) (x :=  (c1, c2, vis, t)) as P1.
     assert (EQ2: ((c1, c2, vis, t) :: h1 ++ h2 =
                   ((c1, c2, vis, t) :: h1 )++h2))...
     assert (EQ3: h1 ++ (c1, c2, vis, t) :: h2 =
                  (h1 ++ (c1, c2, vis, t) :: nil) ++ h2).
     erewrite cons_app,<-app_assoc...
     erewrite EQ2,EQ3;
       eapply Permutation_app...
     intros; split; try eapply Permutation_in...
     try eapply Permutation_sym...

     introv ABS.
     assert (ND := pf0); rewrite domain_distr in ND;
       simpl in ND; eapply no_dup_iff in ND as (_&_&DIS);
       try eapply disjoint_absurd...
     
    Unshelve.
    all:
      try eapply no_dup_isMap;
      try eapply no_dup_cons_removeEntry;
      try eassumption.
    eapply no_dup_split_no_dup_r in TS...
Qed.




