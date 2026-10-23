Require Import
        Bool List Lia PeanoNat Program.Equality
        ListAddOns Max Domain RemoveEntry NewEntries Replication
        header
        operations pi_syntax 
        pairEq type_system
        semantics  
        type_operations_1 
        split_exists_neutral
        sub_split
        no_dup_split_no_dup
        proposition27
        split_existential 
        split_not_exists
        split_operations
        type_checking_0
        lts_operations 
        split_operations_2 
        split_operations_3
        split_existential_2 
        type_checking_1
        disjoint_newEntries
        lts_no_dup 
        tc_prelim
        tc_premises2
        tc_substitution
        tc_dep_relabel_premises
        tc_dep_relabel_premises_2
        tc_dep_relabel_new
        disjoint_newEntries
        type_system_rules
        tc_premises_3
        split_operations_4
        split_cons_remove
        tc_premises_4
        tc_ill_vis
        split_cons_remove_2
        tc_premises_5
        tc_premises_6
        tc_premises_7
        substitution_prelim
        sne_premises
        lts_iff
        typeCheck_dep_relabel1
        tc_weak_is_un
        tc_premises_8
        lts_payload_un_inp.


Require Import CpdtTactics LibTactics.

Require Import Coq.Logic.Classical_Prop.

Section SubjectReduction.
  
  Hint Resolve typeCheck_rewrite_pf
       in_g_in_domain.



       


  Lemma wf_rewrite  p :
    NoDup (secLabs p) -> NoDup (secLabs p).
  Proof. intros; assumption. Qed.  
    
    
  Lemma isMap_vis_proj_removeEntry  b1 b2 t g:
    NoDup (domain g) ->
    isMap (vis_proj ((b1, b2, vis, t) :: removeEntry (b1, b2) g)).
    Proof with eauto.
    intros.  simpl.  eapply isMap_not_in. intros ABS. eapply in_domain_in_g in ABS as (ff &tt &ABS); eapply proj_in,no_dup_not_in_removeEntry in ABS; try contradiction...
    try eapply proj_isMap,isMap_removeEntry...
  Qed.
Lemma isMap_illProj_removeEntry b1 b2 t g f:
                 NoDup (domain g) ->
                 isMap (ill_proj ((b1, b2, f, t) :: removeEntry (b1, b2) g)).
Proof with eauto.
  intros.
  destruct f.
  simpl;try eapply proj_in,no_dup_not_in_removeEntry...
  
 simpl; try eapply isMap_not_in. intros ABS. eapply in_domain_in_g in ABS as (ff &tt &ABS); eapply proj_in,no_dup_not_in_removeEntry in ABS; try contradiction...
 try eapply proj_isMap,isMap_removeEntry...

  simpl;try eapply proj_in,no_dup_not_in_removeEntry...
Qed.



Lemma no_dup_g g: NoDup (domain g) -> NoDup g.
Proof with eauto.
  induction g; introv ND; try destruct a as [[[a1 a2] f1]t1];
    simpl in ND; inv ND; try econstructor...
Qed.

  

  Hint Resolve incl_pos in_vis_ill_proj.
  

   Lemma sr_strong :
    forall g p a p' nd_pf pf 
           g1 g2 k1 h pf1 pf2 pfk1 nd_pf1,
      sl_pos p -> (* HYP *)
      typeCheck g1 pf1 p -> (* g1 |- p *)
      tEnv_split g1 g2 g pf1 pf2 pf -> (* g1 + g2 = g *)
      lts g p a h p' nd_pf -> (* g>p -a-> h>p' *)
      lts g1 p a k1 p' nd_pf1 ->    (* g1>p -a-> k1>p' *)
      typeCheck k1 pfk1 p'. (* k1 |- p' *)
   Proof with eauto using
              typeCheck_hid_proj.
    intros g p a p' nd_pf pf g1 g2 k1 h
           pf1 pf2 pfk1 nd_pf1
           SLP TYP TS LTS AFT.
    generalize dependent g1.
    generalize dependent g2.
    generalize dependent k1.
    dependent induction LTS.
    
    - Case parL.

      assert (lts_finite := nonDivergentProcesses).
      intros k1 pfk1 g2 pf2 g1 pf1 nd_pf1
             TYP TS LTSPAR.
      remember q as p3. remember pf0 as nd_pf. subst pf0.
      inversion TYP.

      assert (IH1 : sl_pos p1).
      unfold sl_pos in SLP; unfold secLabs in SLP;
        fold secLabs in SLP; fold sl_pos in SLP. subst p0 q p4.
      unfold pos in SLP; unfold sl_pos; unfold pos.
      intros; specialize SLP with x1 x2; intuition. 
      subst p0 q p4.
      
      apply no_dup_split_no_dup_l with
          g0 g3 g1 pf0 pf3 pf1 in nd_pf1 as nd_pf0.
            apply no_dup_split_no_dup_r with
          g0 g3 g1 pf0 pf3 pf1 in nd_pf1 as nd_pf3.
      specialize split_lts_exists_lts with
          (g :=g1) (g1:= g0) (g2 := g3) 
          (p := p1) (a := a) (g' := k1) 
          (p' := p2) (pf1 := pf0) (pf2 := pf3)
          (pf := pf1) (nd_pf := nd_pf1) (nd_pf1 := nd_pf0)
        as LTS1.
      assert (TS2 := H1).
      apply LTS1 in TS2 as LTS0.
      destruct LTS0 as [k0 LTS0].
      clear LTS1.
      apply split_of_split with
          g0 g3 g1 g2 g pf0 pf3 pf1 pf2 pf in H1
        as EXSPLITG0.
      
      destruct EXSPLITG0 as [w2 [pfw2 EXSPLITG0]].
      apply lts_no_dup with
          g0 p1 a k0 p2 nd_pf0
        in LTS0 as nd_pfk0.
      apply no_dup_isMap in nd_pfk0 as pfk0...
      eapply lts_no_dup 
        in LTSPAR as nd_pfk1...
      all:eauto.

      (* lts g p1 a g' p2 nd_pf *)
      destruct a.
      +  remember n as a1. remember n0 as a2.
         remember n1 as b1. remember n2 as b2.

         assert (DIFF : (a1, a2) <> (b1, b2)).
         eapply nonRecActions1...

         (* a = aIn a1 a2 b1 b2 *)
        apply lts_after_inp in LTS0 as LEM.
         destruct LEM as
             [f [m [ q [t [r [tb [TYPa [TYPb [NHID TP]]]]]]]]].
         move m at top.
         
         (* In (b1, b2, f, tb) g0 *)
         destruct tb.
         *
           (* tb = Chan m0 p tb *)
           assert (TYP3b:
                     exists f3 q3,
                       In ((b1, b2), f3, (Chan m0 q3 tb)) g3).
           eapply tsub_payload with (pf := pf1) in TYPb.
           destruct TYPb as [pp1 TYPb]; inversion TYPb; subst.
           eapply tsuper_payload_r in H...
           destruct H as [pp3 TYP3]; inversion TYP3...
           eauto.
           destruct TYP3b as [f3 [q3 TYP3b]].
           (*  In (b1, b2, f, Chan m0 p tb) g0 *)
           (**** 2DO: we might avoid to destruct both the flag and the modality immediately ****)
           destruct m0.
           **
             (* m0 = lin *)
             destruct f.
             ***
               (* f = hid *)
               contradiction.
             ***
               (* f = ill *)
               assert (f3 = ill).
               (* by showing that  f3 = hid ->
                   tEnv_split g0 g3 g1 pf0 pf3 pf1 ->
flagOf b g1 hid and
tEnv_split g1 g2 g pf1 pf2 pf ->
flagOf b g1 hid ->
flagOf b g hid.
finally
lts g p1 (aIn a1 a2 b1 b2) g' p2 nd_pf ->contradiction by apply lts_inp_obj_not_hid*)
               destruct f3.
               clear IHLTS.
               eapply lts_inp_obj_not_hid in LTS0;
                 eapply lts_inp_obj_not_hid in LTS.
               eapply fsub_hid with (pf := pf1)  in TYP3b.
               inversion TYP3b; subst.
               eapply fsub_hid with (pf := pf)  in H.
               contradiction.
               eauto. eapply split_comm...
               tauto.
               eapply fsub_vis with (pf := pf1)  in TYP3b.
               inversion TYP3b; subst.
               eapply fsuper_vis with (pf1 := pf0) in H.
               destruct H as [H _].
               assert (ill = vis).
               eapply flag_of_map with (g := g0)...
               discriminate.
               eauto.
               eapply split_comm...
               
               assert (TC3 := H3).
               specialize typeCheck_ill with
                   (b1, b2) (Chan lin q3 tb) g3 pf3 p3 as TYPILL.
               apply TYPILL in H3 as [ABS | [EX | EX]].
               discriminate.
               destruct EX as [t' EQ].
               inversion EQ. subst q3 t'.
               clear TYPILL.
               assert (nd_pf3' :
                         NoDup (domain 
                           (((b1, b2), vis, Chan lin empty tb)
                              :: removeEntry (b1, b2) g3))).
               eapply no_dup_cons_removeEntry, no_dup_split_no_dup_r with (pf1 := pf0) (pf := pf1)...
               eapply no_dup_isMap in nd_pf3' as pf3'.
               assert
                 (typeCheck_ill_vis :
                    typeCheck g3 pf3 p3 ->
                    typeCheck
                      (((b1, b2), vis, Chan lin empty tb)
                         :: removeEntry (b1, b2) g3)
                      pf3'
                      p3).
               intros; eapply typeCheck_ill_vis; subst...
               move pf3' at top.
               clear typeCheck_ill_vis.
               specialize IHLTS with
                   (k1 := k0) (g1 := g0)
                   (g2 := w2) (pf1 := pf0) (pf2 := pfw2)
                   (pfk1 := pfk0) (pf := pf) (nd_pf1 := nd_pf0).
               apply IHLTS in IH1. clear IHLTS.
               
               all:eauto.

               assert (TC2 := H2).
               specialize typeCheck_ill with
                   (b1, b2) (Chan lin p tb) g0 pf0 p1 as TYPILL.
               apply TYPILL in H2.
               assert (p = empty).
               move H2 at bottom;destruct H2 as [ABS | [OK | ABS]]; try discriminate. destruct OK as [tt OK]; inversion OK...
               destruct ABS as [pp [tt ABS]]; inversion ABS...
               subst p.

               apply lts_inp with
                   (ta :=  (Chan m q t))
                   (tb := (Chan lin empty tb))
                   (m := m)
                   (q := q)
                   (t := t)
                   (r := r)
                 in LTS0 as G0.
               

               inversion  TYPa. subst g4 n3 t0.
               apply tsub_payload with
                   g0 g3 g1 pf0 pf3 pf1 a1 a2 f m q t in H0 as K. 
               destruct K as [q1 TYP1a].
               apply tsub_payload with
                   g0 g3 g1 pf0 pf3 pf1 b1 b2 ill lin empty tb in TYPb as K.
               destruct K as [q2 TYP1b].
               
               assert (lts_input_exists_plus:
                         exists r',
                           type_plus t (Chan lin q2 tb) r').
               assert (AFT: exists (f : flag) (m : mode) (q : pol) (t r tb : piType),
    typeOf g1 (a1, a2) (Chan m q t) /\ In (b1, b2, f, tb) g1 /\ f <> hid /\ type_plus t tb r).
               eapply lts_after_inp...
               destruct AFT as
                   [ff [mm [qq [tt [rr [ttb [TYPP [INN [_ TPP]]]]]]]]].
               assert (Chan lin q2 tb = ttb).
               eapply type_of_map with (g := g1) (x := (b1, b2))...
               assert (t = tt).
               assert (Chan m q1 t = Chan mm qq tt).
                eapply type_of_map with (g := g1) (x := (a1, a2))...
                inversion H4; subst; intuition.
                inversion H3; subst.
                exists rr...
                
                
               destruct lts_input_exists_plus as [r' TP2].
               assert (LTS1:  lts g1 p1 (aIn a1 a2 b1 b2) k1 p2 nd_pf1). 
               inversion LTSPAR...
               apply lts_inp with
                   (ta :=  Chan m q1 t)
                   (tb := (Chan lin q2 tb))
                   (m := m)
                   (q := q1)
                   (t := t)
                   (r := r')
                 in LTS1 as G1.
               
               assert (TP0 := TP).
               inversion TP. subst t0.
               assert (TP20 := TP2).
               inversion TP2.
               all: eauto.
               destruct m.
               ****
                 remember ((((b1, b2), vis, Chan lin empty tb)
                              :: removeEntry (b1, b2) g3))
                   as g3'.
                 
                 apply TPar with
                      (pf1 := pfk0) (pf2 := pf3').

                 (* HYP *)
                 (* g1>p1 -a-> k1>p2 *)
                 (* g0>p1 -a-> k0>p2 *)
                 (* g0 + g3 = g1 *)
                 (* g3(b)= (ill, Chan lin q3 t) *)
                 (* g3' = g3 \b, (vis, Chan lin empty t) *)
                 (* GOAL *)
                 (* k0 + g3' = k1 *) 

                 subst.
                 
                 
                 destruct G0 as [G0 ABS].
                 assert (K0 : lin=lin). tauto.
                 apply G0 in K0 as W0.
                 apply G1 in K0 as W1.
                 revert dependent pfk0; rewrite W0.
                 revert dependent pfk1; rewrite W1.
                 intros. subst.
                 
                 specialize typeCheck_ill with
                     (n1, n2) (Chan lin q2 tb) g1 pf1 (dPar p1 p3) as TYPILL2.
                 apply TYPILL2 in TYP as [ABS2 | [EX1 | EX2]].
                 discriminate.
                 destruct EX1 as [t2 TYPb1].
                 inversion TYPb1. subst.
                 inversion H8; subst. 
                 assert (p0 = p7). inversion H11...
                 subst p0.
                 assert (p7 = p). inversion TP. inversion H3...
                 subst.
                 (* HYP:  tEnv_split g0 g3 g1 pf0 pf3 pf1 *)
                 (* GOAL:  tEnv_split
    ((a1, a2, vis, Chan lin empty (Chan lin empty tb))
     :: (b1, b2, vis, Chan lin p7 tb) :: removeEntry (a1, a2) (removeEntry (b1, b2) g0))
    ((b1, b2, vis, Chan lin empty tb) :: removeEntry (b1, b2) g3)
    ((a1, a2, vis, Chan lin empty (Chan lin empty tb))
     :: (b1, b2, vis, Chan lin p7 tb) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1))
    pfk0 pf3' pfk1 *)
                 assert
                   (nd_pff0: NoDup (domain
                             (removeEntry (n, n0)
                                          ((n, n0, vis, Chan lin empty (Chan lin p t2))
                                             :: (n1, n2, vis, Chan lin p t2) :: removeEntry (n, n0) (removeEntry (n1, n2) g0))))).
                   unfold removeEntry. fold removeEntry.
                 assert (EQ2:  pair_eq (n, n0) (n, n0) = true). eauto.  rewrite EQ2.
                 erewrite removeEntry_swap.
                 eapply no_dup_cons_removeEntry, no_dup_removeEntry_no_dup...
                 eauto.
                 assert (nd_pff3:
                           NoDup (domain (
                 
                                      (removeEntry (n, n0) ((n1, n2, vis, Chan lin empty t2) :: removeEntry (n1, n2) g3))))).
                 eapply no_dup_removeEntry_no_dup,no_dup_cons_removeEntry,no_dup_split_no_dup_r with (pf := pf1)...
                 assert (nd_pff1:
                           NoDup (domain (
                 removeEntry (n, n0)
   ((n, n0, vis, Chan lin empty (Chan lin p t2))
      :: (n1, n2, vis, Chan lin p t2) :: removeEntry (n, n0) (removeEntry (n1, n2) g1))))).
                   unfold removeEntry. fold removeEntry.
                 assert (EQ2:  pair_eq (n, n0) (n, n0) = true). eauto.  rewrite EQ2.
                 erewrite removeEntry_swap.
                 eapply no_dup_cons_removeEntry, no_dup_removeEntry_no_dup...
                 eauto.
                 apply no_dup_isMap in nd_pff3 as pff3; eapply  no_dup_isMap in nd_pff0 as pff0;eapply  no_dup_isMap in nd_pff1 as pff1.
                
                 
                 eapply SpLin with (n := (n, n0)) (f := vis) (p := empty) (pf' := pff0) (pf'' := pff3) (pf''' := pff1).
                 eauto. eauto. eauto. right.
                 (*In (n, n0, vis, Chan lin empty (Chan lin p t2)) (removeEntry (n1, n2) g3)*)
                 (* ??? *)
                 assert (q1 = inp).
                 assert (exists t : piType,
    typeOf g1 (n, n0) (Chan lin inp t) \/
    typeOf g1 (n, n0) (Chan un inp t) \/ typeOf g1 (n, n0) (Chan un io t)).
                 eapply type_of_in_action...
                 destruct H as
                     [tt [TYP1 | [TYP1 | TYP1]]].
                 assert (Chan lin q1 (Chan lin p t2) =
                         Chan lin inp tt).
                 eapply type_of_map with (x := (n, n0)) (g := g1)...
                 inversion H...
                  assert (Chan lin q1 (Chan lin p t2) =
                         Chan un inp tt).
                 eapply type_of_map with (x := (n, n0)) (g := g1)...
                 inversion H...
                  assert (Chan lin q1 (Chan lin p t2) =
                         Chan un io tt).
                 eapply type_of_map with (x := (n, n0)) (g := g1)...
                 inversion H...
                 subst.
                 assert (q = inp).
                 assert (exists t : piType,
    typeOf g0 (n, n0) (Chan lin inp t) \/
    typeOf g0 (n, n0) (Chan un inp t) \/ typeOf g0 (n, n0) (Chan un io t)).
                 eapply type_of_in_action...
                 destruct H as
                     [tt [TYP1 | [TYP1 | TYP1]]].
                 assert (Chan lin q (Chan lin p t2) =
                         Chan lin inp tt).
                 eapply type_of_map with (x := (n, n0)) (g := g0)...
                 inversion H...
                  assert (Chan lin q (Chan lin p t2) =
                         Chan un inp tt).
                 eapply type_of_map with (x := (n, n0)) (g := g0)...
                 inversion H...
                  assert (Chan lin q (Chan lin p t2) =
                         Chan un io tt).
                 eapply type_of_map with (x := (n, n0)) (g := g0)...
                 inversion H...
                 subst.
                 inversion TYP1a; subst.
                 eapply tsuper_payload_r with (pf2 := pf3) in H as K.
                 destruct K as [pp3 TYP3].
                 inversion TYP3; subst.
                 assert (pol_plus inp pp3 inp).
                 eapply split_plus_lin with (pf1 := pf0) (pf2 := pf3) (pf3 := pf1)...
                 assert (pp3 = empty).
                 inversion H4...
                 subst.
                 assert (F0: flagOf g0 (n, n0) vis).
                 eapply lts_vis_subject...
                 inversion F0; subst.
                 eapply fsub_vis with (pf := pf1) in H5.
                 inversion H5; subst.
                 eapply fsuper_vis with (pf2 := pf3) in H6.
                 destruct H6 as [_ K].
                 inversion K; subst.
                 assert (f1 = vis /\  Chan lin empty (Chan lin p t2) = t1).
                 eapply in_isMap with (g := g3)...
                 destruct H9; subst.
                 eapply removeEntry_in...
                 eauto.
                 eauto.
                 eauto.
   
                 (*tEnv_split
    (removeEntry (n, n0)
       ((n, n0, vis, Chan lin empty (Chan lin p t2))
        :: (n1, n2, vis, Chan lin p t2) :: removeEntry (n, n0) (removeEntry (n1, n2) g0)))
    (removeEntry (n, n0) ((n1, n2, vis, Chan lin empty t2) :: removeEntry (n1, n2) g3))
    ?g''' ?pf' ?pf'' ?pf'''*)

                  assert (EQ2:  pair_eq (n, n0) (n, n0) = true).
                  eauto.
                  assert (EQ3: pair_eq (n1, n2) (n, n0) = false).
                  eapply pairEq_neq. intuition.
                 revert dependent pff0.
                 revert dependent pff3.
                 revert dependent pff1.
                 unfold removeEntry. fold removeEntry.
                 rewrite EQ2,EQ3,removeEntry_swap.
                 assert (EQ4:
                          (n1, n2, vis, Chan lin empty t2)
               :: removeEntry (n, n0) (removeEntry (n1, n2) g3) =((n1, n2, vis, Chan lin empty t2)
               :: removeEntry (n1, n2) (removeEntry (n, n0) g3))).
                 erewrite removeEntry_swap.
                 tauto.
                 eauto. 
                 assert (EQ5:
                          (n1, n2, vis, Chan lin p t2)
               :: removeEntry (n, n0) (removeEntry (n1, n2) g0) =((n1, n2, vis, Chan lin p t2)
               :: removeEntry (n1, n2) (removeEntry (n, n0) g0))).
                 erewrite removeEntry_swap.
                 tauto.
                 eauto.
                 rewrite EQ4,EQ5.
                 intros.
                 eapply tEnv_split_add_vis.
                 eapply no_dup_removeEntry_no_dup...
                 econstructor...
                 intros ABS2. eapply not_lin_is_unrestricted in ABS2; intuition.
                 eapply split_remove.
                 eapply no_dup_split_no_dup_l with (pf := pf1)...
                 eapply no_dup_split_no_dup_r with (pf := pf1)...
                 eauto.
                 eauto.
                 eauto.
                 eauto.
                 eauto.
                 eauto.
                 intuition.
                 
                 all: try discriminate.
                 all: try destruct EX2 as [pp [tt EX2]]; try discriminate.
                 
                 
                 specialize flag_of_split_l with 
                     g0 g3 g1 pf0 pf3 pf1 (n1, n2) as FSPLIT.
                 apply FSPLIT in TS2 as [ABS1 [ABS2 ILL2]].
                 assert (flagOf g0 (n1, n2) ill).
                 apply F_Entry in TYPb... 
                 apply ILL2 in H as [[ILL3 ILL1] | [HID3 HID1]].
                 inversion ILL1.  subst.
                 inversion TYP1b. subst.
                 assert (ill = f0 /\ t = Chan lin q2 tb).
                 apply in_isMap with (x := (n1, n2)) (g := g1)...
                 destruct H4; subst...
                 
                 
                 inversion HID3; subst.
                 assert (ill = hid /\ Chan lin empty tb = t).
                 apply in_isMap with (x := (n1, n2)) (g := g3)...
                 destruct H3; contradiction.
                 eauto.
                 subst g3'.
                 eapply typeCheck_ill_vis.
                 eapply no_dup_split_no_dup_r with (pf := pf1)...
                 eauto.
                 subst... 

               ****
                 (* m = un *)
                 destruct G1 as [_ G1].
                 destruct G0 as [_ G0].
                 assert (SL : sl_pos p1)...

                 assert (ND_SL1: NoDup (secLabs p1)).
                 assert (TYP2 := TYP).
                 eapply typeCheck_no_dup in TYP as [_ ND_SL]; try simpl in ND_SL; try eapply no_dup_distr in ND_SL;
                   intuition.

                 assert (MAX0:
                          max (secLabs p1) <= max (domain g0)).
                 assert (TYP2 := TYP).
                 eapply typeCheck_no_dup in TYP as [INCL_SL _]; try simpl in INCL_SL.
                 erewrite split_max;
                   try eapply incl_preserves_max,incl_distr...
                 tauto.
                 assert (K0EQ: exists ne : list (name * name * flag * piType),
                            k0 = ne ++ (b1, b2, vis, r) :: removeEntry (b1, b2) g0)...
                 
                 assert (K1EQ: exists ne : list (name * name * flag * piType),
            k1 = ne ++ (b1, b2, vis, r') :: removeEntry (b1, b2) g1); try erewrite split_max in MAX0...
                 
                 destruct K0EQ as [ne0 K0EQ].
                 destruct K1EQ as [ne1 K1EQ].

                 assert (DISJ_ne0:
                          disjoint (domain ne0)
                            (domain ((b1, b2, vis, r) :: removeEntry (b1, b2) g0))).
                 subst k0; repeat rewrite domain_distr,no_dup_iff in nd_pfk0; intuition.

                

                 assert (DISJ_ne1:
                          disjoint (domain ne1)
                            (domain ((b1, b2, vis, r') :: removeEntry (b1, b2) g1))).
                 
                 
                  subst k1; repeat rewrite domain_distr,no_dup_iff in nd_pfk1; intuition.
                 
                 
                 move LTS1 at bottom. move LTS0 at bottom.
                 assert (NE:
                            ne0 = nil \/
       exists q,
         replication p1 p2 q /\
         incl (secLabs q) (secLabs p1) /\
         ne0 = newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0))).
                 eapply lts_un_input_action_newEntries...

                 
                 destruct NE.
                 
                 (* NON REPLICATED INPUT *)
                 *****
                   clear TYPILL.
                   assert (NE1NIL: ne1 <> nil -> False).
                 intros ABS.
                 eapply lts_un_input_action_newEntries
                   with (k := ne1) (pf := nd_pf1) in LTS1 as ABS1.
                 destruct ABS1 as [ABS1 | ABS1]. contradiction.
                 destruct ABS1 as [rp [RP [INrp EQN]]].
                 eapply lts_un_input_action_newEntries_2  with (k := ne0) (q := rp) (pf := nd_pf0) in LTS0 as ABS0.
                 assert (newEntries g1 (secLabs (dep_relabel rp (domain g1) nd_pf1)) (max (domain g1)) = nil).
                 eapply newEntries_nil with (g := g0).
                 eauto.
                 intros. 
                 eapply split_domain_l...
                 assert (MAX: max (domain g0) = max (domain g1)).
                 eapply split_max...
                 erewrite <-MAX, max_dep_relabel with (nd_pf1 := nd_pf0).
                 subst...
                 eauto.
                 subst; contradiction.
                 all:eauto.
                 apply NNPP in NE1NIL.
                 subst.
                 
                 inversion H8. subst.
                 assert (p0 = p). inversion H7...
                 subst.

                 
                 
                 inversion TYP1b; subst.
                 assert (q2 = empty).
                 assert (pol_plus empty empty q2).
                 eapply split_plus_lin with
                     (b1 := n1) (pf1 := pf0) (pf2 := pf3) (pf3 := pf1).
                 eauto.
                 eauto.
                 eauto.
                 eauto.
                 inversion H3...
                 subst.
                 assert (p = p7).
                 inversion H11...
                 subst p7.
                 
                 eapply TPar with  (pf1 := pfk0) (pf2 := pf3').
                 eapply tEnv_split_add_vis.
                 eauto.
                 eauto.
                 intros ABS.  eapply not_lin_is_unrestricted in ABS; intuition.
                 eauto.
                 eauto.
                 eapply typeCheck_ill_vis.
                 eapply no_dup_split_no_dup_r with (pf := pf1)...
                 eauto.
                 eauto.
                  (* REPLICATED INPUT *)
                 *****
                   destruct H12 as
                     [rp [RP [INRP EQN0]]].
                 eapply lts_un_input_action_newEntries_2  with (k := ne1) (q := rp) (pf := nd_pf1) in LTS1 as EQN1.

                 

                 assert  (nd_pfne0:
                           NoDup (domain ne0)).
                 subst. erewrite domain_distr in nd_pfk0; eapply no_dup_distr in nd_pfk0. intuition.

                 assert (nd_pfne1:
                           NoDup (domain ne1)).
                 subst. erewrite domain_distr in nd_pfk1; eapply no_dup_distr in nd_pfk1. intuition.
                 
                 
                 remember
                   (newEntries g3 (secLabs (dep_relabel rp (domain g3) nd_pf3)) (max (domain g3))) as ne3.

                 assert (nd_pfne3:
                           NoDup (domain ne3)).
                 subst ne3; eapply newEntries_no_dup.
                 eapply wf_rewrite,prop27,incl_incl2.
                 eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
                 eauto.
                 eapply incl_tran with (m := secLabs p1)...
                 assert(  incl (secLabs p1) (domain g0)).
                 eapply typeCheck_no_dup with (pf := pf0)...
                 eapply incl_iff with (m1 := domain g0);
                   try eassumption.
                 intros; eapply split_domain_m...
                 eauto.
                 
                 assert (nd_pfk3:
                           NoDup
                             (domain
                                (ne3 ++
                                     ((b1, b2, vis, Chan lin empty tb)
                                        :: removeEntry (b1, b2) g3)))).
                 erewrite domain_distr, no_dup_iff.
                 split. assumption.
                 split. eapply no_dup_cons_removeEntry...
                 erewrite disjoint_commute. subst ne3.
                 assert (DIS: disjoint (domain g3)
    (domain
       (newEntries g3 (secLabs (dep_relabel rp (domain g3) nd_pf3))
          (max (domain g3))))).
                 eapply new_entries_disjoint.
                 unfold sl_pos, pos in *; intros.
                 specialize SLP with x1 x2;
                   unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INRP; specialize INRP with (x1,x2); intuition.
                 assert (MAX: max(domain g1) >= max (secLabs rp)).
                 eapply incl_preserves_max, incl_tran with (m := secLabs p1)... assert(  incl (secLabs p1) (domain g0)).
                 eapply typeCheck_no_dup with (pf := pf0)...
                 eapply incl_iff with (m1 := domain g0)...
                erewrite split_max with (pf := pf1). lia.
                eapply split_comm...
                eapply disjoint_iff with (l1  := domain g3), in_removeEntry_cons_iff,in_g_in_domain...
                

                 eapply no_dup_isMap in nd_pfk3 as pfk3.
                 eapply no_dup_isMap in nd_pfne0 as pfne0.
                 eapply no_dup_isMap in nd_pfne3 as pfne3.
                 eapply no_dup_isMap in nd_pfne1 as pfne1.
                 
                 eapply TPar with
                     (pf1 := pfk0) (pf2 := pfk3) (pf := pfk1).
                 
                

                 (* tEnv_split k0 (ne3 ++ (b1, b2, vis, Chan lin empty tb) :: removeEntry (b1, b2) g3) k1 pfk0 pfk3
    pfk1*)
                 inversion TYP1b. subst.
                 assert (PP: pol_plus empty empty q2).
                 eapply split_plus_lin with (pf1 := pf0) (pf2 := pf3) (pf3 := pf1) (b1 := n1) (b2 := n2)...
                 assert (p = p7).
                 assert (q2 = empty).
                 inversion PP...
                 subst.
                 inversion H11.  subst.
                 inversion H7. subst...
                 subst.
                 inversion H8; subst...
                 inversion H8; subst...
                 inversion H7; subst...
                 subst p7.
               
                 eapply split_distr with
                     (pf1 := pfne0) (pf2 := pfne3) (pf := pfne1).
                 subst.
                 eapply split_newEntries...
                 eapply tEnv_split_add_vis.
                 eauto.
                 eauto.
                 intros ABS; eapply not_lin_is_unrestricted in ABS; intuition.
                 eauto.
                 
                 eauto.
                 eapply typeCheck_weak2 with (pfk := pfne3).
                 erewrite <-domain_distr...
                 eapply typeCheck_ill_vis.
                 eauto.
                 eauto.
                 subst...

                 (* cons ne3 ?pfk *)
                 assert (INVNE: forall c1 c2 ff tt,
                            In (c1, c2, ff, tt) ne3 ->
                            In (c1, c2 - max (domain g3)) (secLabs rp) /\ In (c1, c2 - max (domain g3), ff, tt) g3).
                 intros.
                 eapply inverse_newEntries.
                 eauto.
                 (* sl_pos rp *)
                 eapply sl_pos_par_l in SLP;
                   unfold sl_pos in SLP;
                   unfold sl_pos.
                 eapply incl_pos with (l2 :=(secLabs p1))...
                 (* incl (secLabs rp) (domain g3) *)
                 eapply incl_tran with (m := secLabs p1).
                 assumption.
                 eapply incl_iff with (m1 := domain g0).
                 eapply typeCheck_no_dup with (pf := pf0)...
                 intros. eapply split_domain_m...
                 (*In (c1, c2, ff, tt)
    (newEntries g3
       (map (fun x : name * name => (fst x, snd x + max (domain g3))) (secLabs rp))
       (max (domain g3)))*)
                 subst. erewrite <-identif_seclabs_of_dep_relabel...
                
                 eapply cons_char.
                 destruct ne3. left...
                 right. intros.
                 specialize INVNE with c1 c2 ff tt.
                 apply INVNE in H12; clear INVNE.
                 destruct H12 as [INSL IN3].
                 remember (c2 - max (domain g3)) as c''.
                 assert (ff = ill).
                 assert (IN1: In (c1, c'') (secLabs p1)).
                 eapply INRP...
                 assert (NOTINSL: ~In (c1, c'') (secLabs p3)).
                 intros ABS.
                 assert (ND: NoDup (secLabs (dPar p1 p3))).
                 eapply typeCheck_no_dup with (pf := pf1)...
                 unfold secLabs in ND. fold secLabs in ND.
                 erewrite no_dup_iff in ND; destruct ND as [ND1 [ND2 DIS]].
                  eapply disjoint_absurd...
                 assert (NOTINFN: ~ In (c1, c'') (fn p3)).
                 intros ABS.
                 assert (DIS: disjoint (fn (dPar p1 p3)) (secLabs (dPar p1 p3))).
                 eapply fn_disjoint_sl with (pf := pf1)...
                 unfold fn, secLabs in DIS;
                   fold fn in DIS; fold secLabs  in DIS.
                 eapply disjoint_absurd with (x:= (c1, c'')) (l := (fn p1 ++ fn p3)) (m := (secLabs p3 ++ secLabs p1)).
                 eauto. eapply in_app_iff; right...
                 eapply in_app_iff; right...
                 assert (IN0: exists tt, In (c1, c'', hid, tt) g0).
                 eapply typeCheck_hid...
                 destruct IN0 as [ttt F0].
                 assert (F1: In (c1, c'') (domain g1)). 
                 eapply split_domain_l_2 with (x := (c1, c'')) in H1; move H1 at bottom.
                 eapply in_g_in_domain in F0; intuition.
                 eapply in_domain_in_g in F1.
                 destruct F1 as [f1 [tt1 F1]].
                 assert (FP: exists f3, flagOf g3 (c1, c'') f3 /\ flag_plus hid f3 f1).
                 eapply split_flag_plus with (pf1 := pf0) (pf2 := pf3) (pf := pf1)...
                 destruct FP as [f3' [F3 FP]].
                 assert (ff = f3').
                 eapply flag_of_map with (g := g3) (x := (c1, c''))...
                 subst ff.
                 assert (F1': flagOf g1 (c1, c'')  hid).
                 eapply fsub_hid...
                 inversion F1'. subst g4 n3 f0.
                 assert (f1 = hid).
                 eapply flag_of_map with (g := g1) (x := (c1, c''))...
                 subst f1.
                 inversion FP...

                 subst.
                 eapply typeCheck_ill with (p := p3)...

                 subst ne3;
                   rewrite identif_seclabs_of_dep_relabel in *;
                   eapply Peirce; intros ABS;
                   eapply not_disjoint in ABS as ([x1 x2] &ABS1 &ABS2);
                   eapply in_bv_lt_max with (pf := pf3) in ABS1;
                   eapply in_domain_in_g in ABS2 as (ff &tt &ABS2);
                   eapply newEntries_gte_max in ABS2;
                   try lia;
                   try eassumption.
                 
                 all:eauto.
                 
               ****
                 apply type_plus_comm...
               ****
                 apply type_plus_comm...
               ****
                 destruct EX as [pp [tt ABS]]; inversion ABS; discriminate.
               ****
                 subst...
             *** 
               (* f = vis *)
               assert (f3 = vis).
               assert (FVIS: flagOf g3 (b1, b2) vis /\ flagOf g1 (b1, b2) vis).
               eapply flag_of_split_l...
               destruct FVIS as [F3 _].
               inversion F3; subst.
               eapply flag_of_map with (g:=g3)...
               
               subst f3.
               assert (TC3 := H3).
               specialize typeCheck_vis with
                   (b1, b2) (Chan lin q3 tb) g3 pf3 p3 as TYPVIS.
               apply TYPVIS in H3 as EX. move EX at bottom.
               assert (nd_pf3' :
                         NoDup (domain 
                           (((b1, b2), vis, Chan lin q3 tb)
                              :: removeEntry (b1, b2) g3))).
               eapply no_dup_cons_removeEntry, no_dup_split_no_dup_r with (pf1 := pf0) (pf := pf1)...
               eapply no_dup_isMap in nd_pf3' as pf3'.
               move pf3' at top.
               specialize IHLTS with
                   (k1 := k0) (g1 := g0)
                   (g2 := w2) (pf1 := pf0) (pf2 := pfw2)
                   (pfk1 := pfk0) (pf := pf) (nd_pf1 := nd_pf0).
               apply IHLTS in IH1. clear IHLTS.
               
               all:eauto.

               assert (TC2 := H2).
               apply lts_inp with
                   (ta :=  (Chan m q t))
                   (tb := (Chan lin p tb))
                   (m := m)
                   (q := q)
                   (t := t)
                   (r := r)
                 in LTS0 as G0.
               

               inversion  TYPa. subst g4 n3 t0.
               apply tsub_payload with
                   g0 g3 g1 pf0 pf3 pf1 a1 a2 f m q t in H as K. 
               destruct K as [q1 TYP1a].
               apply tsub_payload with
                   g0 g3 g1 pf0 pf3 pf1 b1 b2 vis lin p tb in TYPb as K.
               destruct K as [q2 TYP1b].
               
                assert (lts_input_exists_plus:
                         exists r',
                           type_plus t (Chan lin q2 tb) r').
               assert (AFT: exists (f : flag) (m : mode) (q : pol) (t r tb : piType),
    typeOf g1 (a1, a2) (Chan m q t) /\ In (b1, b2, f, tb) g1 /\ f <> hid /\ type_plus t tb r).
               eapply lts_after_inp...
               destruct AFT as
                   [ff [mm [qq [tt [rr [ttb [TYPP [INN [_ TPP]]]]]]]]].
               assert (Chan lin q2 tb = ttb).
               eapply type_of_map with (g := g1) (x := (b1, b2))...
               assert (t = tt).
               assert (Chan m q1 t = Chan mm qq tt).
                eapply type_of_map with (g := g1) (x := (a1, a2))...
                inversion H4; subst... 
                exists rr; subst...
                
                
               destruct lts_input_exists_plus as [r' TP2].
               assert (LTS1:  lts g1 p1 (aIn a1 a2 b1 b2) k1 p2 nd_pf1). 
               inversion LTSPAR...
               apply lts_inp with
                   (ta :=  Chan m q1 t)
                   (tb := (Chan lin q2 tb))
                   (m := m)
                   (q := q1)
                   (t := t)
                   (r := r')
                 in LTS1 as G1.
               
               assert (TP0 := TP).
               inversion TP. subst t0.
               assert (TP20 := TP2).
               inversion TP2.
               all: eauto.
               destruct m.
               ****
                 (*remember ((((b1, b2), vis, Chan lin empty tb)
                              :: removeEntry (b1, b2) g3))
                   as g3'.*)
                 
                 apply TPar with
                     (pf1 := pfk0) (pf2 := pf3').

                 (* HYP *)
                 (* g1>p1 -a-> k1>p2 *)
                 (* g0>p1 -a-> k0>p2 *)
                 (* g0 + g3 = g1 *)
                 (* g3(b)= (ill, Chan lin q3 t) *)
                 (* g3' = g3 \b, (vis, Chan lin empty t) *)
                 (* GOAL *)
                 (* k0 + g3' = k1 *) 

                 
                 
                 
                 destruct G0 as [G0 ABS].
                 assert (K0 : lin=lin). tauto.
                 apply G0 in K0 as W0.
                 apply G1 in K0 as W1.
                 revert dependent pfk0; rewrite W0.
                 revert dependent pfk1; rewrite W1.
                 intros.
                 subst.
                 
                 
                 inversion H8. subst.
                 remember p as pp. subst p.
                 remember p0 as p. subst p0.
                 remember tb as t2. subst tb.
                 (* HYP:  tEnv_split g0 g3 g1 pf0 pf3 pf1 *)
                 (* GOAL:   tEnv_split
    ((n, n0, vis, Chan lin empty (Chan lin p0 tb))
     :: (n1, n2, vis, Chan lin p5 tb)
        :: removeEntry (n, n0) (removeEntry (n1, n2) g0)) g3
    ((n, n0, vis, Chan lin empty (Chan lin p0 tb))
     :: (n1, n2, vis, Chan lin p8 tb)
        :: removeEntry (n, n0) (removeEntry (n1, n2) g1)) pfk0 pf3 pfk1 *)
                 assert
                   (nd_pff0: NoDup (domain
                             (removeEntry (n, n0)
                                          ((n, n0, vis, Chan lin empty (Chan lin p t2))
                                             :: (n1, n2, vis, Chan lin p5 t2) :: removeEntry (n, n0) (removeEntry (n1, n2) g0))))).
                   unfold removeEntry. fold removeEntry.
                 assert (EQ2:  pair_eq (n, n0) (n, n0) = true). eauto.  rewrite EQ2.
                 erewrite removeEntry_swap.
                 eapply no_dup_cons_removeEntry, no_dup_removeEntry_no_dup...
                 eauto.
                 assert (nd_pff3:
                           NoDup (domain (removeEntry (n, n0)((n1, n2, vis, Chan lin q3 t2) :: removeEntry (n1, n2) g3)))).
                 eapply no_dup_removeEntry_no_dup, no_dup_cons_removeEntry,no_dup_split_no_dup_r with (pf := pf1)...
                 assert (nd_pff1:
                           NoDup (domain (
                 removeEntry (n, n0)
   ((n, n0, vis, Chan lin empty (Chan lin p t2))
      :: (n1, n2, vis, Chan lin p8 t2) :: removeEntry (n, n0) (removeEntry (n1, n2) g1))))).
                   unfold removeEntry. fold removeEntry.
                 assert (EQ2:  pair_eq (n, n0) (n, n0) = true). eauto.  rewrite EQ2.
                 erewrite removeEntry_swap.
                 eapply no_dup_cons_removeEntry, no_dup_removeEntry_no_dup...
                 eauto.
                 apply no_dup_isMap in nd_pff3 as pff3; eapply  no_dup_isMap in nd_pff0 as pff0;eapply  no_dup_isMap in nd_pff1 as pff1.
                
                 
                 eapply SpLin with (n := (n, n0)) (f := vis) (p := empty) (pf' := pff0) (pf'' := pff3) (pf''' := pff1).
                 eauto. eauto. eauto. right.
                 (*In (n, n0, vis, Chan lin empty (Chan lin p t2)) (removeEntry (n1, n2) g3)*)
              
                 remember H as KK. subst H.
                 assert (q1 = inp).
                 assert (exists t : piType,
    typeOf g1 (n, n0) (Chan lin inp t) \/
    typeOf g1 (n, n0) (Chan un inp t) \/ typeOf g1 (n, n0) (Chan un io t)).
                 eapply type_of_in_action...
                 destruct H as
                     [tt [TYP1 | [TYP1 | TYP1]]].
                 assert (Chan lin q1 (Chan lin p t2) =
                         Chan lin inp tt).
                 eapply type_of_map with (x := (n, n0)) (g := g1)...
                 inversion H...
                  assert (Chan lin q1 (Chan lin p t2) =
                         Chan un inp tt).
                 eapply type_of_map with (x := (n, n0)) (g := g1)...
                 inversion H...
                  assert (Chan lin q1 (Chan lin p t2) =
                         Chan un io tt).
                 eapply type_of_map with (x := (n, n0)) (g := g1)...
                 inversion H...
                 subst.
                 assert (q = inp).
                 assert (exists t : piType,
    typeOf g0 (n, n0) (Chan lin inp t) \/
    typeOf g0 (n, n0) (Chan un inp t) \/ typeOf g0 (n, n0) (Chan un io t)).
                 eapply type_of_in_action...
                 destruct H as
                     [tt [TYP1 | [TYP1 | TYP1]]].
                 assert (Chan lin q (Chan lin p t2) =
                         Chan lin inp tt).
                 eapply type_of_map with (x := (n, n0)) (g := g0)...
                 inversion H...
                  assert (Chan lin q (Chan lin p t2) =
                         Chan un inp tt).
                 eapply type_of_map with (x := (n, n0)) (g := g0)...
                 inversion H...
                  assert (Chan lin q (Chan lin p t2) =
                         Chan un io tt).
                 eapply type_of_map with (x := (n, n0)) (g := g0)...
                 inversion H...
                 subst.
                 inversion TYP1a; subst.
                 eapply tsuper_payload_r with (pf2 := pf3) in H as K.
                 destruct K as [pp3 TYP3].
                 inversion TYP3; subst.
                 assert (pol_plus inp pp3 inp).
                 eapply split_plus_lin with (pf1 := pf0) (pf2 := pf3) (pf3 := pf1)...
                 assert (pp3 = empty).
                 inversion H4...
                 subst.
                 assert (F0: flagOf g0 (n, n0) vis).
                 eapply lts_vis_subject...
                 inversion F0; subst.
                 eapply fsub_vis with (pf := pf1) in H5.
                 inversion H5; subst.
                 eapply fsuper_vis with (pf2 := pf3) in H6.
                 destruct H6 as [_ K].
                 inversion K; subst.
                 assert (f1 = vis /\  Chan lin empty (Chan lin p t2) = t1).
                 eapply in_isMap with (g := g3)...
                 destruct H9; subst.
                 eapply removeEntry_in.
                 (*(n, n0) <> (n1, n2)*)
                 eauto.
                 assumption.
                 eauto. eauto. eauto.
   
                 (*tEnv_split
    (removeEntry (n, n0)
       ((n, n0, vis, Chan lin empty (Chan lin p t2))
        :: (n1, n2, vis, Chan lin p t2) :: removeEntry (n, n0) (removeEntry (n1, n2) g0)))
    (removeEntry (n, n0) ((n1, n2, vis, Chan lin empty t2) :: removeEntry (n1, n2) g3))
    ?g''' ?pf' ?pf'' ?pf'''*)

                  assert (EQ2:  pair_eq (n, n0) (n, n0) = true).
                  eauto.
                  assert (EQ3: pair_eq (n1, n2) (n, n0) = false).
                  eapply pairEq_neq.  intuition.
                  assert (EQ4:
                          (n1, n2, vis, Chan lin q3 t2)
               :: removeEntry (n, n0) (removeEntry (n1, n2) g3) =((n1, n2, vis, Chan lin q3 t2)
               :: removeEntry (n1, n2) (removeEntry (n, n0) g3))).
                 erewrite removeEntry_swap.
                 tauto.
                 eauto.
                 assert (EQ5:
                          (n1, n2, vis, Chan lin p5 t2)
               :: removeEntry (n, n0) (removeEntry (n1, n2) g0) =((n1, n2, vis, Chan lin p5 t2)
               :: removeEntry (n1, n2) (removeEntry (n, n0) g0))).
                 erewrite removeEntry_swap.
                 tauto.
                 eauto.
                 revert dependent pff0.
                 revert dependent pff3.
                 revert dependent pff1.
                 unfold removeEntry. fold removeEntry.
                 rewrite EQ2,EQ3,removeEntry_swap.
                 
                 rewrite EQ4,EQ5.
                 intros.
                 eapply tEnv_split_add_vis.
                 eapply no_dup_removeEntry_no_dup...
                 inversion TYP1b. subst.
                 assert (PP: pol_plus pp q3 q2).
                 eapply split_plus_lin with (b1 := n1) (b2 := n2) (pf1 := pf0) (pf2 := pf3) (pf3 := pf1)...
                  (* p + pp = p5
                    p + q2 = p8  
                    pp + q3 = q2 *)
                 (* GOAL *)
                 (* p5 + q3 = p8 *)
                 (* p + pp + q3 = p8 *)
                 (* p + pp + q3 = p + q2 *)
                 (* p + q2 = p + q2 *)
                 econstructor.
                 move H7 at bottom. move H11 at bottom. move  PP at bottom.
                 destruct p.
                 inversion H7; inversion H11; inversion PP; subst...
                 inversion H7; inversion H11; inversion PP; subst; eauto; try discriminate.
                 inversion H7; inversion H11; inversion PP; subst; eauto; try discriminate.
                 inversion H7; inversion H11; inversion PP; subst; eauto; try discriminate.
                 intros ABS2; eapply not_lin_is_unrestricted in ABS2; intuition.
                 
                 eapply split_remove.
                 eapply no_dup_split_no_dup_l with (pf := pf1)...
                 eapply no_dup_split_no_dup_r with (pf := pf1)...
                 eauto.
                 eauto.
                 eauto.
                 eauto.
                 eauto.
                 eauto.
                 intuition.

                
                 eapply typeCheck_impl with (pf1 := pf3)...
                 intuition.
                 case_eq (pair_eq (a, b3) (b1, b2)).
                 intros PEQ. rewrite <-pairEq_eq in PEQ; inversion PEQ;  subst.
                 assert (b0 = vis /\ b = Chan lin q3 tb).
                 eapply in_isMap...
                 intuition; subst...
                 intros PNEQ.
                 right.
                 rewrite <-pairEq_neq in PNEQ.
                 eapply removeEntry_in...
(*                 case_eq (pair_eq (a, b3) (b1, b2)).
                 intros PEQ. rewrite <-pairEq_eq in PEQ; inversion PEQ;  subst.*)
                 inversion H14. inversion H18; subst...
                 eapply in_removeEntry...
               ****
                 (* m = un *)
                    
                 destruct G1 as [_ G1].
                 destruct G0 as [_ G0].

                 assert (SL : sl_pos p1).
                 eapply sl_pos_par_l...

                 assert (ND_SL1: NoDup (secLabs p1)).
                 assert (TYP2 := TYP).
                 eapply typeCheck_no_dup in TYP as [_ ND_SL]; try simpl in ND_SL; try eapply no_dup_distr in ND_SL;
                   intuition.

                 assert (MAX0:
                          max (secLabs p1) <= max (domain g0)).
                 assert (TYP2 := TYP).
                 eapply typeCheck_no_dup in TYP as [INCL_SL _]; try simpl in INCL_SL.
                 erewrite split_max;
                   try eapply incl_preserves_max,incl_distr...
                 tauto.


              
                 
                 assert (K0EQ: exists ne : list (name * name * flag * piType),
                            k0 = ne ++ (b1, b2, vis, r) :: removeEntry (b1, b2) g0)...

                 
                 erewrite split_max with (g := g1) in MAX0...
                 assert (K1EQ: exists ne : list (name * name * flag * piType),
            k1 = ne ++ (b1, b2, vis, r') :: removeEntry (b1, b2) g1)...
                 
                 destruct K0EQ as [ne0 K0EQ].
                 destruct K1EQ as [ne1 K1EQ].

                    assert (DISJ_ne0:
                          disjoint (domain ne0)
                            (domain ((b1, b2, vis, r) :: removeEntry (b1, b2) g0))).
                 subst k0; repeat rewrite domain_distr,no_dup_iff in nd_pfk0; intuition.

                

                 assert (DISJ_ne1:
                          disjoint (domain ne1)
                            (domain ((b1, b2, vis, r') :: removeEntry (b1, b2) g1))).
                 
                 
                 subst k1; repeat rewrite domain_distr,no_dup_iff in nd_pfk1; intuition.
                 move LTS1 at bottom. move LTS0 at bottom.
                 assert (NE:
                            ne0 = nil \/
       exists q,
         replication p1 p2 q /\
         incl (secLabs q) (secLabs p1) /\
         ne0 = newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0))).
                 eapply lts_un_input_action_newEntries...
                 destruct NE.
                 
                 (* NON REPLICATED INPUT *)
                 *****
                    assert (NE1NIL: ne1 <> nil -> False).
                 intros ABS.
                 eapply lts_un_input_action_newEntries
                   with (k := ne1) (pf := nd_pf1) in LTS1 as ABS1.
                 destruct ABS1 as [ABS1 | ABS1]. contradiction.
                 destruct ABS1 as [rp [RP [INrp EQN]]].
                 eapply lts_un_input_action_newEntries_2  with (k := ne0) (q := rp) (pf := nd_pf0) in LTS0 as ABS0.
                 assert (newEntries g1 (secLabs (dep_relabel rp (domain g1) nd_pf1)) (max (domain g1)) = nil).
                 eapply newEntries_nil with (g := g0).
                 eauto.
                 intros. 
                 eapply split_domain_l...
                 assert (MAX: max (domain g0) = max (domain g1)).
                 eapply split_max...
                 erewrite <-MAX, max_dep_relabel with (nd_pf1 := nd_pf0).
                 subst...
                 eauto.
                 subst; contradiction.
                 all:eauto.
                 apply NNPP in NE1NIL.
                 subst.
                 
                 inversion H8. subst.

                 
                 
                 inversion TYP1b; subst.
                 
                 eapply TPar with  (pf1 := pfk0) (pf2 := pf3').
                 eapply tEnv_split_add_vis.
                 eauto.
                  assert (PP: pol_plus p q3 q2).
                 eapply split_plus_lin with (b1 := n1) (b2 := n2) (pf1 := pf0) (pf2 := pf3) (pf3 := pf1)...
                 econstructor.
                  (* p + pp = p5
                    p + q2 = p8  
                    pp + q3 = q2 *)
                 (* GOAL *)
                 (* p5 + q3 = p8 *)
                 (* p + pp + q3 = p8 *)
                 (* p + pp + q3 = p + q2 *)
                 (* p + q2 = p + q2 *)
                 move H7 at bottom. move H11 at bottom. move  PP at bottom.
                 destruct p0.
                 inversion H7; inversion H11; inversion PP; subst;eauto;try discriminate.
                 inversion H7; inversion H11; inversion PP; subst; eauto; try discriminate.
                 inversion H7; inversion H11; inversion PP; subst; eauto; try discriminate.
                 inversion H7; inversion H11; inversion PP; subst; eauto; try discriminate.
                 intros ABS2; eapply not_lin_is_unrestricted in ABS2; intuition.
                 
                 
                 eauto.
                 eauto.

                 eapply typeCheck_impl with (pf1 := pf3)...
                 intuition.
                 case_eq (pair_eq (a, b1) (n1, n2)).
                 intros PEQ. rewrite <-pairEq_eq in PEQ; inversion PEQ;  subst.
                 assert (b0 = vis /\ b = Chan lin q3 tb).
                 eapply in_isMap...
                 intuition; subst...
                 intros PNEQ.
                 right.
                 rewrite <-pairEq_neq in PNEQ.
                 eapply removeEntry_in...
(*                 case_eq (pair_eq (a, b3) (b1, b2)).
                 intros PEQ. rewrite <-pairEq_eq in PEQ; inversion PEQ;  subst.*)
                 destruct H6 as [H10|H10]. inversion H10; subst...
                 eapply in_removeEntry...

                  (* REPLICATED INPUT *)
                 *****
                   destruct H12 as
                     [rp [RP [INRP EQN0]]].
                 eapply lts_un_input_action_newEntries_2  with (k := ne1) (q := rp) (pf := nd_pf1) in LTS1 as EQN1.

                

                 assert  (nd_pfne0:
                           NoDup (domain ne0)).
                 subst. erewrite domain_distr in nd_pfk0; eapply no_dup_distr in nd_pfk0. intuition.

                 assert (nd_pfne1:
                           NoDup (domain ne1)).
                 subst. erewrite domain_distr in nd_pfk1; eapply no_dup_distr in nd_pfk1. intuition.
                 
                               remember
                   (newEntries g3 (secLabs (dep_relabel rp (domain g3) nd_pf3)) (max (domain g3))) as ne3.

                 assert (nd_pfne3:
                           NoDup (domain ne3)).
                 subst ne3; eapply newEntries_no_dup.
                 eapply wf_rewrite,prop27,incl_incl2.
                 eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
                 eauto.
                 eapply incl_tran with (m := secLabs p1)...
                 assert(  incl (secLabs p1) (domain g0)).
                 eapply typeCheck_no_dup with (pf := pf0)...
                 eapply incl_iff with (m1 := domain g0);
                   try eassumption.
                 intros; eapply split_domain_m...
                 eauto.
                 
                 assert (nd_pfk3:
                           NoDup
                             (domain
                                (ne3 ++
                                     ((b1, b2, vis, Chan lin q3 tb)
                                        :: removeEntry (b1, b2) g3)))).
                 erewrite domain_distr, no_dup_iff.
                 split. assumption.
                 split. eapply no_dup_cons_removeEntry...
                 erewrite disjoint_commute. subst ne3.
                 assert (DIS: disjoint (domain g3)
    (domain
       (newEntries g3 (secLabs (dep_relabel rp (domain g3) nd_pf3))
          (max (domain g3))))).
                 eapply new_entries_disjoint.
                 unfold sl_pos, pos in *; intros.
                 specialize SLP with x1 x2;
                   unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INRP; specialize INRP with (x1,x2); intuition.
                 assert (MAX: max(domain g1) >= max (secLabs rp)).
                 eapply incl_preserves_max, incl_tran with (m := secLabs p1)... assert(  incl (secLabs p1) (domain g0)).
                 eapply typeCheck_no_dup with (pf := pf0)...
                 eapply incl_iff with (m1 := domain g0)...
                erewrite split_max with (pf := pf1). lia.
                eapply split_comm...
                eapply disjoint_iff with (l1  := domain g3), in_removeEntry_cons_iff,in_g_in_domain...

                 eapply no_dup_isMap in nd_pfk3 as pfk3.
                 eapply no_dup_isMap in nd_pfne0 as pfne0.
                 eapply no_dup_isMap in nd_pfne3 as pfne3.
                 eapply no_dup_isMap in nd_pfne1 as pfne1.
                 
                 eapply TPar with
                     (pf1 := pfk0) (pf2 := pfk3) (pf := pfk1).


                 (* tEnv_split k0 (ne3 ++ (b1, b2, vis, Chan lin q2 tb) :: removeEntry (b1, b2) g3) k1 pfk0 pfk3
    pfk1*)
                 inversion TYP1b. subst.
                  assert (PP: pol_plus p q3 q2).
                 eapply split_plus_lin with (b1 := n1) (b2 := n2) (pf1 := pf0) (pf2 := pf3) (pf3 := pf1)...

               
                 eapply split_distr with
                     (pf1 := pfne0) (pf2 := pfne3) (pf := pfne1).
                 subst.
                 eapply split_newEntries...
                 eapply tEnv_split_add_vis.
                 eauto.
                 econstructor.
                 inversion H8; subst.
                  (* p + pp = p5
                    p + q2 = p8  
                    pp + q3 = q2 *)
                 (* GOAL *)
                 (* p5 + q3 = p8 *)
                 (* p + pp + q3 = p8 *)
                 (* p + pp + q3 = p + q2 *)
                 (* p + q2 = p + q2 *)
                 move H7 at bottom. move H11 at bottom. move  PP at bottom.
                   destruct p0.
                 inversion H7; inversion H11; inversion PP; subst;eauto;try discriminate.
                 inversion H7; inversion H11; inversion PP; subst; eauto; try discriminate.
                 inversion H7; inversion H11; inversion PP; subst; eauto; try discriminate.
                 inversion H7; inversion H11; inversion PP; subst; eauto; try discriminate.
                 intros ABS2; eapply not_lin_is_unrestricted in ABS2; intuition.


                 
                 eauto.
                 eauto.
                 eapply typeCheck_weak2 with (pfk := pfne3).
                 erewrite <-domain_distr...
                  eapply typeCheck_impl with (pf1 := pf3)...
                 intuition.
                 case_eq (pair_eq (a, b3) (b1, b2)).
                 intros PEQ. rewrite <-pairEq_eq in PEQ; inversion PEQ;  subst.
                 assert (b0 = vis /\ b = Chan lin q3 tb).
                 eapply in_isMap...
                 intuition; subst...
                 intros PNEQ.
                 right.
                 rewrite <-pairEq_neq in PNEQ.
                 eapply removeEntry_in...
(*                 case_eq (pair_eq (a, b3) (b1, b2)).
                 intros PEQ. rewrite <-pairEq_eq in PEQ; inversion PEQ;  subst.*)
                 inversion H15. inversion H16; subst...
                 eapply in_removeEntry...

                 (* cons ne3 ?pfk *)
                 assert (INVNE: forall c1 c2 ff tt,
                            In (c1, c2, ff, tt) ne3 ->
                            In (c1, c2 - max (domain g3)) (secLabs rp) /\ In (c1, c2 - max (domain g3), ff, tt) g3).
                 intros.
                 eapply inverse_newEntries.
                 eauto.
                 (* sl_pos rp *)
                 eapply sl_pos_par_l in SLP;
                   unfold sl_pos in SLP;
                   unfold sl_pos.
                 eapply incl_pos with (l2 :=(secLabs p1))...
                 (* incl (secLabs rp) (domain g3) *)
                 eapply incl_tran with (m := secLabs p1).
                 assumption.
                 eapply incl_iff with (m1 := domain g0).
                 eapply typeCheck_no_dup with (pf := pf0)...
                 intros. eapply split_domain_m...
                 (*In (c1, c2, ff, tt)
    (newEntries g3
       (map (fun x : name * name => (fst x, snd x + max (domain g3))) (secLabs rp))
       (max (domain g3)))*)
                 subst. erewrite <-identif_seclabs_of_dep_relabel...
                
                 eapply cons_char.
                 destruct ne3. left...
                 right. intros.
                 specialize INVNE with c1 c2 ff tt.
                 apply INVNE in H12; clear INVNE.
                 destruct H12 as [INSL IN3].
                 remember (c2 - max (domain g3)) as c''.
                 assert (ff = ill).
                 assert (IN1: In (c1, c'') (secLabs p1)).
                 eapply INRP...
                 assert (NOTINSL: ~In (c1, c'') (secLabs p3)).
                 intros ABS.
                 assert (ND: NoDup (secLabs (dPar p1 p3))).
                 eapply typeCheck_no_dup with (pf := pf1)...
                 unfold secLabs in ND. fold secLabs in ND.
                 erewrite no_dup_iff in ND; destruct ND as [ND1 [ND2 DIS]].
                  eapply disjoint_absurd...
                 assert (NOTINFN: ~ In (c1, c'') (fn p3)).
                 intros ABS.
                 assert (DIS: disjoint (fn (dPar p1 p3)) (secLabs (dPar p1 p3))).
                 eapply fn_disjoint_sl with (pf := pf1)...
                 unfold fn, secLabs in DIS;
                   fold fn in DIS; fold secLabs  in DIS.
                 eapply disjoint_absurd with (x:= (c1, c'')) (l := (fn p1 ++ fn p3)) (m := (secLabs p3 ++ secLabs p1)).
                 eauto. eapply in_app_iff; right...
                 eapply in_app_iff; right...
                 assert (IN0: exists tt, In (c1, c'', hid, tt) g0).
                 eapply typeCheck_hid...
                 destruct IN0 as [ttt F0].
                 assert (F1: In (c1, c'') (domain g1)). 
                 eapply split_domain_l_2 with (x := (c1, c'')) in H1; move H1 at bottom.
                 eapply in_g_in_domain in F0; intuition.
                 eapply in_domain_in_g in F1.
                 destruct F1 as [f1 [tt1 F1]].
                 assert (FP: exists f3, flagOf g3 (c1, c'') f3 /\ flag_plus hid f3 f1).
                 eapply split_flag_plus with (pf1 := pf0) (pf2 := pf3) (pf := pf1)...
                 destruct FP as [f3' [F3 FP]].
                 assert (ff = f3').
                 eapply flag_of_map with (g := g3) (x := (c1, c''))...
                 subst ff.
                 assert (F1': flagOf g1 (c1, c'')  hid).
                 eapply fsub_hid...
                 inversion F1'. subst g4 n3 f0.
                 assert (f1 = hid).
                 eapply flag_of_map with (g := g1) (x := (c1, c''))...
                 subst f1.
                 inversion FP...

                 subst.
                 eapply typeCheck_ill with (p := p3)...

                 subst ne3;
                   rewrite identif_seclabs_of_dep_relabel in *;
                   eapply Peirce; intros ABS;
                   eapply not_disjoint in ABS as ([x1 x2] &ABS1 &ABS2);
                   eapply in_bv_lt_max with (pf := pf3) in ABS1;
                   eapply in_domain_in_g in ABS2 as (ff &tt &ABS2);
                   eapply newEntries_gte_max in ABS2;
                   try lia;
                   try eassumption.

                 all:eauto.
                 
               ****
                 apply type_plus_comm...
               ****
                 apply type_plus_comm...

           **
             (* m0 = un *)
             
             eapply tsub_un with (pf := pf1) in TYPb as TYP1b.
             inversion TYP1b. subst g4 n3 t0.
             assert (IN1:= H). clear H.
             assert (q3 = p).
             eapply split_plus_un with (pf1 := pf0) (pf2 := pf3) (pf3 := pf1) (b1 := b1) (b2 := b2) (f1 := f) (p1 := p)
                                       (t := tb)...
             subst q3.
             
             destruct f.
             ***
               (* f = hid *)
               contradiction.
             ***
               (* f = ill *)
               assert (f3 = ill).
               (* by showing that  f3 = hid ->
                   tEnv_split g0 g3 g1 pf0 pf3 pf1 ->
flagOf b g1 hid and
tEnv_split g1 g2 g pf1 pf2 pf ->
flagOf b g1 hid ->
flagOf b g hid.
finally
lts g p1 (aIn a1 a2 b1 b2) g' p2 nd_pf ->contradiction by apply lts_inp_obj_not_hid*)
               destruct f3.
               clear IHLTS.
               eapply lts_inp_obj_not_hid in LTS0;
                 eapply lts_inp_obj_not_hid in LTS.
               eapply fsub_hid with (pf := pf1)  in TYP3b.
               inversion TYP3b; subst.
               eapply fsub_hid with (pf := pf)  in H.
               contradiction.
               eauto. eapply split_comm...
               tauto.
               eapply fsub_vis with (pf := pf1)  in TYP3b.
               inversion TYP3b; subst.
               eapply fsuper_vis with (pf1 := pf0) in H.
               destruct H as [H _].
               assert (ill = vis).
               eapply flag_of_map with (g := g0)...
               discriminate.
               eauto.
               eapply split_comm...

               subst f3.
               
              
               
               
               assert (TC3 := H3).
               eapply IHLTS in IH1. clear IHLTS.
               
               all:eauto.

               assert (TC2 := H2).
               

               eapply lts_inp with
                   (ta :=  (Chan m q t))
                   (tb := (Chan un p tb))
                   (m := m)
                   (q := q)
                   (t := t)
                   (r := r)
                 in LTS0 as G0.
               

               inversion  TYPa. subst g4 n3 t0.
               apply tsub_payload with
                   g0 g3 g1 pf0 pf3 pf1 a1 a2 f m q t in H as K. 
               destruct K as [q1 TYP1a].
               
               
               assert (lts_input_exists_plus:
                         exists r',
                           type_plus t (Chan un p tb) r').
               assert (AFT: exists (f : flag) (m : mode) (q : pol) (t r tb : piType),
    typeOf g1 (a1, a2) (Chan m q t) /\ In (b1, b2, f, tb) g1 /\ f <> hid /\ type_plus t tb r).
               eapply lts_after_inp...
               destruct AFT as
                   [ff [mm [qq [tt [rr [ttb [TYPP [INN [_ TPP]]]]]]]]].
               assert (Chan un p tb = ttb).
               eapply type_of_map with (g := g1) (x := (b1, b2))...
               assert (t = tt).
               assert (Chan m q1 t = Chan mm qq tt).
                eapply type_of_map with (g := g1) (x := (a1, a2))...
                inversion H4; subst; intuition.
                inversion H4; subst.
                exists rr...
                
                
               destruct lts_input_exists_plus as [r' TP2].
               assert (LTS1:  lts g1 p1 (aIn a1 a2 b1 b2) k1 p2 nd_pf1). 
               inversion LTSPAR...
               apply lts_inp with
                   (ta :=  Chan m q1 t)
                   (tb := (Chan un p tb))
                   (m := m)
                   (q := q1)
                   (t := t)
                   (r := r')
                 in LTS1 as G1.
               
               assert (TP0 := TP).
               inversion TP. subst t0.
               assert (TP20 := TP2).
               inversion TP2.
               all: eauto.

              
               
               destruct m.
               ****
                 (*remember ((((b1, b2), vis, Chan lin empty tb)
                              :: removeEntry (b1, b2) g3))
                   as g3'.*)
                 
               assert (nd_pf3' :
                         NoDup (domain 
                           ((a1, a2, vis, Chan lin empty t) :: ((b1, b2), vis, Chan un (pol_cup p0 p) tb)
                                                            ::                                              removeEntry (a1, a2) (removeEntry (b1, b2) g3)))).
               eapply no_dup_cons_removeEntry_app... 
               eapply no_dup_isMap in nd_pf3' as pf3'.
                 
                 apply TPar with
                      (pf1 := pfk0) (pf2 := pf3').

                 (* HYP *)
                 (* g1>p1 -a-> k1>p2 *)
                 (* g0>p1 -a-> k0>p2 *)
                 (* g0 + g3 = g1 *)
                 (* g3(b)= (ill, Chan lin q3 t) *)
                 (* g3' = g3 \b, (vis, Chan lin empty t) *)
                 (* GOAL *)
                 (* k0 + g3' = k1 *) 

                 subst.
                 assert (p5 = p0).
                 inversion H6...
                 subst p5.
                 
                 destruct G0 as [G0 ABS].
                 assert (K0 : lin=lin). tauto.
                 apply G0 in K0 as W0.
                 apply G1 in K0 as W1.
                 revert dependent pfk0; rewrite W0.
                 revert dependent pfk1; rewrite W1.
                 intros. subst.
                 
                 (* HYP:  tEnv_split g0 g3 g1 pf0 pf3 pf1 *)
                 (* GOAL:  tEnv_split
    ((a1, a2, vis, Chan lin empty (Chan lin empty tb))
     :: (b1, b2, vis, Chan lin p7 tb) :: removeEntry (a1, a2) (removeEntry (b1, b2) g0))
    ((b1, b2, vis, Chan lin empty tb) :: removeEntry (b1, b2) g3)
    ((a1, a2, vis, Chan lin empty (Chan lin empty tb))
     :: (b1, b2, vis, Chan lin p7 tb) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1))
    pfk0 pf3' pfk1 *)
                 remember p as pp. subst p.
                 remember p0 as p. subst p0.
                 remember pp as p0. subst pp.
                 remember (pol_cup p p0) as pp0.
                 remember tb as t2. subst tb.
                 assert
                   (nd_pff0: NoDup (domain
                             (removeEntry (n, n0)
                                          ((n, n0, vis, Chan lin empty (Chan un p t2))
                                             :: (n1, n2, vis, Chan un pp0 t2) :: removeEntry (n, n0) (removeEntry (n1, n2) g0))))).
                   unfold removeEntry. fold removeEntry.
                 assert (EQ2:  pair_eq (n, n0) (n, n0) = true). eauto.  rewrite EQ2.
                 erewrite removeEntry_swap.
                 eapply no_dup_cons_removeEntry, no_dup_removeEntry_no_dup...
                 eauto.
                 assert (nd_pff3: NoDup (domain
                             (removeEntry (n, n0)
                                          ((n, n0, vis, Chan lin empty (Chan un p t2))
                                             :: (n1, n2, vis, Chan un pp0 t2) :: removeEntry (n, n0) (removeEntry (n1, n2) g3))))).
                  unfold removeEntry. fold removeEntry.
                 assert (EQ2:  pair_eq (n, n0) (n, n0) = true). eauto.  rewrite EQ2.
                 erewrite removeEntry_swap.
                 eapply no_dup_cons_removeEntry, no_dup_removeEntry_no_dup...
                 eauto.
                 assert (nd_pff1:
                           NoDup (domain (
                (removeEntry (n, n0)
                                          ((n, n0, vis, Chan lin empty (Chan un p t2))
                                             :: (n1, n2, vis, Chan un pp0 t2) :: removeEntry (n, n0) (removeEntry (n1, n2) g1)))))).
                   unfold removeEntry. fold removeEntry.
                 assert (EQ2:  pair_eq (n, n0) (n, n0) = true). eauto.  rewrite EQ2.
                 erewrite removeEntry_swap.
                 eapply no_dup_cons_removeEntry, no_dup_removeEntry_no_dup...
                 eauto.
                 apply no_dup_isMap in nd_pff3 as pff3; eapply  no_dup_isMap in nd_pff0 as pff0;eapply  no_dup_isMap in nd_pff1 as pff1.
                
                 
                 eapply SpLin with (n := (n, n0)) (f := vis) (p := empty) (pf' := pff0) (pf'' := pff3) (pf''' := pff1).
                 eauto. eauto. eauto. eauto.
                 (*tEnv_split
    (removeEntry (n, n0)
       ((n, n0, vis, Chan lin empty (Chan lin p t2))
        :: (n1, n2, vis, Chan lin p t2) :: removeEntry (n, n0) (removeEntry (n1, n2) g0)))
    (removeEntry (n, n0) ((n1, n2, vis, Chan lin empty t2) :: removeEntry (n1, n2) g3))
    ?g''' ?pf' ?pf'' ?pf'''*)

                  assert (EQ2:  pair_eq (n, n0) (n, n0) = true).
                  eauto.
                  assert (EQ3: pair_eq (n1, n2) (n, n0) = false).
                  eapply pairEq_neq. intuition.
                 revert dependent pff0.
                 revert dependent pff3.
                 revert dependent pff1.
                 unfold removeEntry. fold removeEntry.
                 rewrite EQ2,removeEntry_swap.
                 assert (EQ4:
                          (n1, n2, vis, Chan un pp0 t2)
               :: removeEntry (n, n0) (removeEntry (n1, n2) g3) =((n1, n2, vis, Chan un pp0 t2)
               :: removeEntry (n1, n2) (removeEntry (n, n0) g3))).
                 erewrite removeEntry_swap.
                 tauto.
                 eauto. 
                 assert (EQ5:
                          (n1, n2, vis, Chan un pp0 t2)
               :: removeEntry (n, n0) (removeEntry (n1, n2) g0) =((n1, n2, vis, Chan un pp0 t2)
               :: removeEntry (n1, n2) (removeEntry (n, n0) g0))).
                 erewrite removeEntry_swap.
                 tauto.
                 eauto.
                 rewrite EQ4,EQ5.
                 intros.
                 eapply tEnv_split_add_vis.
                 eapply no_dup_removeEntry_no_dup...
                 rewrite <-pol_cup_id at 3.
                 econstructor...
                 intros _.
                 intuition.
                 eapply split_remove...
                 eauto.
                 subst... 
                 eauto.
                 eauto.
                 eauto.
                 (* typeCheck
    ((a1, a2, vis, Chan lin empty t)
     :: (b1, b2, vis, Chan un (pol_cup p0 p) tb)
        :: removeEntry (a1, a2) (removeEntry (b1, b2) g3)) pf3' p3*)

                  assert (nd_pf3w'' :
                           NoDup (domain
                                   ((b1, b2, vis, Chan un p tb)
     :: removeEntry (b1, b2) ((a1, a2, vis, Chan lin empty t)
                                :: removeEntry (a1, a2) g3)))).
                  
                 erewrite <-removeEntry_shift at 1. eapply no_dup_cons_removeEntry_app... intuition.
                 eapply no_dup_isMap in nd_pf3w'' as pf3w''.
                 assert (TCW:  typeCheck
    ((b1, b2, vis, Chan un p tb)
     :: removeEntry (b1, b2) ((a1, a2, vis, Chan lin empty t)
     :: removeEntry (a1, a2) g3)) pf3w'' p3).
                 eapply typeCheck_ill_vis.
                 eapply no_dup_cons_removeEntry...
                 eapply typeCheck_impl with (pf1 := pf3).
                 eauto.
                 eapply no_dup_cons_removeEntry...
                 eauto.

                 (*forall x : name * name * flag * piType,
  In x g3 <-> In x ((a1, a2, vis, Chan lin empty t) :: removeEntry (a1, a2) g3)*)
                 assert (INa: In (a1, a2, vis,  Chan lin inp t) g0 /\
                            In (a1, a2, vis, Chan lin empty t ) g3 /\ In (a1, a2, vis, Chan lin inp t ) g1).
                 eapply lts_middle...
                 destruct INa as [IN0a [IN3a IN1a]].
                 assert (Chan lin q t = Chan lin inp t).
                 eapply type_of_map with (g := g0)...
                 inversion H10; subst q.
                 split; intros IN; destruct x as [[[x1 x2] fx] ft]. case_eq (pair_eq (x1, x2) (a1, a2)).
                 intros PEQ; rewrite <-pairEq_eq in PEQ; inversion PEQ; subst. left.
                 assert (vis = fx /\ Chan lin empty (Chan un p0 tb) = ft). eapply in_isMap... intuition; subst; intuition.
                 intros PNEQ. rewrite <-pairEq_neq in PNEQ.
                 right. eapply removeEntry_in...
                 inversion IN. inversion H11; subst...
                 eapply in_removeEntry...

                 (*In (b1, b2, ill, Chan un p0 tb)
    ((a1, a2, vis, Chan lin empty t) :: removeEntry (a1, a2) g3)*)
                 right. eapply removeEntry_in.
                 intuition.
                 eauto.

                 assert (nd_pf3w''': NoDup (domain
                                  (((b1, b2, vis, Chan un (pol_cup p p0) tb)
           :: removeEntry (b1, b2)
                ((b1, b2, vis, Chan un p tb)
                 :: removeEntry (b1, b2)
                 ((a1, a2, vis, Chan lin empty t) :: removeEntry (a1, a2) g3)))))).
                 unfold removeEntry. fold removeEntry.
                 rewrite pairEq_eq_true.
                 eapply pairEq_neq in DIFF as PNEQ.
                 rewrite PNEQ.
                  eapply no_dup_cons_removeEntry_app...
                  eapply no_dup_isMap in nd_pf3w''' as
                      pf3w'''.
                  eapply typeCheck_weak_is_un with  (pf2 := pf3w''') in TCW. move TCW at bottom.
                 eapply typeCheck_impl with (pf1 := pf3w''').
                 eauto.
                 eauto.
                 eauto.
                 unfold removeEntry at 1. fold removeEntry.
                 rewrite  pairEq_eq_true, removeEntry_swap.
                 rewrite <-removeEntry_shift.
                 rewrite pol_cup_comm.
                 eapply  cons_cons_iff.
                 intuition. intuition.
                 rewrite <-removeEntry_shift. eapply no_dup_cons_removeEntry_app...
                 intuition.
                 eauto.
                 
               ****
                 (* m = un *)
                    
                 destruct G1 as [_ G1].
                 destruct G0 as [_ G0].

                 assert (SL : sl_pos p1)...

                 assert (ND_SL1: NoDup (secLabs p1)).
                 assert (TYP2 := TYP).
                 eapply typeCheck_no_dup in TYP as [_ ND_SL]; try simpl in ND_SL; try eapply no_dup_distr in ND_SL;
                   intuition.

                 assert (MAX0:
                          max (secLabs p1) <= max (domain g0)).
                 assert (TYP2 := TYP).
                 eapply typeCheck_no_dup in TYP as [INCL_SL _]; try simpl in INCL_SL.
                 erewrite split_max;
                   try eapply incl_preserves_max,incl_distr...
                 tauto.

                 
                 assert (K0EQ: exists ne : list (name * name * flag * piType),
                            k0 = ne ++ (b1, b2, vis, r) :: removeEntry (b1, b2) g0)...

                 erewrite split_max with (g := g1) in MAX0...
                 assert (K1EQ: exists ne : list (name * name * flag * piType),
            k1 = ne ++ (b1, b2, vis, r') :: removeEntry (b1, b2) g1)...
                 
                 destruct K0EQ as [ne0 K0EQ].
                 destruct K1EQ as [ne1 K1EQ].

                 
 assert (DISJ_ne0:
                          disjoint (domain ne0)
                            (domain ((b1, b2, vis, r) :: removeEntry (b1, b2) g0))).
                 subst k0; repeat rewrite domain_distr,no_dup_iff in nd_pfk0; intuition.

                

                 assert (DISJ_ne1:
                          disjoint (domain ne1)
                            (domain ((b1, b2, vis, r') :: removeEntry (b1, b2) g1))).
                 
                 
                 subst k1; repeat rewrite domain_distr,no_dup_iff in nd_pfk1; intuition.

                 
                 move LTS1 at bottom. move LTS0 at bottom.
                 assert (NE:
                            ne0 = nil \/
       exists q,
         replication p1 p2 q /\
         incl (secLabs q) (secLabs p1) /\
         ne0 = newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0))).
                 eapply lts_un_input_action_newEntries...
                 destruct NE.
                 
                 (* NON REPLICATED INPUT *)
                 *****
                   assert (NE1NIL: ne1 <> nil -> False).
                 intros ABS.
                 eapply lts_un_input_action_newEntries
                   with (k := ne1) (pf := nd_pf1) in LTS1 as ABS1.
                 destruct ABS1 as [ABS1 | ABS1]. contradiction.
                 destruct ABS1 as [rp [RP [INrp EQN]]].
                 eapply lts_un_input_action_newEntries_2  with (k := ne0) (q := rp) (pf := nd_pf0) in LTS0 as ABS0.
                 assert (newEntries g1 (secLabs (dep_relabel rp (domain g1) nd_pf1)) (max (domain g1)) = nil).
                 eapply newEntries_nil with (g := g0).
                 eauto.
                 intros. 
                 eapply split_domain_l...
                 assert (MAX: max (domain g0) = max (domain g1)).
                 eapply split_max...
                 erewrite <-MAX, max_dep_relabel with (nd_pf1 := nd_pf0).
                 subst...
                 eauto.
                 subst; contradiction.
                 all:eauto.
                 apply NNPP in NE1NIL.
                 subst.

                 
                inversion H6; subst.
                 
                 assert (nd_pf3': NoDup (domain
                                           ((n1, n2, vis, Chan un (pol_cup p0 p) tb) :: removeEntry (n1, n2) g3))).
                 eapply no_dup_cons_removeEntry...
                 eapply no_dup_isMap in nd_pf3' as pf3'.
                 
                 eapply TPar with  (pf1 := pfk0) (pf2 := pf3').
                 eapply tEnv_split_add_vis.
                 eauto.
                 erewrite <-pol_cup_id at 3...
                 intros _.
                 intuition.
                 eauto.
                 eauto.

                 (*typeCheck ((n1, n2, vis, Chan un (pol_cup p0 p) tb) :: removeEntry (n1, n2) g3) pf3' p3)*)
                 assert (nd_pf3'': NoDup (domain( ((n1, n2, vis, Chan un p tb) :: removeEntry (n1, n2) g3)))).
                 eapply no_dup_cons_removeEntry...
                 eapply no_dup_isMap in nd_pf3'' as pf3''.
                 eapply typeCheck_ill_vis with (pf1 := pf3'') in TC3.
                 assert (nd_pf3''': NoDup (domain( ((n1, n2, vis, Chan un (pol_cup p p0) tb) :: removeEntry (n1, n2) ((n1, n2, vis, Chan un p tb) :: removeEntry (n1, n2) g3))))).
                 eapply no_dup_cons_removeEntry...  
                 eapply no_dup_isMap in nd_pf3''' as pf3'''.
                 eapply typeCheck_weak_is_un with (pf2 := pf3''') in TC3.
                 move TC3 at bottom.
                 revert dependent pf3'''.
                 unfold removeEntry. erewrite pairEq_eq_true,pol_cup_comm. fold removeEntry. intros.
                 eapply typeCheck_rewrite_pf... 
                 eauto.
                 eauto.
                 eauto.
                 eauto.
                  (* REPLICATED INPUT *)
                 *****
                   assert (p5 = p0). subst. inversion H6...
                 subst p5.
                   assert (H11 := H10). assert (H12 := H11).
                   destruct H12 as
                     [rp [RP [INRP EQN0]]].
                 eapply lts_un_input_action_newEntries_2  with (k := ne1) (q := rp) (pf := nd_pf1) in LTS1 as EQN1.

                 
                 assert  (nd_pfne0:
                           NoDup (domain ne0)).
                 subst. erewrite domain_distr in nd_pfk0; eapply no_dup_distr in nd_pfk0. intuition.

                 assert (nd_pfne1:
                           NoDup (domain ne1)).
                 subst. erewrite domain_distr in nd_pfk1; eapply no_dup_distr in nd_pfk1. intuition.
                 
                 remember
                   (newEntries g3 (secLabs (dep_relabel rp (domain g3) nd_pf3)) (max (domain g3))) as ne3.

                 assert (nd_pfne3:
                           NoDup (domain ne3)).
                 subst ne3; eapply newEntries_no_dup.
                 eapply wf_rewrite,prop27,incl_incl2.
                 eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
                 eauto.
                 eapply incl_tran with (m := secLabs p1)...
                 assert(  incl (secLabs p1) (domain g0)).
                 eapply typeCheck_no_dup with (pf := pf0)...
                 eapply incl_iff with (m1 := domain g0);
                   try eassumption.
                 intros; eapply split_domain_m...
                 eauto.
                 
                 assert (nd_pfk3:
                           NoDup
                             (domain
                                (ne3 ++
                                     ((b1, b2, vis, Chan un (pol_cup p0 p) tb)
                                        :: removeEntry (b1, b2) g3)))).
                 erewrite domain_distr, no_dup_iff.
                 split. assumption.
                 split. eapply no_dup_cons_removeEntry...
                 erewrite disjoint_commute. subst ne3.
                 assert (DIS: disjoint (domain g3)
    (domain
       (newEntries g3 (secLabs (dep_relabel rp (domain g3) nd_pf3))
          (max (domain g3))))).
                 eapply new_entries_disjoint.
                 unfold sl_pos, pos in *; intros.
                 specialize SLP with x1 x2;
                   unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INRP; specialize INRP with (x1,x2); intuition.
                 assert (MAX: max(domain g1) >= max (secLabs rp)).
                 eapply incl_preserves_max, incl_tran with (m := secLabs p1)... assert(  incl (secLabs p1) (domain g0)).
                 eapply typeCheck_no_dup with (pf := pf0)...
                 eapply incl_iff with (m1 := domain g0)...
                erewrite split_max with (pf := pf1). lia.
                eapply split_comm...
                eapply disjoint_iff with (l1  := domain g3), in_removeEntry_cons_iff,in_g_in_domain...
                

                 eapply no_dup_isMap in nd_pfk3 as pfk3.
                 eapply no_dup_isMap in nd_pfne0 as pfne0.
                 eapply no_dup_isMap in nd_pfne3 as pfne3.
                 eapply no_dup_isMap in nd_pfne1 as pfne1.
                 
                 eapply TPar with
                     (pf1 := pfk0) (pf2 := pfk3) (pf := pfk1).


                 (* tEnv_split k0 (ne3 ++ (b1, b2, vis, Chan lin empty tb) :: removeEntry (b1, b2) g3) k1 pfk0 pfk3
    pfk1*)
                 
               
                 subst k0 k1. eapply split_distr with
                     (pf1 := pfne0) (pf2 := pfne3) (pf := pfne1).
                 subst.
                 eapply split_newEntries...
                 eapply tEnv_split_add_vis.
                 eauto.
                 subst.
                 erewrite <-pol_cup_id at 3...
                 intros _; intuition.
                 eauto.
                 eauto.

                 (* typeCheck (ne3 ++ (b1, b2, vis, Chan un (pol_cup p0 p) tb) :: removeEntry (b1, b2) g3) pfk3
    p3*)
                 assert (nd_pf3' : NoDup(domain ((b1, b2, vis, Chan un p tb) :: removeEntry (b1, b2) g3))).
                 eapply no_dup_cons_removeEntry...
                 eapply no_dup_isMap in nd_pf3' as pf3'.
                 eapply typeCheck_ill_vis with (pf1 := pf3') in TC3.
                 move TC3 at bottom.
                 assert (nd_pf3'' :
                           NoDup(domain
                                   ((b1, b2, vis, Chan un (pol_cup p p0) tb) :: removeEntry (b1, b2) ((b1, b2, vis, Chan un p tb) :: removeEntry (b1, b2) g3)))).
                 eapply no_dup_cons_removeEntry...
                 eapply no_dup_isMap in nd_pf3'' as pf3''.
                 eapply typeCheck_weak_is_un with (pf2 := pf3'') in TC3 as TC3'.
                 revert dependent pf3''.
                 unfold removeEntry.
                 rewrite pairEq_eq_true, pol_cup_comm.
                 fold removeEntry. intros.

                 
                 eapply typeCheck_weak2 with (pfk := pfne3).
                 erewrite <-domain_distr...
                 eauto.

                 (* cons ne3 ?pfk *)
                 assert (INVNE: forall c1 c2 ff tt,
                            In (c1, c2, ff, tt) ne3 ->
                            In (c1, c2 - max (domain g3)) (secLabs rp) /\ In (c1, c2 - max (domain g3), ff, tt) g3).
                 intros.
                 eapply inverse_newEntries.
                 eauto.
                 (* sl_pos rp *)
                 eapply sl_pos_par_l in SLP;
                   unfold sl_pos in SLP;
                   unfold sl_pos.
                 eapply incl_pos with (l2 :=(secLabs p1))...
                 (* incl (secLabs rp) (domain g3) *)
                 eapply incl_tran with (m := secLabs p1).
                 assumption.
                 eapply incl_iff with (m1 := domain g0).
                 eapply typeCheck_no_dup with (pf := pf0)...
                 intros. eapply split_domain_m...
                 (*In (c1, c2, ff, tt)
    (newEntries g3
       (map (fun x : name * name => (fst x, snd x + max (domain g3))) (secLabs rp))
       (max (domain g3)))*)
                 subst. erewrite <-identif_seclabs_of_dep_relabel...
                
                 eapply cons_char.
                 destruct ne3. left...
                 right. intros.
                 specialize INVNE with c1 c2 ff tt.
                 apply INVNE in H12; clear INVNE.
                 destruct H12 as [INSL IN3].
                 remember (c2 - max (domain g3)) as c''.
                 assert (ff = ill). assert (IN' := IN1). clear IN1.
                 assert (IN1: In (c1, c'') (secLabs p1)).
                 eapply INRP...
                 assert (NOTINSL: ~In (c1, c'') (secLabs p3)).
                 intros ABS.
                 assert (ND: NoDup (secLabs (dPar p1 p3))).
                 eapply typeCheck_no_dup with (pf := pf1)...
                 unfold secLabs in ND. fold secLabs in ND.
                 erewrite no_dup_iff in ND; destruct ND as [ND1 [ND2 DIS]].
                  eapply disjoint_absurd...
                 assert (NOTINFN: ~ In (c1, c'') (fn p3)).
                 intros ABS.
                 assert (DIS: disjoint (fn (dPar p1 p3)) (secLabs (dPar p1 p3))).
                 eapply fn_disjoint_sl with (pf := pf1)...
                 unfold fn, secLabs in DIS;
                   fold fn in DIS; fold secLabs  in DIS.
                 eapply disjoint_absurd with (x:= (c1, c'')) (l := (fn p1 ++ fn p3)) (m := (secLabs p3 ++ secLabs p1)).
                 eauto. eapply in_app_iff; right...
                 eapply in_app_iff; right...
                 assert (IN0: exists tt, In (c1, c'', hid, tt) g0).
                 eapply typeCheck_hid...
                 destruct IN0 as [ttt F0].
                 assert (F1: In (c1, c'') (domain g1)). 
                 eapply split_domain_l_2 with (x := (c1, c'')) in H1; move H1 at bottom.
                 eapply in_g_in_domain in F0; intuition.
                 eapply in_domain_in_g in F1.
                 destruct F1 as [f1 [tt1 F1]].
                 assert (FP: exists f3, flagOf g3 (c1, c'') f3 /\ flag_plus hid f3 f1).
                 eapply split_flag_plus with (pf1 := pf0) (pf2 := pf3) (pf := pf1)...
                 destruct FP as [f3' [F3 FP]].
                 assert (ff = f3').
                 eapply flag_of_map with (g := g3) (x := (c1, c''))...
                 subst ff.
                 assert (F1': flagOf g1 (c1, c'')  hid).
                 eapply fsub_hid...
                 inversion F1'. subst g4 n3 f2.
                 assert (f1 = hid).
                 eapply flag_of_map with (g := g1) (x := (c1, c''))...
                 subst f1.
                 inversion FP...

                 subst.
                 eapply typeCheck_ill with (pf := pf3)...

                 subst ne3;
                   rewrite identif_seclabs_of_dep_relabel in *;
                   eapply Peirce; intros ABS;
                   eapply not_disjoint in ABS as ([x1 x2] &ABS1 &ABS2);
                   eapply in_bv_lt_max with (pf := pf3) in ABS1;
                   eapply in_domain_in_g in ABS2 as (ff &tt &ABS2);
                   eapply newEntries_gte_max in ABS2;
                   try lia;
                   try eassumption.

                 all:eauto.
                 
               ****
                 apply type_plus_comm...
               ****
                 apply type_plus_comm...
             *** 
               (* f = vis *)
               assert (f3 = vis).
               assert (FVIS: flagOf g3 (b1, b2) vis /\ flagOf g1 (b1, b2) vis).
               eapply flag_of_split_l...
               destruct FVIS as [F3 _].
               inversion F3; subst.
               eapply flag_of_map with (g:=g3)...
               
               subst f3.
               assert (TC3 := H3).
               specialize typeCheck_vis with
                   (b1, b2) (Chan un p tb) g3 pf3 p3 as TYPVIS.
               apply TYPVIS in H3 as EX. move EX at bottom.
               
               specialize IHLTS with
                   (k1 := k0) (g1 := g0)
                   (g2 := w2) (pf1 := pf0) (pf2 := pfw2)
                   (pfk1 := pfk0) (pf := pf) (nd_pf1 := nd_pf0).
               apply IHLTS in IH1. clear IHLTS.
               
               all:eauto.

               assert (TC2 := H2).
               apply lts_inp with
                   (ta :=  (Chan m q t))
                   (tb := (Chan un p tb))
                   (m := m)
                   (q := q)
                   (t := t)
                   (r := r)
                 in LTS0 as G0.
               

               inversion  TYPa. subst g4 n3 t0.
               apply tsub_payload with
                   g0 g3 g1 pf0 pf3 pf1 a1 a2 f m q t in H as K. 
               destruct K as [q1 TYP1a].
               apply tsub_payload with
                   g0 g3 g1 pf0 pf3 pf1 b1 b2 vis un p tb in TYPb as K.
               assert (TYP1b' := TYP1b). clear TYP1b.
               destruct K as [q2 TYP1b].
               
                assert (lts_input_exists_plus:
                         exists r',
                           type_plus t (Chan un p tb) r').
               assert (AFT: exists (f : flag) (m : mode) (q : pol) (t r tb : piType),
    typeOf g1 (a1, a2) (Chan m q t) /\ In (b1, b2, f, tb) g1 /\ f <> hid /\ type_plus t tb r).
               eapply lts_after_inp...
               destruct AFT as
                   [ff [mm [qq [tt [rr [ttb [TYPP [INN [_ TPP]]]]]]]]].
               assert (Chan un p tb = ttb).
               eapply type_of_map with (g := g1) (x := (b1, b2))...
               assert (t = tt).
               assert (Chan m q1 t = Chan mm qq tt).
                eapply type_of_map with (g := g1) (x := (a1, a2))...
                inversion H4; subst... 
                exists rr; subst...
                
                
               destruct lts_input_exists_plus as [r' TP2].
               assert (LTS1:  lts g1 p1 (aIn a1 a2 b1 b2) k1 p2 nd_pf1). 
               inversion LTSPAR...
               apply lts_inp with
                   (ta :=  Chan m q1 t)
                   (tb := (Chan un p tb))
                   (m := m)
                   (q := q1)
                   (t := t)
                   (r := r')
                 in LTS1 as G1.
               
               assert (TP0 := TP).
               inversion TP. subst t0.
               assert (TP20 := TP2).
               inversion TP2.
               all: eauto.
               destruct m.
               ****
                 (*remember ((((b1, b2), vis, Chan lin empty tb)
                              :: removeEntry (b1, b2) g3))
                   as g3'.*)

                 assert (nd_pf3' :
                         NoDup (domain 
                           ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, Chan un (pol_cup p0 p) tb)
                              :: removeEntry (a1, a2)(removeEntry (b1, b2) g3)))).
               eapply no_dup_cons_removeEntry_app... 
               eapply no_dup_isMap in nd_pf3' as pf3'.
               move pf3' at top.
                 
                 apply TPar with
                     (pf1 := pfk0) (pf2 := pf3').

                 (* HYP *)
                 (* g1>p1 -a-> k1>p2 *)
                 (* g0>p1 -a-> k0>p2 *)
                 (* g0 + g3 = g1 *)
                 (* g3(b)= (ill, Chan lin q3 t) *)
                 (* g3' = g3 \b, (vis, Chan lin empty t) *)
                 (* GOAL *)
                 (* k0 + g3' = k1 *) 

                 
                 
                 
                 destruct G0 as [G0 ABS].
                 assert (K0 : lin=lin). tauto.
                 apply G0 in K0 as W0.
                 apply G1 in K0 as W1.
                 revert dependent pfk0; rewrite W0.
                 revert dependent pfk1; rewrite W1.
                 intros.
                 subst.
                 
                 assert (p5 = p0). subst. inversion H6...
                 subst p5.
                 remember p as pp. subst p.
                 remember p0 as p. subst p0.
                 remember tb as t2. subst tb.
                 remember pp as p0. subst pp.
                 remember (pol_cup p p0) as pp0.
                 (* HYP:  tEnv_split g0 g3 g1 pf0 pf3 pf1 *)
                 (* GOAL:  tEnv_split
    ((n, n0, vis, Chan lin empty (Chan un p0 tb))
     :: (n1, n2, vis, Chan un (pol_cup p0 p) tb)
        :: removeEntry (n, n0) (removeEntry (n1, n2) g0))
    ((n, n0, vis, Chan lin empty (Chan un p0 tb))
     :: (n1, n2, vis, Chan un (pol_cup p0 p) tb)
        :: removeEntry (n, n0) (removeEntry (n1, n2) g3))
    ((n, n0, vis, Chan lin empty (Chan un p0 tb))
     :: (n1, n2, vis, Chan un (pol_cup p0 p) tb)
        :: removeEntry (n, n0) (removeEntry (n1, n2) g1)) pfk0 pf3' pfk1*)
                 assert
                   (nd_pff0: NoDup (domain
                             (removeEntry (n, n0)
                                          ((n, n0, vis, Chan lin empty (Chan un p t2))
                                             :: (n1, n2, vis, Chan un pp0 t2) :: removeEntry (n, n0) (removeEntry (n1, n2) g0))))).
                   unfold removeEntry. fold removeEntry.
                 assert (EQ2:  pair_eq (n, n0) (n, n0) = true). eauto.  rewrite EQ2.
                 erewrite removeEntry_swap.
                 eapply no_dup_cons_removeEntry, no_dup_removeEntry_no_dup...
                 eauto.
                 assert
                   (nd_pff3: NoDup (domain
                             (removeEntry (n, n0)
                                          ((n, n0, vis, Chan lin empty (Chan un p t2))
                                             :: (n1, n2, vis, Chan un pp0 t2) :: removeEntry (n, n0) (removeEntry (n1, n2) g3))))).
                   unfold removeEntry. fold removeEntry.
                 assert (EQ2:  pair_eq (n, n0) (n, n0) = true). eauto.  rewrite EQ2.
                 erewrite removeEntry_swap.
                 eapply no_dup_cons_removeEntry, no_dup_removeEntry_no_dup...
                 eauto.
                 assert
                   (nd_pff1: NoDup (domain
                             (removeEntry (n, n0)
                                          ((n, n0, vis, Chan lin empty (Chan un p t2))
                                             :: (n1, n2, vis, Chan un pp0 t2) :: removeEntry (n, n0) (removeEntry (n1, n2) g1))))).
                   unfold removeEntry. fold removeEntry.
                 assert (EQ2:  pair_eq (n, n0) (n, n0) = true). eauto.  rewrite EQ2.
                 erewrite removeEntry_swap.
                 eapply no_dup_cons_removeEntry, no_dup_removeEntry_no_dup...
                 eauto.
                 apply no_dup_isMap in nd_pff3 as pff3; eapply  no_dup_isMap in nd_pff0 as pff0;eapply  no_dup_isMap in nd_pff1 as pff1.
                
                 
                 subst pp0. eapply SpLin with (f := vis) (pf' := pff0) (pf'' := pff3) (pf''' := pff1) (p := empty) (q := empty).
                 eauto. eauto. eauto. eauto. 

   
                 (*tEnv_split
    (removeEntry (n, n0)
       ((n, n0, vis, Chan lin empty (Chan un p t2))
        :: (n1, n2, vis, Chan un (pol_cup p p0) t2)
           :: removeEntry (n, n0) (removeEntry (n1, n2) g0)))
    (removeEntry (n, n0)
       ((n, n0, vis, Chan lin empty (Chan un p t2))
        :: (n1, n2, vis, Chan un (pol_cup p p0) t2)
           :: removeEntry (n, n0) (removeEntry (n1, n2) g3)))
    (removeEntry (n, n0)
       ((n, n0, vis, Chan lin empty (Chan un p t2))
        :: (n1, n2, vis, Chan un (pol_cup p p0) t2)
           :: removeEntry (n, n0) (removeEntry (n1, n2) g1))) pff0 pff3 pff1*)

                  (*assert (EQ2:  pair_eq (n, n0) (n, n0) = true).
                  eauto.
                  assert (EQ3: pair_eq (n1, n2) (n, n0) = false).
                  eapply pairEq_neq.  intuition.
                  assert (EQ4:
                          (n1, n2, vis, Chan lin q3 t2)
               :: removeEntry (n, n0) (removeEntry (n1, n2) g3) =((n1, n2, vis, Chan lin q3 t2)
               :: removeEntry (n1, n2) (removeEntry (n, n0) g3))).
                 erewrite removeEntry_swap.
                 tauto.
                 eauto.
                 assert (EQ5:
                          (n1, n2, vis, Chan lin empty t2)
               :: removeEntry (n, n0) (removeEntry (n1, n2) g0) =((n1, n2, vis, Chan lin p5 t2)
               :: removeEntry (n1, n2) (removeEntry (n, n0) g0))).
                 erewrite removeEntry_swap.
                 tauto.
                 eauto.*)
                 revert dependent pff0.
                 revert dependent pff3.
                 revert dependent pff1.
                 unfold removeEntry.
                 erewrite pairEq_eq_true.
                 fold removeEntry.
                 erewrite removeEntry_swap.
                 assert (EQ3: removeEntry (n, n0) (removeEntry (n1, n2) g3) = removeEntry (n1, n2) (removeEntry (n, n0) g3)). eapply removeEntry_swap...
                 assert (EQ0: removeEntry (n, n0) (removeEntry (n1, n2) g0) = removeEntry (n1, n2) (removeEntry (n, n0) g0)). eapply removeEntry_swap... rewrite EQ3,EQ0.
                 intros.
                 
                 eapply tEnv_split_add_vis.
                 eapply no_dup_removeEntry_no_dup...
                 inversion TYP1b. subst.
                 erewrite <-pol_cup_id at 3...
                 intuition.
                 
                 eapply split_remove...
                 intuition.
                 eauto.
                 eauto.
                 eauto.
                 eauto.

                 (* typeCheck
    ((a1, a2, vis, Chan lin empty t)
     :: (b1, b2, vis, Chan un (pol_cup p0 p) tb)
        :: removeEntry (a1, a2) (removeEntry (b1, b2) g3)) pf3' p3*)
                 assert (nd_pf'':
                           NoDup (domain(
                                      (b1, b2, vis, Chan un (pol_cup p p0) tb)::removeEntry (b1, b2) ((a1, a2, vis, Chan lin empty t) :: removeEntry (a1, a2) ( g3))))).
                 eapply no_dup_cons_removeEntry,no_dup_cons_removeEntry...
                 eapply no_dup_isMap in nd_pf'' as pf''.
                 eapply typeCheck_impl with (pf1 := pf'')...
                 eapply typeCheck_weak_is_un.
                 eapply no_dup_cons_removeEntry...
                 eapply typeCheck_impl with (pf1 := pf3).
                 eauto.
                 eapply no_dup_cons_removeEntry...
                 eauto.
                 eapply in_removeEntry_cons_iff_0.
                 eauto.
                 assert (EXT: In (a1, a2, vis, Chan lin inp t ) g0 /\
                 In (a1, a2, vis, Chan lin empty t ) g3 /\
                 In (a1, a2, vis, Chan lin inp t ) g1).
                 eapply lts_middle...
                 destruct EXT as [INN3 [INN0 INN1]].
                 assert (TEQ: Chan lin q t =Chan lin inp t). eapply type_of_map with (g := g0)...  
                 inversion TEQ; subst q...

                 right. eapply removeEntry_in.
                 intuition.
                 eauto.

                 erewrite <-removeEntry_shift.
                 assert (EQR: removeEntry (b1, b2) (removeEntry (a1, a2) g3) = removeEntry (a1, a2) (removeEntry (b1, b2) g3)). eapply removeEntry_swap.  intuition.
                 erewrite EQR, pol_cup_comm. eapply cons_cons_iff.
                 intuition.
               ****
                 (* m = un *)
                    
                 destruct G1 as [_ G1].
                 destruct G0 as [_ G0].

                 assert (SL : sl_pos p1)...

                 assert (ND_SL1: NoDup (secLabs p1)).
                 assert (TYP2 := TYP).
                 eapply typeCheck_no_dup in TYP as [_ ND_SL]; try simpl in ND_SL; try eapply no_dup_distr in ND_SL;
                   intuition.

                 assert (MAX0:
                          max (secLabs p1) <= max (domain g0)).
                 assert (TYP2 := TYP).
                 eapply typeCheck_no_dup in TYP as [INCL_SL _]; try simpl in INCL_SL.
                 erewrite split_max;
                   try eapply incl_preserves_max,incl_distr...
                 tauto.

                 
                 assert (K0EQ: exists ne : list (name * name * flag * piType),
                            k0 = ne ++ (b1, b2, vis, r) :: removeEntry (b1, b2) g0)...

                 erewrite split_max with (g := g1) in MAX0...
                 assert (K1EQ: exists ne : list (name * name * flag * piType),
            k1 = ne ++ (b1, b2, vis, r') :: removeEntry (b1, b2) g1)...
                 
                 destruct K0EQ as [ne0 K0EQ].
                 destruct K1EQ as [ne1 K1EQ].
                 assert (DISJ_ne0:
                          disjoint (domain ne0)
                            (domain ((b1, b2, vis, r) :: removeEntry (b1, b2) g0))).
                 subst k0; repeat rewrite domain_distr,no_dup_iff in nd_pfk0; intuition.

                

                 assert (DISJ_ne1:
                          disjoint (domain ne1)
                            (domain ((b1, b2, vis, r') :: removeEntry (b1, b2) g1))).
                 
                 
                 subst k1; repeat rewrite domain_distr,no_dup_iff in nd_pfk1; intuition.
                 
                 move LTS1 at bottom. move LTS0 at bottom.
                 assert (NE:
                            ne0 = nil \/
       exists q,
         replication p1 p2 q /\
         incl (secLabs q) (secLabs p1) /\
         ne0 = newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0))).
                 eapply lts_un_input_action_newEntries...
                 destruct NE.
                 
                 (* NON REPLICATED INPUT *)
                 *****
                    assert (NE1NIL: ne1 <> nil -> False).
                 intros ABS.
                 eapply lts_un_input_action_newEntries
                   with (k := ne1) (pf := nd_pf1) in LTS1 as ABS1.
                 destruct ABS1 as [ABS1 | ABS1]. contradiction.
                 destruct ABS1 as [rp [RP [INrp EQN]]].
                 eapply lts_un_input_action_newEntries_2  with (k := ne0) (q := rp) (pf := nd_pf0) in LTS0 as ABS0.
                 assert (newEntries g1 (secLabs (dep_relabel rp (domain g1) nd_pf1)) (max (domain g1)) = nil).
                 eapply newEntries_nil with (g := g0).
                 eauto.
                 intros. 
                 eapply split_domain_l...
                 assert (MAX: max (domain g0) = max (domain g1)).
                 eapply split_max...
                 erewrite <-MAX, max_dep_relabel with (nd_pf1 := nd_pf0).
                 subst...
                 eauto.
                 subst; contradiction.
                 all:eauto.
                 apply NNPP in NE1NIL.
                 subst.
                 
                 inversion H6. subst p5.

                 
                 
                 inversion TYP1b; subst.
                 assert (nd_pf3': NoDup (domain
                                           ((n1, n2, vis, Chan un (pol_cup p p0) tb) :: removeEntry (n1, n2) g3))).
                 eapply no_dup_cons_removeEntry...
                 eapply no_dup_isMap in nd_pf3' as pf3'.
                 
                 eapply TPar with  (pf1 := pfk0) (pf2 := pf3').
                 eapply tEnv_split_add_vis.
                 eauto.
                 assert (PC: (pol_cup p p0) = (pol_cup p0 p)).  eapply pol_cup_comm.
                 erewrite PC. erewrite <-pol_cup_id at 3...
                 erewrite pol_cup_comm. intuition.
                 
                 eauto.
                 eauto.
                 eapply typeCheck_weak_is_un.
                 eauto.
                 eauto.
                 eauto.
                  (* REPLICATED INPUT *)
                 *****
                   assert (p5 = p0). subst. inversion H6...
                 subst p5 p6 t0 p4 r r'.
                 
                   assert (H11 := H10). assert (H12 := H11).
                   destruct H12 as
                     [rp [RP [INRP EQN0]]].
                 eapply lts_un_input_action_newEntries_2  with (k := ne1) (q := rp) (pf := nd_pf1) in LTS1 as EQN1.

                 

                 assert  (nd_pfne0:
                           NoDup (domain ne0)).
                 subst. erewrite domain_distr in nd_pfk0; eapply no_dup_distr in nd_pfk0. intuition.

                 assert (nd_pfne1:
                           NoDup (domain ne1)).
                 subst. erewrite domain_distr in nd_pfk1; eapply no_dup_distr in nd_pfk1. intuition.
                 
                 
                 remember
                   (newEntries g3 (secLabs (dep_relabel rp (domain g3) nd_pf3)) (max (domain g3))) as ne3.

                 assert (nd_pfne3:
                           NoDup (domain ne3)).
                 subst ne3; eapply newEntries_no_dup.
                 eapply wf_rewrite,prop27,incl_incl2.
                 eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
                 eauto.
                 eapply incl_tran with (m := secLabs p1)...
                 assert(  incl (secLabs p1) (domain g0)).
                 eapply typeCheck_no_dup with (pf := pf0)...
                 eapply incl_iff with (m1 := domain g0);
                   try eassumption.
                 intros; eapply split_domain_m...
                 eauto.
                 
                 assert (nd_pfk3:
                           NoDup
                             (domain
                                (ne3 ++
                                     ((b1, b2, vis, Chan un (pol_cup p p0) tb)
                                        :: removeEntry (b1, b2) g3)))).
                 erewrite domain_distr, no_dup_iff.
                 split. assumption.
                 split. eapply no_dup_cons_removeEntry...
                 erewrite disjoint_commute. subst ne3.
                 assert (DIS: disjoint (domain g3)
    (domain
       (newEntries g3 (secLabs (dep_relabel rp (domain g3) nd_pf3))
          (max (domain g3))))).
                 eapply new_entries_disjoint.
                 unfold sl_pos, pos in *; intros.
                 specialize SLP with x1 x2;
                   unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INRP; specialize INRP with (x1,x2); intuition.
                 assert (MAX: max(domain g1) >= max (secLabs rp)).
                 eapply incl_preserves_max, incl_tran with (m := secLabs p1)... assert(  incl (secLabs p1) (domain g0)).
                 eapply typeCheck_no_dup with (pf := pf0)...
                 eapply incl_iff with (m1 := domain g0)...
                erewrite split_max with (pf := pf1). lia.
                eapply split_comm...
                eapply disjoint_iff with (l1  := domain g3), in_removeEntry_cons_iff,in_g_in_domain...

                 eapply no_dup_isMap in nd_pfk3 as pfk3.
                 eapply no_dup_isMap in nd_pfne0 as pfne0.
                 eapply no_dup_isMap in nd_pfne3 as pfne3.
                 eapply no_dup_isMap in nd_pfne1 as pfne1.
                 
                 eapply TPar with
                     (pf1 := pfk0) (pf2 := pfk3) (pf := pfk1).


                 (* tEnv_split k0 (ne3 ++ (b1, b2, vis, Chan un (pol_cup p p0) tb) :: removeEntry (b1, b2) g3)
    k1 pfk0 pfk3 pfk1*)
                 inversion TYP1b. subst.
                  
                 eapply split_distr with
                     (pf1 := pfne0) (pf2 := pfne3) (pf := pfne1).
                 eapply split_newEntries...
                 eapply tEnv_split_add_vis.
                 eauto.
                 assert (PC : pol_cup p p0 = pol_cup p0 p).
                 eapply pol_cup_comm...
                 erewrite PC. erewrite <-pol_cup_id at 3...
                 erewrite pol_cup_comm.
                 intuition.

                 
                 eauto.
                 eauto.
                 eapply typeCheck_weak2 with (pfk := pfne3).
                 erewrite <-domain_distr...
                 eapply typeCheck_weak_is_un...

                 (* cons ne3 ?pfk *)
                 assert (INVNE: forall c1 c2 ff tt,
                            In (c1, c2, ff, tt) ne3 ->
                            In (c1, c2 - max (domain g3)) (secLabs rp) /\ In (c1, c2 - max (domain g3), ff, tt) g3).
                 intros.
                 eapply inverse_newEntries.
                 eauto.
                 (* sl_pos rp *)
                 eapply sl_pos_par_l in SLP;
                   unfold sl_pos in SLP;
                   unfold sl_pos.
                 eapply incl_pos with (l2 :=(secLabs p1))...
                 (* incl (secLabs rp) (domain g3) *)
                 eapply incl_tran with (m := secLabs p1).
                 assumption.
                 eapply incl_iff with (m1 := domain g0).
                 eapply typeCheck_no_dup with (pf := pf0)...
                 intros. eapply split_domain_m...
                 (*In (c1, c2, ff, tt)
    (newEntries g3
       (map (fun x : name * name => (fst x, snd x + max (domain g3))) (secLabs rp))
       (max (domain g3)))*)
                 subst. erewrite <-identif_seclabs_of_dep_relabel...
                
                 eapply cons_char.
                 destruct ne3. left...
                 right. intros.
                 specialize INVNE with c1 c2 ff tt.
                 apply INVNE in H4; clear INVNE.
                 destruct H4 as [INSL IN3].
                 remember (c2 - max (domain g3)) as c''.
                 assert (ff = ill). assert (IN1' := IN1). clear IN1. 
                 assert (IN1: In (c1, c'') (secLabs p1)).
                 eapply INRP...
                 assert (NOTINSL: ~In (c1, c'') (secLabs p3)).
                 intros ABS.
                 assert (ND: NoDup (secLabs (dPar p1 p3))).
                 eapply typeCheck_no_dup with (pf := pf1)...
                 unfold secLabs in ND. fold secLabs in ND.
                 erewrite no_dup_iff in ND; destruct ND as [ND1 [ND2 DIS]].
                  eapply disjoint_absurd...
                 assert (NOTINFN: ~ In (c1, c'') (fn p3)).
                 intros ABS.
                 assert (DIS: disjoint (fn (dPar p1 p3)) (secLabs (dPar p1 p3))).
                 eapply fn_disjoint_sl with (pf := pf1)...
                 unfold fn, secLabs in DIS;
                   fold fn in DIS; fold secLabs  in DIS.
                 eapply disjoint_absurd with (x:= (c1, c'')) (l := (fn p1 ++ fn p3)) (m := (secLabs p3 ++ secLabs p1)).
                 eauto. eapply in_app_iff; right...
                 eapply in_app_iff; right...
                 assert (IN0: exists tt, In (c1, c'', hid, tt) g0).
                 eapply typeCheck_hid...
                 destruct IN0 as [ttt F0].
                 assert (F1: In (c1, c'') (domain g1)). 
                 eapply split_domain_l_2 with (x := (c1, c'')) in H1; move H1 at bottom.
                 eapply in_g_in_domain in F0; intuition.
                 eapply in_domain_in_g in F1.
                 destruct F1 as [f1 [tt1 F1]].
                 assert (FP: exists f3, flagOf g3 (c1, c'') f3 /\ flag_plus hid f3 f1).
                 eapply split_flag_plus with (pf1 := pf0) (pf2 := pf3) (pf := pf1)...
                 destruct FP as [f3' [F3 FP]].
                 assert (ff = f3').
                 eapply flag_of_map with (g := g3) (x := (c1, c''))...
                 subst ff.
                 assert (F1': flagOf g1 (c1, c'')  hid).
                 eapply fsub_hid...
                 inversion F1'. subst g4 n3 f2.
                 assert (f1 = hid).
                 eapply flag_of_map with (g := g1) (x := (c1, c''))...
                 subst f1.
                 inversion FP...

                 subst.
                 eapply typeCheck_ill with (p := p3)...

                 subst ne3;
                   rewrite identif_seclabs_of_dep_relabel in *;
                   eapply Peirce; intros ABS;
                   eapply not_disjoint in ABS as ([x1 x2] &ABS1 &ABS2);
                   eapply in_bv_lt_max with (pf := pf3) in ABS1;
                   eapply in_domain_in_g in ABS2 as (ff &tt &ABS2);
                   eapply newEntries_gte_max in ABS2;
                   try lia;
                   try eassumption.

                 all:eauto.
                 
               ****
                 apply type_plus_comm...
               ****
                 apply type_plus_comm...
             *** eauto.
         *  (* tb = Top *)
           inversion TP. subst t r.
           apply lts_inp with (m := m) (q := q) (t := Top) (r := Top) (ta := Chan m q Top) (tb := Top)in LTS0 as K0.
           eapply lts_inp_obj_not_hid in LTS as NHID1.
           inversion LTSPAR.
           subst p0 q0 a g'0 p4 pf4.
           assert (LTS1 := H8).
           inversion TYPa. subst g4 n3 t.
           assert (INN0a := H). clear H.
           eapply tsub_payload with (pf := pf1) in INN0a as TYP1a.
           destruct TYP1a as [pa TYP1a].
           apply lts_inp with (m := m) (q := pa) (t := Top) (r := Top) (tb := Top) (ta := Chan m pa Top) in LTS1 as K1.
           assert (TC' := H2). 
           assert (TC1 : typeCheck k0 pfk0 p2).
           eapply IHLTS.
           eapply sl_pos_par_l...
           eauto.
           eauto.
           eauto.
           assert (TC2 := H3). clear H2 H3 H8.
           
           destruct m.
            **
              assert (EQK0: k0 =
        (a1, a2, vis, Chan lin empty Top)
          :: (b1, b2, vis, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g0)). intuition.
              assert (EQK1:  k1 =
        (a1, a2, vis, Chan lin empty Top)
          :: (b1, b2, vis, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)). intuition.
              assert (nd_pfk3: NoDup(domain
                                       ( (a1, a2, vis, Chan lin empty Top)
                                           :: (b1, b2, vis, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g3)))).
              eapply no_dup_cons_removeEntry_app...
              eapply no_dup_isMap in nd_pfk3 as pfk3.
              eapply TPar with (pf1 := pfk0) (pf2 := pfk3).

              subst.
              revert dependent pfk0.
              erewrite removeEntry_shift.
              intros. 
              revert dependent pfk3.
               erewrite removeEntry_shift.
              intros.
               revert dependent pfk1.
              erewrite removeEntry_shift.
              intros.
              eapply tEnv_split_add_vis.
              eapply no_dup_cons_removeEntry...
              eauto.
              intros ABS. eapply not_lin_is_unrestricted in ABS; intuition.
              eapply tEnv_split_add_vis...
              all:intuition.
              (*typeCheck
    ((a1, a2, vis, Chan lin empty Top)
     :: (b1, b2, vis, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g3)) pfk3 p3*)
              assert (EXT: In (a1, a2, vis, Chan lin inp Top ) g0 /\
                 In (a1, a2, vis, Chan lin empty Top ) g3 /\
                 In (a1, a2, vis, Chan lin inp Top ) g1).
              eapply lts_middle...
              destruct EXT as [IN0a [IN3a IN1a]].
              assert (EQ: Chan lin q Top = Chan lin inp Top).
              eapply type_of_map with (g := g0)...
              inversion EQ; subst q.
              assert (nd_pfk3': NoDup (domain
                                         ((b1, b2, vis, Top) :: removeEntry (b1, b2) ((a1, a2, vis, Chan lin empty Top):: removeEntry (a1, a2) g3)))).
              erewrite <-removeEntry_shift. 
              eapply no_dup_cons_removeEntry_app...
              intuition.
              eapply no_dup_isMap in nd_pfk3' as pfk3'.
              eapply typeCheck_impl with (pf1 := pfk3').
              eauto.
              eauto.
              destruct f.
              (* f = hid *)
              contradiction.
              (* f = ill *)
              eapply flag_of_split_l with (n:= (b1, b2)) in TS2 as FLG.
              assert (F0: flagOf g0 (b1, b2) ill)...
              eapply FLG in F0 as [F0 | ABS].
              eapply typeCheck_ill_vis.
              eapply no_dup_cons_removeEntry...
              (* typeCheck ((a1, a2, vis, Chan lin empty Top) :: removeEntry (a1, a2) g3) ?pf8 p3*)
              eapply typeCheck_impl with (pf1 := pf3).
              eauto.
              eapply no_dup_cons_removeEntry...
              eauto.
              eapply in_removeEntry_cons_iff_0.
              eauto.
              eauto.
              right.
              eapply removeEntry_in.
              intuition.
              (*In (b1, b2, ill, Top) g3*)
              eapply tsub_top with (pf := pf1) in TYPb as TYP1b.
              inversion TYP1b. subst g4 n3 t. 
              eapply tsuper_top_r with (pf2 := pf3) in H2 as K2.
              inversion K2. subst g4 n3 t.
              assert (f1 = ill).
              eapply flag_of_map with (x := (b1, b2))(g := g3).
              eauto.
              eauto.
              intuition.
              subst...
              eauto.
              eauto.
              destruct ABS as [_ ABS1].
              eapply flag_of_split_l with (n:= (b1, b2)) in TS as FLG1.
              apply FLG1 in ABS1.
              clear FLG FLG1.
              intuition.
              (* f = vis *)
              assert (nd_pfk3'' : NoDup(domain(
                                          ((a1, a2, vis, Chan lin empty Top) :: removeEntry (a1, a2) g3)))).
              eapply no_dup_cons_removeEntry...
              eapply no_dup_isMap in nd_pfk3'' as pfk3''.
                eapply typeCheck_impl with (pf1 := pfk3'').
                eauto.
                eauto.
                eapply typeCheck_impl with (pf1 := pf3).
                eauto.
                eauto.
                eauto.
                eapply in_removeEntry_cons_iff_0.
                eauto.
                eauto.
                (* forall x : name * name * flag * piType,
  In x ((a1, a2, vis, Chan lin empty Top) :: removeEntry (a1, a2) g3) <->
  In x
    ((b1, b2, vis, Top)
     :: removeEntry (b1, b2) ((a1, a2, vis, Chan lin empty Top) :: removeEntry (a1, a2) g3))*)
                 eapply in_removeEntry_cons_iff_0.
                 eauto.
                 right.
                 eapply removeEntry_in.
                 intuition.
                (*  In (b1, b2, vis, Top) g3*)
                 eapply tsub_top with (pf := pf1) in TYPb as TYP1b.
              inversion TYP1b. subst g4 n3 t. 
              eapply tsuper_top_r with (pf2 := pf3) in H2 as K2.
              inversion K2. subst g4 n3 t.
              eapply flag_of_split_l with (n:= (b1, b2)) in TS2 as FLG.
              
              assert (F0: flagOf g0 (b1, b2) vis).
              eauto.
              eapply FLG in F0.
              assert (f1 = vis).
              eapply flag_of_map with (x := (b1, b2)) (g := g3).
              intuition. eauto. intuition.
              subst...
              all:eauto.
              erewrite <-removeEntry_shift,removeEntry_swap.
              eapply cons_cons_iff.
              all:intuition.
            **

              assert (SL : sl_pos p1)...

                 assert (ND_SL1: NoDup (secLabs p1)).
                 assert (TYP2 := TYP).
                 eapply typeCheck_no_dup in TYP as [_ ND_SL]; try simpl in ND_SL; try eapply no_dup_distr in ND_SL;
                   intuition.

                 assert (MAX0:
                          max (secLabs p1) <= max (domain g0)).
                 assert (TYP2 := TYP).
                 eapply typeCheck_no_dup in TYP as [INCL_SL _]; try simpl in INCL_SL.
                 erewrite split_max;
                   try eapply incl_preserves_max,incl_distr...
                 tauto.

                 
                assert (K0EQ:  exists ne : list (name * name * flag * piType),
                           k0 = ne ++ (b1, b2, vis, Top) :: removeEntry (b1, b2) g0). intuition.

                erewrite split_max with (g := g1) in MAX0...
                assert (K1EQ: exists ne : list (name * name * flag * piType),
                           k1 = ne ++ (b1, b2, vis, Top) :: removeEntry (b1, b2) g1). intuition.
                 destruct K0EQ as [ne0 K0EQ].
                 destruct K1EQ as [ne1 K1EQ].

                 assert (DISJ_ne0:
                          disjoint (domain ne0)
                            (domain ((b1, b2, vis, Top) :: removeEntry (b1, b2) g0))).
                 subst k0; repeat rewrite domain_distr,no_dup_iff in nd_pfk0; intuition.

                

                 assert (DISJ_ne1:
                          disjoint (domain ne1)
                            (domain ((b1, b2, vis, Top) :: removeEntry (b1, b2) g1))).
                 
                 
                  subst k1; repeat rewrite domain_distr,no_dup_iff in nd_pfk1; intuition.
                 
                 move LTS1 at bottom. move LTS0 at bottom.
                 assert (NE:
                            ne0 = nil \/
       exists q,
         replication p1 p2 q /\
         incl (secLabs q) (secLabs p1) /\
         ne0 = newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0))).
                 eapply lts_un_input_action_newEntries...
                 destruct NE.
                 
                 (* NON REPLICATED INPUT *)
                    assert (NE1NIL: ne1 <> nil -> False).
                 intros ABS.
                 eapply lts_un_input_action_newEntries
                   with (k := ne1) (pf := nd_pf1) (r := Top)(t := Top) (pol := q) in LTS1 as ABS1.
                 destruct ABS1 as [ABS1 | ABS1]. contradiction.
                 destruct ABS1 as [rp [RP [INrp EQN]]].
                 eapply lts_un_input_action_newEntries_2  with (k := ne0) (r := Top)  (q := rp) (pf := nd_pf0) in LTS0 as ABS0.
                 assert (newEntries g1 (secLabs (dep_relabel rp (domain g1) nd_pf1)) (max (domain g1)) = nil).
                 eapply newEntries_nil with (g := g0).
                 eauto.
                 intros. 
                 eapply split_domain_l...
                 assert (MAX: max (domain g0) = max (domain g1)).
                 eapply split_max...
                 erewrite <-MAX, max_dep_relabel with (nd_pf1 := nd_pf0).
                 subst...
                 eauto.
                 subst; contradiction.
                 eauto.
                 eauto.
                 eauto.
                 eauto.
                 eauto.
                 eauto.
                 inversion TYPa; eapply tsub_un with (pf1 := pf0)...
                 eauto.
                 eauto.
                 eauto.
                 apply NNPP in NE1NIL.
                 subst ne0 ne1.
                 
                 
                 assert (nd_pf3': NoDup (domain
                                           ((b1, b2, vis, Top) :: removeEntry (b1, b2) g3))).
                 eapply no_dup_cons_removeEntry...
                 eapply no_dup_isMap in nd_pf3' as pf3'.
                 
                 eapply TPar with  (pf1 := pfk0) (pf2 := pf3').
                 subst. eapply tEnv_split_add_vis.
                 eauto.
                 eauto.
                 intros ABS; intuition.
                 eauto.
                 eauto.
                 (* typeCheck ((b1, b2, vis, Top) :: removeEntry (b1, b2) g3) pf3' p3*)
                 destruct f.
                 (* f = hid *)
                 contradiction.
                 (* f = ill *)
                   eapply flag_of_split_l with (n:= (b1, b2)) in TS2 as FLG.
              assert (F0: flagOf g0 (b1, b2) ill)...
              eapply FLG in F0 as [F0 | ABS].
              eapply typeCheck_ill_vis.
              eauto.
              eauto.
                  (*  In (b1, b2, ill, Top) g3*)
                 eapply tsub_top with (pf := pf1) in TYPb as TYP1b.
              inversion TYP1b. subst g4 n3 t. 
              eapply tsuper_top_r with (pf2 := pf3) in H as K2.
              inversion K2. subst g4 n3 t.
              assert (f1 = ill).
              eapply flag_of_map with (g := g3) (x := (b1, b2)).
              eauto. eauto. intuition.
              subst...
              eauto.
              eauto.
               destruct ABS as [_ ABS1].
              eapply flag_of_split_l with (n:= (b1, b2)) in TS as FLG1.
              apply FLG1 in ABS1.
              clear FLG FLG1.
              intuition.
              (* f = vis *)
              eapply typeCheck_impl with (pf1 := pf3).
              eauto.
              eauto.
              eauto.
              eapply in_removeEntry_cons_iff_0.
              eauto.
              (*  In (b1, b2, vis, Top) g3*)
                 eapply tsub_top with (pf := pf1) in TYPb as TYP1b.
              inversion TYP1b. subst g4 n3 t. 
              eapply tsuper_top_r with (pf2 := pf3) in H as K2.
              inversion K2. subst g4 n3 t.
              eapply flag_of_split_l with (n:= (b1, b2)) in TS2 as FLG.
              
              assert (F0: flagOf g0 (b1, b2) vis).
              eauto.
              eapply FLG in F0.
              assert (f1 = vis).
              eapply flag_of_map with (x := (b1, b2)) (g := g3).
              intuition. eauto. intuition.
              subst...
              all:eauto.
              
                 (* REPLICATED INPUT *)
                 
              destruct H as
                  [rp [RP [INRP EQN0]]].
              eapply lts_un_input_action_newEntries_2  with (k := ne1) (q := rp) (r := Top) (pf := nd_pf1) in LTS1 as EQN1.

             

              assert  (nd_pfne0:
                         NoDup (domain ne0)).
              subst. erewrite domain_distr in nd_pfk0; eapply no_dup_distr in nd_pfk0. intuition.

              assert (nd_pfne1:
                        NoDup (domain ne1)).
              subst. erewrite domain_distr in nd_pfk1; eapply no_dup_distr in nd_pfk1. intuition.
              
              
              remember
                (newEntries g3 (secLabs (dep_relabel rp (domain g3) nd_pf3)) (max (domain g3))) as ne3.

              assert (nd_pfne3:
                        NoDup (domain ne3)).
              subst ne3; eapply newEntries_no_dup.
                 eapply wf_rewrite,prop27,incl_incl2.
                 eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
                 eauto.
                 eapply incl_tran with (m := secLabs p1)...
                 assert(  incl (secLabs p1) (domain g0)).
                 eapply typeCheck_no_dup with (pf := pf0)...
                 eapply incl_iff with (m1 := domain g0);
                   try eassumption.
                 intros; eapply split_domain_m...
                 eauto.
                 
                 assert (nd_pfk3:
                           NoDup
                             (domain
                                (ne3 ++
                                     ((b1, b2, vis, Top)
                                        :: removeEntry (b1, b2) g3)))).
                 erewrite domain_distr, no_dup_iff.
                 split. assumption.
                 split. eapply no_dup_cons_removeEntry...
                 erewrite disjoint_commute. subst ne3.
                 assert (DIS: disjoint (domain g3)
    (domain
       (newEntries g3 (secLabs (dep_relabel rp (domain g3) nd_pf3))
          (max (domain g3))))).
                 eapply new_entries_disjoint.
                 unfold sl_pos, pos in *; intros.
                 specialize SLP with x1 x2;
                   unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INRP; specialize INRP with (x1,x2); intuition.
                 assert (MAX: max(domain g1) >= max (secLabs rp)).
                 eapply incl_preserves_max, incl_tran with (m := secLabs p1)... assert(  incl (secLabs p1) (domain g0)).
                 eapply typeCheck_no_dup with (pf := pf0)...
                 eapply incl_iff with (m1 := domain g0);
                   try eassumption.
                 eauto.
                erewrite split_max with (pf := pf1). lia.
                eapply split_comm...
                eapply tsub_top with (pf := pf1) in TYPb as TYP1b.
                inversion TYP1b. subst g4 n3 t.
                eapply tsuper_top_r with (pf2 := pf3) in H.
                inversion H.
                eapply disjoint_iff with (l1  := domain g3), in_removeEntry_cons_iff,in_g_in_domain...
                eauto.
                eauto.
                
                 eapply no_dup_isMap in nd_pfk3 as pfk3.
                 eapply no_dup_isMap in nd_pfne0 as pfne0.
                 eapply no_dup_isMap in nd_pfne3 as pfne3.
                 eapply no_dup_isMap in nd_pfne1 as pfne1.
                 
                 eapply TPar with
                     (pf1 := pfk0) (pf2 := pfk3) (pf := pfk1).


                 (* tEnv_split k0 (ne3 ++ (b1, b2, vis, Top) :: removeEntry (b1, b2) g3)
    k1 pfk0 pfk3 pfk1*)
                  
                 subst k0 k1. eapply split_distr with
                     (pf1 := pfne0) (pf2 := pfne3) (pf := pfne1).
                 subst; eapply split_newEntries...
                 eapply tEnv_split_add_vis.
                 eauto.
                 eauto.
                 intuition.

                 
                 eauto.
                 eauto.
                 eapply typeCheck_weak2 with (pfk := pfne3).
                 erewrite <-domain_distr...

                   destruct f.
                 (* f = hid *)
                 contradiction.
                 (* f = ill *)
                   eapply flag_of_split_l with (n:= (b1, b2)) in TS2 as FLG.
              assert (F0: flagOf g0 (b1, b2) ill)...
              eapply FLG in F0 as [F0 | ABS].
              eapply typeCheck_ill_vis.
              eauto.
              eauto.
                  (*  In (b1, b2, ill, Top) g3*)
                 eapply tsub_top with (pf := pf1) in TYPb as TYP1b.
              inversion TYP1b. subst g4 n3 t. 
              eapply tsuper_top_r with (pf2 := pf3) in H as K2.
              inversion K2. subst g4 n3 t.
              assert (f1 = ill).
              eapply flag_of_map with (g := g3) (x := (b1, b2)).
              eauto. eauto. intuition.
              subst...
              eauto.
              eauto.
               destruct ABS as [_ ABS1].
              eapply flag_of_split_l with (n:= (b1, b2)) in TS as FLG1.
              apply FLG1 in ABS1.
              clear FLG FLG1.
              intuition.
              (* f = vis *)
              eapply typeCheck_impl with (pf1 := pf3).
              eauto.
              eapply no_dup_cons_removeEntry...
              eauto.
              eapply in_removeEntry_cons_iff_0.
              eauto.
              (*  In (b1, b2, vis, Top) g3*)
                 eapply tsub_top with (pf := pf1) in TYPb as TYP1b.
              inversion TYP1b. subst g4 n3 t. 
              eapply tsuper_top_r with (pf2 := pf3) in H as K2.
              inversion K2. subst g4 n3 t.
              eapply flag_of_split_l with (n:= (b1, b2)) in TS2 as FLG.
              
              assert (F0: flagOf g0 (b1, b2) vis).
              eauto.
              eapply FLG in F0.
              assert (f1 = vis).
              eapply flag_of_map with (x := (b1, b2)) (g := g3).
              intuition. eauto. intuition.
              subst...
              eauto.
              eauto.

                 (* cons ne3 ?pfk *)
                 assert (INVNE: forall c1 c2 ff tt,
                            In (c1, c2, ff, tt) ne3 ->
                            In (c1, c2 - max (domain g3)) (secLabs rp) /\ In (c1, c2 - max (domain g3), ff, tt) g3).
                 intros.
                 eapply inverse_newEntries.
                 eauto.
                 (* sl_pos rp *)
                 eapply sl_pos_par_l in SLP;
                   unfold sl_pos in SLP;
                   unfold sl_pos.
                 eapply incl_pos with (l2 :=(secLabs p1))...
                 (* incl (secLabs rp) (domain g3) *)
                 eapply incl_tran with (m := secLabs p1).
                 assumption.
                 eapply incl_iff with (m1 := domain g0).
                 eapply typeCheck_no_dup with (pf := pf0)...
                 intros. eapply split_domain_m...
                 (*In (c1, c2, ff, tt)
    (newEntries g3
       (map (fun x : name * name => (fst x, snd x + max (domain g3))) (secLabs rp))
       (max (domain g3)))*)
                 subst. erewrite <-identif_seclabs_of_dep_relabel...
                
                 eapply cons_char.
                 destruct ne3. left...
                 right. intros.
                 specialize INVNE with c1 c2 ff tt.
                 apply INVNE in H; clear INVNE.
                 destruct H as [INSL IN3].
                 remember (c2 - max (domain g3)) as c''.
                 assert (ff = ill). 
                 assert (IN1: In (c1, c'') (secLabs p1)).
                 eapply INRP...
                 assert (NOTINSL: ~In (c1, c'') (secLabs p3)).
                 intros ABS.
                 assert (ND: NoDup (secLabs (dPar p1 p3))).
                 eapply typeCheck_no_dup with (pf := pf1)...
                 unfold secLabs in ND. fold secLabs in ND.
                 erewrite no_dup_iff in ND; destruct ND as [ND1 [ND2 DIS]].
                  eapply disjoint_absurd...
                 assert (NOTINFN: ~ In (c1, c'') (fn p3)).
                 intros ABS.
                 assert (DIS: disjoint (fn (dPar p1 p3)) (secLabs (dPar p1 p3))).
                 eapply fn_disjoint_sl with (pf := pf1)...
                 unfold fn, secLabs in DIS;
                   fold fn in DIS; fold secLabs  in DIS.
                 eapply disjoint_absurd with (x:= (c1, c'')) (l := (fn p1 ++ fn p3)) (m := (secLabs p3 ++ secLabs p1)).
                 eauto. eapply in_app_iff; right...
                 eapply in_app_iff; right...
                 assert (IN0: exists tt, In (c1, c'', hid, tt) g0).
                 eapply typeCheck_hid...
                 destruct IN0 as [ttt F0].
                 assert (F1: In (c1, c'') (domain g1)). 
                 eapply split_domain_l_2 with (x := (c1, c'')) in H1; move H1 at bottom.
                 eapply in_g_in_domain in F0; intuition.
                 eapply in_domain_in_g in F1.
                 destruct F1 as [f1 [tt1 F1]].
                 assert (FP: exists f3, flagOf g3 (c1, c'') f3 /\ flag_plus hid f3 f1).
                 eapply split_flag_plus with (pf1 := pf0) (pf2 := pf3) (pf := pf1)...
                 destruct FP as [f3' [F3 FP]].
                 assert (ff = f3').
                 eapply flag_of_map with (g := g3) (x := (c1, c''))...
                 subst ff.
                 assert (F1': flagOf g1 (c1, c'')  hid).
                 eapply fsub_hid...
                 inversion F1'. subst g4 n3 f2.
                 assert (f1 = hid).
                 eapply flag_of_map with (g := g1) (x := (c1, c''))...
                 subst f1.
                 inversion FP...

                 subst.
                 eapply typeCheck_ill with (p := p3)...

                 subst ne3;
                   rewrite identif_seclabs_of_dep_relabel in *;
                   eapply Peirce; intros ABS;
                   eapply not_disjoint in ABS as ([x1 x2] &ABS1 &ABS2);
                   eapply in_bv_lt_max with (pf := pf3) in ABS1;
                   eapply in_domain_in_g in ABS2 as (ff &tt &ABS2);
                   eapply newEntries_gte_max in ABS2;
                   try lia;
                   try eassumption.
                 
                 all:eauto.
              **
                eauto.
              ** eapply tsub_top with (pf := pf1) in TYPb...
              ** tauto.
              ** eauto.
              ** eauto.
              ** eauto.
              ** eauto.
              ** tauto.
              ** eauto.
      + remember n as a1. remember n0 as a2.
        remember n1 as b1. remember n2 as b2.
        (* a = aOut a1 a2 b1 b2 *)
        subst n n0 n1 n2.
        inversion LTSPAR. subst.
        assert (LTS1 := H8). clear H8.
        assert (DIFF : (a1, a2) <> (b1, b2)).
        eapply nonRecActions2...
        apply lts_after_out in LTS0 as TYP0.
         destruct TYP0 as
            [m [ q [t [r [tb [TYP0a [TYP0b TREM0]]]]]]].
         move m at top.
       apply lts_out with (m := m) (ta := Chan m q t) (tb := tb) (q := q) (t := t) (s:= r) in LTS0 as K0.
       apply lts_after_out in LTS1 as TYP1.
       destruct TYP1 as
            [m1 [ q1 [t1 [r1 [tb1 [TYP1a [TYP1b TREM1]]]]]]].
         move m1 at top.
         apply lts_out with (m := m1) (ta := Chan m1 q1 t1) (tb := tb1) (q := q1) (t := t1) (s:= r1) in LTS1 as K1.
         inversion TYP0a; inversion TYP0b; inversion TYP1b; inversion TYP1a; subst.
         assert (m = m1 /\ t = t1).
         eapply tsuper_payload with (pf1 := pf0) in H14.
         destruct H14 as [pp1 TYP1a'].
         inversion TYP1a'; subst.
         assert (Chan m1 pp1 t1 = Chan m q t).
         eapply type_of_map with (g := g0)...
         inversion H4; intuition.
         eauto.
         destruct H0; subst m1 t1.
         assert (TC1 : typeCheck k0 pfk0 p2).
         eapply IHLTS.
         eapply sl_pos_par_l...
         eauto.
         eauto.
         eauto.
         assert (IN0a := H);assert (IN0b := H6);assert(IN1b :=H10);assert(IN1a := H14).
         assert (TC2 := H3).
         clear H1 H2 H3 H6 H H14 H10 IHLTS.
         move TC1 at bottom. move TC2 at bottom.

         move TREM0 at bottom. move TREM1 at bottom.
         assert (IN3b: exists tb3 : piType, typeOf g3 (b1, b2) tb3 /\ type_plus tb tb3 tb1).
         eapply split_type_plus...
         destruct IN3b as [tb3 [IN3b TPb]].
         inversion TREM0; inversion TREM1.
         destruct H0 as [TP1 ISUN1].
         destruct H2 as [TP2 ISUN2].
         assert (SUB := H); assert (SUB1 := H1). clear H H1.
         
         assert (TP3: type_plus r tb3 r1).
         destruct tb1. destruct m0. destruct p.
        inversion TPb; inversion TP1; inversion TP2; subst; try discriminate; inversion H2; inversion H7; inversion H4; inversion H11; subst; eauto;try discriminate.
        inversion TPb; inversion TP1; inversion TP2; subst; try discriminate; inversion H2; inversion H7; inversion H4; inversion H11; subst; eauto;try discriminate.
         inversion TPb; inversion TP1; inversion TP2; subst; try discriminate; inversion H2; inversion H7; inversion H4; inversion H11; subst; eauto;try discriminate.
         inversion TPb; inversion TP1; inversion TP2; subst; try discriminate; inversion H2; inversion H7; inversion H4; inversion H11; subst; eauto;try discriminate.
         inversion TPb; inversion TP1; inversion TP2; subst; try discriminate; destruct ISUN1; destruct ISUN2; unfold is_unrestricted in *; intuition; subst; eauto; inversion H5; inversion H6; subst.
         inversion TPb; inversion TP1; inversion TP2; subst; try discriminate; eauto.

         destruct m.
         (* m = lin *)
         assert (EQK0: k0 =
        (a1, a2, vis, Chan lin empty t)
        :: (b1, b2, vis, r) :: removeEntry (a1, a2) (removeEntry (b1, b2) g0)). 
         intuition.
         assert (EQK1: k1 =
        (a1, a2, vis, Chan lin empty t)
          :: (b1, b2, vis, r1) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)).
         intuition.
         clear K0 K1.

         assert (nd_pfk3 :
                   NoDup
                     (domain
                        ((a1, a2, vis, Chan lin empty t)
                           :: (b1, b2, vis, tb3)
                           :: removeEntry (a1, a2)
                           (removeEntry (b1, b2) g3)))).
         eapply no_dup_cons_removeEntry_app...
         apply no_dup_isMap in nd_pfk3 as pfk3.
         
         eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
         subst k0 k1.
         revert dependent pfk0.
         rewrite removeEntry_shift.
         intros.
         revert dependent pfk3.
         rewrite removeEntry_shift.
         intros.
         revert dependent pfk1.
         rewrite removeEntry_shift.
         intros.
         eapply tEnv_split_add_vis.
         eapply no_dup_cons_removeEntry...
         eauto.
         intros ABS; eapply not_lin_is_unrestricted in ABS; intuition. 
         eapply tEnv_split_add_vis.
         eauto.
         eauto.
         intros ISUN.
         assert (TBUN: is_unrestricted tb).
         unfold is_unrestricted in ISUN; destruct ISUN as [pp1 [tt1 EQ]]; subst; inversion TP1; inversion TP2; subst; try discriminate; eapply un_is_unrestricted.
         assert (TB1UN: is_unrestricted tb1).
         unfold is_unrestricted in ISUN; destruct ISUN as [pp1 [tt1 EQ]]; subst; inversion TP1; inversion TP2; subst; try discriminate; eapply un_is_unrestricted.
         apply ISUN1 in TBUN as TEQ1; apply ISUN2 in TB1UN as TEQ2.
         assert (TYPb: typeOf g3 (b1, b2) tb /\ typeOf g1 (b1, b2) tb). eapply split_plus_un_isrestricted...
         destruct TYPb as [TYP3b TYP1b'].
         subst r r1.
         assert (tb = tb3).  eapply type_of_map with (g := g3)...
         subst tb3.
         assert (tb = tb1).  eapply type_of_map with (g := g1)...
         intuition.

         eauto.
         all:intuition.
         
         assert (nd_pfk3':
                   NoDup
                     (domain
                     ((b1, b2, vis, tb3) ::removeEntry (b1, b2)((a1, a2, vis, Chan lin empty t)
                         :: removeEntry (a1, a2) ( g3))))).
         eapply no_dup_cons_removeEntry, no_dup_cons_removeEntry...
         eapply no_dup_isMap in nd_pfk3' as pfk3'.
         eapply typeCheck_impl with (pf1 := pfk3').
         eauto.
         eauto.
         inversion IN3b; subst. assert (IN3b' := H); clear H.
         (* typeCheck
    ((b1, b2, vis, tb3)
     :: removeEntry (b1, b2)
          ((a1, a2, vis, Chan lin empty t) :: removeEntry (a1, a2) g3)) pfk3' p3*)
         destruct f3.
         (*f3 = hid *)
         eapply finv_hid_r with (pf1 := pf0) in IN3b' as ABS.
         eapply lts_out_not_ill in LTS0. contradiction.
         eauto.
         eauto.
         (*f3 = ill*)
         eapply typeCheck_ill_vis.
         eapply no_dup_cons_removeEntry...
         eapply typeCheck_impl with (pf1 := pf3).
         eauto.
         eauto.
         eauto.
         eapply in_removeEntry_cons_iff_0.
         eauto.
         (*In (a1, a2, vis, Chan lin empty t) g3*)
         assert (EX: In (a1, a2, vis, Chan lin out t ) g0 /\
                 In (a1, a2, vis, Chan lin empty t ) g3 /\
                 In (a1, a2, vis, Chan lin out t ) g1).
         eapply lts_middle...
         destruct EX as [IN0 [IN3 IN1]].
         assert (EQ: Chan lin out t = Chan lin q t).
         eapply type_of_map with (x := (a1, a2)) (g := g0)...
         inversion EQ; subst...
         right. eapply removeEntry_in...
         (* f3 = vis*)
         assert (nd_pf3' : NoDup (domain (((a1, a2, vis, Chan lin empty t) :: removeEntry (a1, a2) g3)))).
         eapply no_dup_cons_removeEntry...
         eapply no_dup_isMap in nd_pf3' as pf3'.
         eapply typeCheck_impl with (pf1 := pf3').
         eauto.
         eauto.
         eapply typeCheck_impl with (pf1 := pf3)...
         eapply in_removeEntry_cons_iff_0.
         eauto.
          (*In (a1, a2, vis, Chan lin empty t) g3*)
         assert (EX: In (a1, a2, vis, Chan lin out t ) g0 /\
                 In (a1, a2, vis, Chan lin empty t ) g3 /\
                 In (a1, a2, vis, Chan lin out t ) g1).
         eapply lts_middle...
         destruct EX as [IN0 [IN3 IN1]].
         assert (EQ: Chan lin out t = Chan lin q t).
         eapply type_of_map with (x := (a1, a2)) (g := g0)...
         inversion EQ; subst...
         eapply in_removeEntry_cons_iff_0.
         eauto.
         right. eapply removeEntry_in...

         rewrite <-removeEntry_shift, removeEntry_swap.
         eapply cons_cons_iff...
         all:intuition.

         subst.  
         clear H H1.

         assert (nd_pfk3 :
                   NoDup
                     (domain
                        ( (b1, b2, vis, tb3)
                           :: 
                           (removeEntry (b1, b2) g3)))).
         eapply no_dup_cons_removeEntry...
         apply no_dup_isMap in nd_pfk3 as pfk3.
         
         eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
         eapply tEnv_split_add_vis.
         eauto.
         eauto.
         intros ISUN.
         assert (TBUN: is_unrestricted tb).
         unfold is_unrestricted in ISUN; destruct ISUN as [pp1 [tt1 EQ]]; subst; inversion TP1; inversion TP2; subst; try discriminate; eapply un_is_unrestricted.
         assert (TB1UN: is_unrestricted tb1).
         unfold is_unrestricted in ISUN; destruct ISUN as [pp1 [tt1 EQ]]; subst; inversion TP1; inversion TP2; subst; try discriminate; eapply un_is_unrestricted.
         apply ISUN1 in TBUN as TEQ1; apply ISUN2 in TB1UN as TEQ2.
         assert (TYPb: typeOf g3 (b1, b2) tb /\ typeOf g1 (b1, b2) tb). eapply split_plus_un_isrestricted...
         destruct TYPb as [TYP3b TYP1b'].
         subst r r1.
         assert (tb = tb3).  eapply type_of_map with (g := g3)...
         subst tb3.
         assert (tb = tb1).  eapply type_of_map with (g := g1)...
         intuition.

         eauto.
         all:intuition.
         
         (*typeCheck ((b1, b2, vis, tb3) :: removeEntry (b1, b2) g3) pfk3 p3*)
         inversion IN3b. subst. assert (IN3b' := H). clear H.
         destruct f3. 
         (*f3 = hid *)
         eapply finv_hid_r with (pf1 := pf0) in IN3b' as ABS.
         eapply lts_out_not_ill in LTS0. contradiction.
         eauto.
         eauto.
         (*f3 = ill*)
         eapply typeCheck_ill_vis...
         eapply typeCheck_impl with (pf1 := pf3).
         eauto.
         eauto.
         eauto.
         eapply in_removeEntry_cons_iff_0.
         eauto.
         eauto.

         
      + remember n as a1. remember n0 as a2.
        subst n. subst n0.
        (* a = aTau a1 a2  *)
        assert (LEM : exists m t, In (a1, a2, vis, Chan m io t) g0 \/ In (a1, a2, hid, Chan m io t) g0).
        eapply type_of_tau_Action...
        destruct LEM as (m &t &[IN0a | IN0a]).
        destruct m.

        (* m = lin *)
        eapply lts_after_tau_lin with (t := t) in LTS0 as EX0.
        destruct EX0 as [b1 [b2 [f0 [tb0 [DIFF [IN0b [NILL EQK0]]]]]]].
        assert (LEM1: exists f1 tb1 f2 tb2,
                   In (b1, b2, f1, tb1) g3 /\ 
                   In (b1, b2, f2, tb2) g1).
        eapply split_sub...
        destruct LEM1 as [f3 [tb3 [f1 [tb1 [IN3b IN1b]]]]].
        inversion LTSPAR; subst.
        
        assert (LTS1 := H8). clear H8.
        eapply lts_after_tau_lin with (t := t) in LTS1 as EX1.
        destruct EX1 as [c1 [c2 [fc [tc [DIFF2 [IN1c [NILL2 EQK1]]]]]]].
        
        assert (pf' : isMap ((b1, b2, f0, tb0) :: removeEntry (b1, b2) g0)).
        eapply isMap_cons_2...
         assert (pf'' : isMap ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3)).
         eapply isMap_cons_2...
         assert (pf''' : isMap ((b1, b2, f1, tb1) :: removeEntry (b1, b2) g1)).
         eapply isMap_cons_2...
         assert (TS': tEnv_split ((b1, b2, f0, tb0) :: removeEntry (b1, b2) g0)
    ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3)
    ((b1, b2, f1, tb1) :: removeEntry (b1, b2) g1)
    pf' pf'' pf''').
         eapply split_cons_remove_3...

         case_eq ( pair_eq (b1, b2) (c1, c2)).
        (* (b1, b2) = (c1, c2) *)
        intros PEQ. rewrite <-pairEq_eq in PEQ; inversion PEQ; subst c1 c2.
        assert (fc = f1 /\ tc = tb1).
        eapply in_isMap with (g := g1)...
        destruct H; subst fc tc.
        assert (nd_pfk3: NoDup (domain ((a1, a2, vis, Chan lin empty t) :: (b1, b2, f3, tb3) :: removeEntry (a1, a2) (removeEntry (b1, b2) g3)))).
        eapply no_dup_cons_removeEntry_app...
        eapply no_dup_isMap in nd_pfk3 as pfk3.

        eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
        revert dependent pfk0. 
        rewrite removeEntry_shift with (b1 := b1).
        intros.
        revert dependent pfk3.
        rewrite removeEntry_shift with (b1 := b1).
        intros.
        revert dependent pfk1.
        subst k1. rewrite removeEntry_shift with (b1 := b1).
        intros.
        eapply tEnv_split_add_vis.
        eapply no_dup_cons_removeEntry...
        eauto.
        intros ABS; eapply not_lin_is_unrestricted in ABS; contradiction.
        eauto.
        all: try assumption.
        (*typeCheck
    ((a1, a2, vis, Chan lin empty t)
     :: (b1, b2, f0, tb0) :: removeEntry (a1, a2) (removeEntry (b1, b2) g0)) pfk0 p2*)
        eapply IHLTS.
        eapply sl_pos_par_l...
        eauto.
        eauto.
        eauto.
        (*typeCheck
    ((a1, a2, vis, Chan lin empty t)
     :: (b1, b2, f3, tb3) :: removeEntry (a1, a2) (removeEntry (b1, b2) g3)) pfk3 p3*)
        eapply typeCheck_impl with (pf1 := pf3).
        eauto.
        eauto.
        eauto.
        eapply in_removeEntry_cons_iff_1.
        eauto.
        (*In (a1, a2, vis, Chan lin empty t) g3*)
        assert (EX:  In (a1, a2, vis, Chan lin io t ) g0 /\
       In (a1, a2, vis, Chan lin empty t ) g3 /\
                       In (a1, a2, vis, Chan lin io t ) g1).
        assert (MIDDLE: In (a1, a2, vis, Chan lin io t) g0 /\
        In (a1, a2, vis, Chan lin empty t) g3 /\ In (a1, a2, vis, Chan lin io t) g1 \/
        In (a1, a2, hid, Chan lin io t) g0 /\
          In (a1, a2, ill, Chan lin empty t) g3 /\ In (a1, a2, hid, Chan lin io t) g1).
        eapply lts_middle...
        destruct MIDDLE as [OK | (ABS1 &_ &_)]...
        assert (vis = hid).
        eapply in_isMap with (g := g0)...
        discriminate.
        

        intuition.
        eauto.


        intros PNEQ. rewrite <-pairEq_neq in PNEQ.
        assert (nd_pfk3: NoDup (domain ((a1, a2, vis, Chan lin empty t) :: (b1, b2, f3, tb3) :: removeEntry (a1, a2) (removeEntry (b1, b2) g3)))).
        eapply no_dup_cons_removeEntry_app...
        eapply no_dup_isMap in nd_pfk3 as pfk3.
        eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
        subst.
       
        subst.
        revert dependent pfk0. 
        rewrite removeEntry_shift with (b1 := b1).
        intros.
        revert dependent pfk3.
        rewrite removeEntry_shift with (b1 := b1).
        intros.
        revert dependent pfk1.
        rewrite removeEntry_shift with (b1 := c1).
        intros.
        (* tEnv_split
    ((a1, a2, vis, Chan lin empty t)
     :: removeEntry (a1, a2) ((b1, b2, f0, tb0) :: removeEntry (b1, b2) g0))
    ((a1, a2, vis, Chan lin empty t)
     :: removeEntry (a1, a2) ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3))
    ((a1, a2, vis, Chan lin empty t)
     :: removeEntry (a1, a2) ((c1, c2, fc, tc) :: removeEntry (c1, c2) g1)) pfk0
    pfk3 pfk1*)
        eapply tEnv_split_add_vis.
        eapply no_dup_cons_removeEntry...
        eauto.
        intros ABS; eapply not_lin_is_unrestricted in ABS; contradiction.
        assert (nd_pfk1' : NoDup (domain
                                    ((b1, b2, f1, tb1) :: removeEntry (b1, b2)((c1, c2, fc, tc) :: removeEntry (c1, c2) g1)))).
        rewrite <-removeEntry_shift with (b1 := c1).
        eapply no_dup_cons_removeEntry_app...
        eauto.
        eapply no_dup_isMap in nd_pfk1' as pfk1'.
        eapply split_iff with (pf := pfk1').
        eauto.
        eauto. 
        (*tEnv_split ((b1, b2, f0, tb0) :: removeEntry (b1, b2) g0)
    ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3)
    ((b1, b2, f1, tb1)
     :: removeEntry (b1, b2) ((c1, c2, fc, tc) :: removeEntry (c1, c2) g1)) 
    ?pf16 ?pf25 pfk1'*)
        destruct f0.
        (* f0 = hid *)
        eapply fsub_hid with (pf := pf1) in IN0b as FY1. 
        inversion FY1; subst. assert (IN1b' := H); clear H.
        eapply fsuper_hid with (pf1 := pf0) (pf2 := pf3) in IN1b' as HSUB.
        destruct HSUB as [[_ FY3] | [ABS _]].
        inversion FY3; subst.  assert (IN3b' := H); clear H.
        assert (f3 = ill). eapply flag_of_map with (g := g3)...
        assert (f1 = hid). eapply flag_of_map with (g := g1)...
        subst.
        eapply split_cons_remove_2. 
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        right. eapply removeEntry_in.
        eauto.
        eauto.
        (*tEnv_split g0 g3 ((c1, c2, fc, tc) :: removeEntry (c1, c2) g1) *)
        eapply split_iff with (pf := pf1)...
        eapply in_removeEntry_cons_iff_0...
        (* ABS *)
        inversion ABS; subst.
        assert (hid = ill). eapply flag_of_map with (g := g0)...
        discriminate.
        eauto.
        eauto.

      (* f0 = ill *)
        contradiction.
      (* f0 = vis *)  
         eapply fsub_vis with (pf := pf1) in IN0b as FY1. 
        inversion FY1; subst. assert (IN1b' := H); clear H.
        eapply fsuper_vis with (pf1 := pf0) (pf2 := pf3) in IN1b' as HSUB.
        destruct HSUB as [_ FY3].
        inversion FY3; subst.  assert (IN3b' := H); clear H.
        assert (f3 = vis). eapply flag_of_map with (g := g3)...
        assert (f1 = vis). eapply flag_of_map with (g := g1)...
        subst.
        eapply split_cons_remove.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        right. eapply removeEntry_in...
        eapply split_iff with (pf := pf1)...
        eapply in_removeEntry_cons_iff_0...
        eauto.
        eauto.
        assert (REV: forall x : name * name * flag * piType,
                   In x ((c1, c2, fc, tc) :: removeEntry (c1, c2) g1) <->
                   In x
    ((b1, b2, f1, tb1)
     :: removeEntry (b1, b2) ((c1, c2, fc, tc) :: removeEntry (c1, c2) g1))).
        eapply in_removeEntry_cons_iff_0.
        eauto.
        right. eapply removeEntry_in...
        intros x. specialize REV with x; repeat intuition. intuition. intuition. intuition.
        (*typeCheck
    ((a1, a2, vis, Chan lin empty t)
     :: (b1, b2, f0, tb0) :: removeEntry (a1, a2) (removeEntry (b1, b2) g0)) pfk0 p2*)
        eapply IHLTS.
        eapply sl_pos_par_l...
        eauto.
        eauto.
        eauto.
        (* typeCheck
    ((a1, a2, vis, Chan lin empty t)
     :: (b1, b2, f3, tb3) :: removeEntry (a1, a2) (removeEntry (b1, b2) g3)) pfk3 p3 *)
        eapply typeCheck_impl with (pf1 := pf3).
        eauto.
        eauto.
        eauto.
        eapply in_removeEntry_cons_iff_1.
        eauto.
         assert (EX:  In (a1, a2, vis, Chan lin io t ) g0 /\
       In (a1, a2, vis, Chan lin empty t ) g3 /\
                        In (a1, a2, vis, Chan lin io t ) g1).

          assert (MIDDLE: In (a1, a2, vis, Chan lin io t) g0 /\
        In (a1, a2, vis, Chan lin empty t) g3 /\ In (a1, a2, vis, Chan lin io t) g1 \/
        In (a1, a2, hid, Chan lin io t) g0 /\
          In (a1, a2, ill, Chan lin empty t) g3 /\ In (a1, a2, hid, Chan lin io t) g1).
        eapply lts_middle...
        destruct MIDDLE as [OK | (ABS1 &_ &_)]...
        assert (vis = hid).
        eapply in_isMap with (g := g0)...
        discriminate.

        intuition.
        eauto.
        eapply tsub_io with (pf := pf1) in IN0a as K.
        inversion K; subst.
        eapply fsub_vis with (pf := pf1) in IN0a as K1.
        assert (f = vis).
        eapply flag_of_map with (g := g1)...
        subst...
        eauto. eauto. 
        
        eapply lts_finite in H14. contradiction.
        eapply lts_finite in H14. contradiction.

        (* m = un *)
        eapply lts_after_tau_un
          with g0 p1 p2 a1 a2 t k0 nd_pf0 nd_pf0 in LTS0 as EX0.
        destruct EX0 as
          (b1 &b2 &fb0 &tb0 &ne &DIFF &IN0b & EQK0 &NEEQ).
        assert (LEM1: exists f1 tb1 f2 tb2,
                   In (b1, b2, f1, tb1) g3 /\ 
                   In (b1, b2, f2, tb2) g1).
        eapply split_sub...
        destruct LEM1 as [f3 [tb3 [f1 [tb1 [IN3b IN1b]]]]].
        inversion LTSPAR; subst.
        all: try eapply lts_finite in H14; try contradiction.
        
        assert (LTS1 := H8). clear H8.
        eapply lts_after_tau_un with (t := t) (nd_pf1 := nd_pf1) in LTS1 as EX1. 
      
        destruct EX1 as [c1 [c2 [fc [tc [ne1 [DIFF2 [INc [EQK1 NE1EQ]]]]]]]].
        
        assert (pf' : isMap ((b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0)).
        eapply isMap_cons_2...
         assert (pf'' : isMap ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3)).
         eapply isMap_cons_2...
         assert (pf''' : isMap ((b1, b2, f1, tb1) :: removeEntry (b1, b2) g1)).
         eapply isMap_cons_2...
         assert (TS': tEnv_split ((b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0)
    ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3)
    ((b1, b2, f1, tb1) :: removeEntry (b1, b2) g1)
    pf' pf'' pf''').
         eapply split_cons_remove_3...

        
        

         case_eq ( pair_eq (b1, b2) (c1, c2)).
        (* (b1, b2) = (c1, c2) *)
         intros PEQ. rewrite <-pairEq_eq in PEQ.
          
        inversion PEQ;  subst c1 c2.
        assert (fc = f1 /\ tc = tb1).
        eapply in_isMap with (g := g1)...
        destruct H; subst tc fc.

        move EQK0 at bottom.
        move EQK1 at bottom.
        move NEEQ at bottom.
        move NE1EQ at bottom.
        destruct EQK0 as [[EQK0 NILL]| [EQK0 EQ]].
        (*subst fb0.*)
        destruct EQK1 as [[EQK1 NILL2] | [EQK1 EQ]].
        (*subst f1.*)
        destruct NE1EQ as [NE1NIL | REPL1].
        destruct NEEQ as [NENIL | REPL].
        
        assert (nd_pfk3: NoDup (domain ((b1, b2, f3, tb3) :: (removeEntry (b1, b2) g3)))).
        eapply no_dup_cons_removeEntry...
        eapply no_dup_isMap in nd_pfk3 as pfk3.

        
        (**) eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
        subst.
        eapply split_cons_remove_3...
        eauto.
        eapply typeCheck_impl with (pf1 := pf3),in_removeEntry_cons_iff_0...


        (**)
          assert (ne = ne1).
          destruct REPL as [q [REPL [INCL NEEQ]]].

                   
        assert (ne1 = newEntries g1
                                 (secLabs (dep_relabel q (domain g1) nd_pf1))
                                 (max (domain g1))).
        assert (W0:  incl (secLabs p1) (domain (hid_proj g1))).
        eapply typeCheck_hid_proj_par...
        assert (W1:  NoDup (secLabs p1)).
        eapply typeCheck_no_dup with (pf := pf0)...
        assert (W2: In (a1, a2, vis, Chan un io t) g1).
        eapply tsub_un with (pf := pf1) in IN0a as INa. inversion INa; subst; clear INa.
        eapply fsub_vis with (pf := pf1) in IN0a as INa. 
        assert (f = vis). eapply flag_of_map with (g := g1)...
        subst...
        eauto.
        eauto.
        assert (W3 :  In (b1, b2) (domain g1)). eapply in_g_in_domain...
        destruct f1; subst ne1.
        eapply lts_un_tau_action_newEntries_2 with (b1 := b1) (b2 := b2) (g1 := k1)...
        right;simpl; try rewrite pairEq_eq_true...
        contradiction.
         eapply lts_un_tau_action_newEntries_2 with (b1 := b1) (b2 := b2) (g1 := k1)...
        
        
        assert (ne = nil).
        subst; eapply newEntries_nil with (g := g1).
        eauto.
        intros. assert ( In x (domain g0) <-> In x (domain g1)).
        eapply split_domain_l...
        intuition auto.
        assert (MAX: max (domain g0) = max (domain g1)).
        eapply max_same_domain...
        erewrite identif_seclabs_of_dep_relabel;
        erewrite MAX,<-identif_seclabs_of_dep_relabel...
        subst...
        
        subst.
         assert (nd_pfk3: NoDup (domain ((b1, b2, f3, tb3) :: (removeEntry (b1, b2) g3)))).
        eapply no_dup_cons_removeEntry...
        eapply no_dup_isMap in nd_pfk3 as pfk3.
        eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
        subst.
        eapply split_cons_remove_3...
        eauto.
        eapply typeCheck_impl with (pf1 := pf3),in_removeEntry_cons_iff_0...

      
        (**)
        
        destruct NEEQ as [NENIL | REPL].
        assert (ne1 = ne).
        destruct REPL1 as [q [REPL [INCL NEEQ]]].
        assert (ne = newEntries g0
                                 (secLabs (dep_relabel q (domain g0) nd_pf0))
                                 (max (domain g0))).
         assert (W0:  incl (secLabs p1) (domain (hid_proj g0)))...
         
        assert (W1:  NoDup (secLabs p1)).
        eapply typeCheck_no_dup with (pf := pf0)...
        assert (W2: In (a1, a2, vis, Chan un io t) g1).
        eapply tsub_un with (pf := pf1) in IN0a as INa. inversion INa; subst; clear INa.
        eapply fsub_vis with (pf := pf1) in IN0a as INa. 
        assert (f = vis). eapply flag_of_map with (g := g1)...
        subst...
        eauto.
        eauto.
        assert (W3 :  In (b1, b2) (domain g0)). eapply in_g_in_domain...
        destruct fb0; subst ne.
        eapply lts_un_tau_action_newEntries_2 with (b1 := b1) (b2 := b2)...
        right;simpl; try rewrite pairEq_eq_true...
        contradiction.
         eapply lts_un_tau_action_newEntries_2 with (b1 := b1) (b2 := b2)...
        assert (f1 = fb0).
        destruct f1.
        eapply fsuper_hid with (n := (b1,b2)) in TS'
            as [(OK &_)  | (ABS &_)].
        inverts OK as OK; inverts OK as K;
          try inv K; try tauto.
        assert (~In (b1, b2, hid, t0) (removeEntry (b1, b2) g0)).
        eapply no_dup_not_in_removeEntry...
        contradiction.
        
        inverts ABS as ABS; inverts ABS as K; try inv K;
          try contradiction.
        
        assert (~In (b1, b2, ill, t0) (removeEntry (b1, b2) g0)).
        eapply no_dup_not_in_removeEntry...
        contradiction.
        eauto.
        contradiction.
        eapply fsuper_vis with (n := (b1,b2))  in TS'
            as (OK &_).
          inverts OK as OK; inverts OK as K;
          try inv K; try tauto.
          assert (~In (b1, b2, vis, t0) (removeEntry (b1, b2) g0)).
          eapply no_dup_not_in_removeEntry...
          contradiction.
         eauto.
        assert (ne1 = nil).
        subst ne1. eapply newEntries_nil with (g := g0).
        eauto.
        intros; eapply split_domain_l...
        intuition auto.
        assert (MAX: max (domain g1) = max (domain g0)).
        eapply max_same_domain...
        erewrite identif_seclabs_of_dep_relabel,MAX,<-identif_seclabs_of_dep_relabel, <-H...
        subst...

        subst.
        assert (nd_pfk3: NoDup (domain ((b1, b2, f3, tb3) :: (removeEntry (b1, b2) g3)))).
        eapply no_dup_cons_removeEntry...
        eapply no_dup_isMap in nd_pfk3 as pfk3.
        eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
        subst.
        eapply split_cons_remove_3...
        eauto.
        eapply typeCheck_impl with (pf1 := pf3),in_removeEntry_cons_iff_0...

        (* replicated case *)
        destruct REPL1 as [q1 [REPL1 [INCL1 NEEQ1]]].
        destruct REPL as [q [REPL [INCL NEEQ]]].
        assert (q = q1). eapply replication_unique...
        subst q1.

        remember (newEntries g3 (secLabs (dep_relabel q (domain g3) nd_pf3)) (max (domain g3))) as ne3.
        assert (nd_pfk3: NoDup (domain (ne3 ++ (b1, b2, f3, tb3) :: (removeEntry (b1, b2) g3)))).
        erewrite domain_distr. eapply distr_no_dup.
        subst. eapply newEntries_no_dup.
        eapply wf_rewrite,prop27,incl_incl2.
       eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
       eauto.
       eapply incl_tran with (m := secLabs p1)...
       eapply incl_iff with (m1 := (domain g0)).
       eapply typeCheck_no_dup with (pf := pf0)...
       intros; eapply split_domain_m...
       eauto.
       eapply no_dup_cons_removeEntry...
       assert (DIS : disjoint (domain g3) (domain ne3)).
       subst; eapply new_entries_disjoint.
        unfold sl_pos, pos in *; intros.
        specialize SLP with x1 x2;
          unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL; specialize INCL with (x1,x2); intuition.
         assert (MAX2: max(domain g3) >= max (secLabs q)).
        eapply incl_preserves_max, incl_tran with (m := secLabs p1)... assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        eapply incl_iff with (m1 := domain g0);
          try eassumption.
        intros; eapply split_domain_m...  
        lia.
        assert (NIN: ~In (b1, b2) (domain ne3)).
        intros ABS.
        assert (INB: In (b1, b2) (domain g3)).
        eapply in_g_in_domain...
        eapply disjoint_absurd...  
        eapply disjoint_commute, disjoint_cons_removeEntry...
        apply no_dup_isMap in nd_pfk3 as pfk3.
        eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
        subst.
        eapply split_distr.
        eapply split_newEntries...
        eapply split_cons_remove_3...
        eauto.
        
        (* typeCheck (ne3 ++ (b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) pfk3 p3 *)
        assert (nd_pfne3g3: NoDup (domain (ne3 ++ g3))).
        erewrite domain_distr. eapply distr_no_dup.
        subst; eapply newEntries_no_dup...
        eapply wf_rewrite,prop27,incl_incl2.
        eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
        eauto.
        eapply incl_tran with (m := secLabs p1)...
        assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        eapply incl_iff with (m1 := domain g0); try eassumption.
        intros; eapply split_domain_m...
        eauto.
        subst; erewrite disjoint_commute; eapply new_entries_disjoint.
        unfold sl_pos, pos in *; intros.
        specialize SLP with x1 x2;
          unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL; specialize INCL with (x1,x2); intuition.
        assert (MAX: max(domain g1) >= max (secLabs q)).
        eapply incl_preserves_max, incl_tran with (m := secLabs p1)... assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        eapply incl_iff with (m1 := domain g0)...
        erewrite split_max with (pf := pf1). lia.
        eapply split_comm...
        eapply no_dup_isMap in nd_pfne3g3 as pfne3g3.
        
        
        eapply typeCheck_impl with (pf1 := pfne3g3).
        eauto. eauto.
        eapply typeCheck_weak2.
        erewrite <-domain_distr...
        eauto.
        (* cons ne3 ?pfk *)
        assert (INVNE: forall c1 c2 ff tt,
                   In (c1, c2, ff, tt) ne3 ->
                   In (c1, c2 - max (domain g3)) (secLabs q) /\ In (c1, c2 - max (domain g3), ff, tt) g3).
        intros.
        eapply inverse_newEntries.
        eauto.
        (* sl_pos rp *)
                 eapply sl_pos_par_l in SLP;
                   unfold sl_pos in SLP;
                   unfold sl_pos.
                 eapply incl_pos with (l2 :=(secLabs p1))...
        (* incl (secLabs rp) (domain g3) *)
        eapply incl_tran with (m := secLabs p1).
        assumption.
        eapply incl_iff with (m1 := domain g0).
        eapply typeCheck_no_dup with (pf := pf0)...
        intros. eapply split_domain_m... 
        (*In (c1, c2, ff, tt)
    (newEntries g3
       (map (fun x : name * name => (fst x, snd x + max (domain g3))) (secLabs rp))
       (max (domain g3)))*)
        subst. erewrite <-identif_seclabs_of_dep_relabel...
        eapply cons_char.
        destruct ne3. left...
        right. intros.
        specialize INVNE with c1 c2 ff tt.
        apply INVNE in H; clear INVNE.
        destruct H as [INSL IN3'].
        remember (c2 - max (domain g3)) as c''.
        assert (IN2: exists t, In (c1, c'',hid, t) g0).
        eapply typeCheck_hid...
        destruct IN2 as [tt0 IN2].
        assert (ff = ill).
        assert (IN1: In (c1, c'') (secLabs p1)).
        eapply INCL...
        assert (flagOf g3 (c1, c'') ill).
        eapply finv_hid_r,split_comm...
        eapply flag_of_map with (g := g3)...
        subst ff.
        assert (F1': flagOf g1 (c1, c'')  hid).
        eapply fsub_hid... 
        inversion F1'. subst g4 n f.
        eapply typeCheck_ill with (p := p3)...

        subst ne3;
          rewrite identif_seclabs_of_dep_relabel in *;
          eapply Peirce; intros ABS;
          eapply not_disjoint in ABS as ([x1 x2] &ABS1 &ABS2);
          eapply in_bv_lt_max with (pf := pf3) in ABS1;
          eapply in_domain_in_g in ABS2 as (ff &tt &ABS2);
          eapply newEntries_gte_max in ABS2;
          try lia;
          try eassumption.
        
        eapply in_app_removeEntry_iff_0...
        

       
        (* uclose *)
        (**) subst f1.
           
        assert (fb0 = hid).
        eapply fsuper_hid with (n := (b1,b2))in TS' as [(OK &_) | (ABS &_)].
        inverts OK as OK; inv OK. try inv H;try contradiction; try tauto.
        assert (~In (b1, b2, hid, t0) (removeEntry (b1, b2) g0)).
        eapply no_dup_not_in_removeEntry...
        contradiction.
        inverts ABS as OK; inv OK. inv H; try contradiction; try tauto.
        assert (~In (b1, b2, ill, t0) (removeEntry (b1, b2) g0)).
        eapply no_dup_not_in_removeEntry...
        contradiction.
        eauto.
        subst fb0.
       
        
        destruct NE1EQ as [NE1NIL | REPL1].
        destruct NEEQ as [NENIL | REPL].
        
        
        assert (nd_pfk3: NoDup (domain ((b1, b2, f3, tb3) :: (removeEntry (b1, b2) ((b1, b2, vis, tb3) ::removeEntry (b1, b2)g3))))).
        eapply no_dup_cons_removeEntry,no_dup_cons_removeEntry...
        eapply no_dup_isMap in nd_pfk3 as pfk3.

        simpl in pfk3; rewrite pairEq_eq_true in pfk3.
        gen pfk1. rewrite EQK1,   NE1NIL; simpl;
          rewrite pairEq_eq_true; intros.
        
        eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
        subst.
        assert ( NoDup (domain (nil ++ (b1, b2, vis, tb1) :: removeEntry (b1, b2) g1))).
        eapply no_dup_cons_removeEntry...
        
       
        assert (TB3: exists tb3', typeOf  ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1, b2) tb3' /\ type_plus tb0 tb3' tb1).
        eapply split_type_plus with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
        destruct TB3 as (tb3' & TB3 & TP3).
        assert (tb3' = tb3).
        inversion TB3; inversion H0. inversion H7...
        assert (~In (b1, b2, f, tb3') (removeEntry (b1, b2) g3)). eapply no_dup_not_in_removeEntry...
        contradiction.
        subst tb3'.
         assert (FB3:  exists f3' : flag, flagOf  ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1, b2) f3' /\ flag_plus hid f3' hid).
         eapply split_flag_plus with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
         destruct FB3 as (f3' &FYP3 & FP3).
         assert (f3 = f3').
          inversion FYP3; inversion H0. inversion H7...
        assert (~In (b1, b2, f3', t0) (removeEntry (b1, b2) g3)). eapply no_dup_not_in_removeEntry...
        contradiction.
         subst f3'.
         assert (is_unrestricted tb1 -> tb0 = tb3 /\ tb3 = tb1).
         intros ISUN. destruct ISUN as (q &tt &ISUN).
         subst tb1.
         assert (EX0: exists p1 : pol, typeOf ((b1, b2, hid, tb0) :: removeEntry (b1, b2) g0) (b1, b2) (Chan un p1 tt)).
         eapply tsuper_payload with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
         assert (EX3:  exists p2 : pol, typeOf ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1, b2) (Chan un p2 tt)).
         eapply tsuper_payload_r with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
         destruct EX0 as (pp0 & TB0).
         destruct EX3 as (pp3 & TB3').
         assert (tb0 = Chan un pp0 tt).
         eapply type_of_map with (g := ((b1, b2, hid, tb0) :: removeEntry (b1, b2) g0))...
         assert (tb3 = Chan un pp3 tt).
         eapply type_of_map with (g := ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3))...
         subst tb0 tb3.
         assert (pp0 = pp3 /\ pp3 = q).
         eapply split_plus_un...
         destruct H0; subst pp0 pp3...

         simpl.
         eapply tEnv_split_add_fp... 
         eauto.
        eapply typeCheck_impl with (pf1 := pf3),in_removeEntry_cons_iff_0...

        assert (ne = ne1).
        destruct REPL as [q [REPL [INCL NEEQ]]].
        assert (ne1 = newEntries g1
                                 (secLabs (dep_relabel q (domain g1) nd_pf1))
                                 (max (domain g1))).
        assert (W0:  incl (secLabs p1) (domain (hid_proj g1))).
        eapply typeCheck_hid_proj_par...
        assert (W1:  NoDup (secLabs p1)).
        eapply typeCheck_no_dup with (pf := pf0)...
        assert (W2: In (a1, a2, vis, Chan un io t) g1).
        eapply tsub_un with (pf := pf1) in IN0a as INa. inversion INa; subst; clear INa.
        eapply fsub_vis with (pf := pf1) in IN0a as INa. 
        assert (f = vis). eapply flag_of_map with (g := g1)...
        subst...
        eauto.
        eauto.
        assert (W3 :  In (b1, b2) (domain g1)). eapply in_g_in_domain...
        eapply lts_un_tau_action_newEntries_2 with (b1 := b1) (b2 := b2)...
        assert (ne = nil).
        subst; eapply newEntries_nil with (g := g1).
        eauto.
        intros. assert ( In x (domain g0) <-> In x (domain g1)).
        eapply split_domain_l...
        intuition auto.
        assert (MAX: max (domain g0) = max (domain g1)).
        eapply max_same_domain...
        erewrite identif_seclabs_of_dep_relabel,MAX,<-identif_seclabs_of_dep_relabel...
        subst...
        
        
        subst.

        assert (nd_pfk3: NoDup (domain ((b1, b2, f3, tb3) :: (removeEntry (b1, b2) ((b1, b2, vis, tb3) ::removeEntry (b1, b2)g3))))).
        eapply no_dup_cons_removeEntry,no_dup_cons_removeEntry...
        eapply no_dup_isMap in nd_pfk3 as pfk3.

         simpl in pfk3; rewrite pairEq_eq_true in pfk3.
        gen pfk1; simpl;
          rewrite pairEq_eq_true; intros.

        eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
        simpl.
        subst.
        assert ( NoDup (domain (nil ++ (b1, b2, vis, tb1) :: removeEntry (b1, b2) g1))).
        eapply no_dup_cons_removeEntry...
        assert (TB3: exists tb3', typeOf  ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1, b2) tb3' /\ type_plus tb0 tb3' tb1).
        eapply split_type_plus with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
        destruct TB3 as (tb3' & TB3 & TP3).
        assert (tb3' = tb3).
        inversion TB3; inversion H0. inversion H7...
        assert (~In (b1, b2, f, tb3') (removeEntry (b1, b2) g3)). eapply no_dup_not_in_removeEntry...
        contradiction.
        subst tb3'.
         assert (FB3:  exists f3' : flag, flagOf  ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1, b2) f3' /\ flag_plus hid f3' hid).
         eapply split_flag_plus with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
         destruct FB3 as (f3' &FYP3 & FP3).
         assert (f3 = f3').
          inversion FYP3; inversion H0. inversion H7...
        assert (~In (b1, b2, f3', t0) (removeEntry (b1, b2) g3)). eapply no_dup_not_in_removeEntry...
        contradiction.
         subst f3'.
         assert (is_unrestricted tb1 -> tb0 = tb3 /\ tb3 = tb1).
         intros ISUN. destruct ISUN as (q &tt &ISUN).
         subst tb1.
         assert (EX0: exists p1 : pol, typeOf ((b1, b2, hid, tb0) :: removeEntry (b1, b2) g0) (b1, b2) (Chan un p1 tt)).
         eapply tsuper_payload with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
         assert (EX3:  exists p2 : pol, typeOf ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1, b2) (Chan un p2 tt)).
         eapply tsuper_payload_r with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
         destruct EX0 as (pp0 & TB0).
         destruct EX3 as (pp3 & TB3').
         assert (tb0 = Chan un pp0 tt).
         eapply type_of_map with (g := ((b1, b2, hid, tb0) :: removeEntry (b1, b2) g0))...
         assert (tb3 = Chan un pp3 tt).
         eapply type_of_map with (g := ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3))...
         subst tb0 tb3.
         assert (pp0 = pp3 /\ pp3 = q).
         eapply split_plus_un...
         destruct H0; subst pp0 pp3...

         eapply tEnv_split_add_fp... 
         eauto.
        eapply typeCheck_impl with (pf1 := pf3),in_removeEntry_cons_iff_0...

        destruct NEEQ as [NENIL | REPL].
        assert (ne1 = ne).
        destruct REPL1 as [q [REPL [INCL NEEQ]]].
        assert (ne = newEntries g0
                                 (secLabs (dep_relabel q (domain g0) nd_pf0))
                                 (max (domain g0))).
         assert (W0:  incl (secLabs p1) (domain (hid_proj g0)))... 
        (*assert (IN0: incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup...
        eapply incl_iff with (m2 := domain g) in IN0.
        unfold incl in *; intros a IN1; specialize IN0 with a;
          eapply IN0 in IN1 as K; eapply in_domain_in_g in K as (ff &tt &K). Search secLabs hid. *)
        
        assert (W1:  NoDup (secLabs p1)).
        eapply typeCheck_no_dup with (pf := pf0)...
        assert (W3 :  In (b1, b2) (domain g0)). eapply in_g_in_domain...
        subst ne.
        eapply lts_un_tau_action_newEntries_2 with (b1 := b1) (b2 := b2)...
        right;simpl; try rewrite pairEq_eq_true...
        assert (ne1 = nil).
        subst ne1; eapply newEntries_nil with (g := g0).
        eauto.
        intros; eapply split_domain_l...
        intuition auto.
        assert (MAX: max (domain g1) = max (domain g0)).
        eapply max_same_domain...
        erewrite identif_seclabs_of_dep_relabel,MAX,<-identif_seclabs_of_dep_relabel, <-H...
        subst...

        subst.
        assert (nd_pfk3: NoDup (domain ((b1, b2, f3, tb3) :: (removeEntry (b1, b2) ((b1, b2, vis, tb3) ::removeEntry (b1, b2)g3))))).
        eapply no_dup_cons_removeEntry,no_dup_cons_removeEntry...
        eapply no_dup_isMap in nd_pfk3 as pfk3.

         simpl in pfk3; rewrite pairEq_eq_true in pfk3.
        gen pfk1; simpl;
          rewrite pairEq_eq_true; intros.

        eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
        subst.
        assert ( NoDup (domain (nil ++ (b1, b2, vis, tb1) :: removeEntry (b1, b2) g1))).
        eapply no_dup_cons_removeEntry...
        assert (TB3: exists tb3', typeOf  ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1, b2) tb3' /\ type_plus tb0 tb3' tb1).
        eapply split_type_plus with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
        destruct TB3 as (tb3' & TB3 & TP3).
        assert (tb3' = tb3).
        inversion TB3; inversion H0. inversion H7...
        assert (~In (b1, b2, f, tb3') (removeEntry (b1, b2) g3)). eapply no_dup_not_in_removeEntry...
        contradiction.
        subst tb3'.
         assert (FB3:  exists f3' : flag, flagOf  ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1, b2) f3' /\ flag_plus hid f3' hid).
         eapply split_flag_plus with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
         destruct FB3 as (f3' &FYP3 & FP3).
         assert (f3 = f3').
          inversion FYP3; inversion H0. inversion H7...
        assert (~In (b1, b2, f3', t0) (removeEntry (b1, b2) g3)). eapply no_dup_not_in_removeEntry...
        contradiction.
         subst f3'.
         assert (is_unrestricted tb1 -> tb0 = tb3 /\ tb3 = tb1).
         intros ISUN. destruct ISUN as (q &tt &ISUN).
         subst tb1.
         assert (EX0: exists p1 : pol, typeOf ((b1, b2, hid, tb0) :: removeEntry (b1, b2) g0) (b1, b2) (Chan un p1 tt)).
         eapply tsuper_payload with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
         assert (EX3:  exists p2 : pol, typeOf ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1, b2) (Chan un p2 tt)).
         eapply tsuper_payload_r with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
         destruct EX0 as (pp0 & TB0).
         destruct EX3 as (pp3 & TB3').
         assert (tb0 = Chan un pp0 tt).
         eapply type_of_map with (g := ((b1, b2, hid, tb0) :: removeEntry (b1, b2) g0))...
         assert (tb3 = Chan un pp3 tt).
         eapply type_of_map with (g := ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3))...
         subst tb0 tb3.
         assert (pp0 = pp3 /\ pp3 = q).
         eapply split_plus_un...
         destruct H0; subst pp0 pp3...

         eapply tEnv_split_add_fp...

         eauto.
        eapply typeCheck_impl with (pf1 := pf3),in_removeEntry_cons_iff_0...

        (* replicated case *)
        destruct REPL1 as [q1 [REPL1 [INCL1 NEEQ1]]].
        destruct REPL as [q [REPL [INCL NEEQ]]].
        assert (q = q1). eapply replication_unique...
        subst q1.

        
        remember (newEntries g3 (secLabs (dep_relabel q (domain g3) nd_pf3)) (max (domain g3))) as ne3.
        assert (nd_pfk3': NoDup (domain (ne3 ++  ((b1, b2, vis, tb3) ::removeEntry (b1, b2)g3)))).
        erewrite domain_distr. eapply distr_no_dup.
        subst. eapply newEntries_no_dup.
        eapply wf_rewrite,prop27,incl_incl2.
       eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
       eauto.
       eapply incl_tran with (m := secLabs p1)...
       eapply incl_iff with (m1 := (domain g0)).
       eapply typeCheck_no_dup with (pf := pf0)...
       intros; eapply split_domain_m...
       eauto.
       eapply no_dup_cons_removeEntry...
       assert (DIS : disjoint (domain g3) (domain ne3)).
       subst; eapply new_entries_disjoint.
        unfold sl_pos, pos in *; intros.
        specialize SLP with x1 x2;
          unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL; specialize INCL with (x1,x2); intuition.
         assert (MAX2: max(domain g3) >= max (secLabs q)).
        eapply incl_preserves_max, incl_tran with (m := secLabs p1)... assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        eapply incl_iff with (m1 := domain g0);
          try eassumption.
        intros; eapply split_domain_m...  
        lia.
         assert (NIN: ~In (b1, b2) (domain ne3)).
        intros ABS.
        assert (INB: In (b1, b2) (domain g3)).
        eapply in_g_in_domain...
        eapply disjoint_absurd...
        eapply disjoint_commute, disjoint_cons_removeEntry...
        
        assert (nd_pfk3: NoDup (domain ((b1, b2, f3, tb3) :: (removeEntry (b1, b2) (ne3 ++  ((b1, b2, vis, tb3) ::removeEntry (b1, b2)g3)))))).
        eapply no_dup_cons_removeEntry...
        apply no_dup_isMap in nd_pfk3 as pfk3.

        
        eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
        subst.
        
        remember (newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0))) as ne0.
        assert (nd_pfk0': NoDup (domain (ne0 ++  ((b1, b2, vis, tb0) ::removeEntry (b1, b2)g0)))).
        erewrite domain_distr. eapply distr_no_dup.
        subst. eapply newEntries_no_dup.
        eapply wf_rewrite,prop27,incl_incl2.
       eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
       eauto.
       eapply incl_tran with (m := secLabs p1)...
       eapply typeCheck_no_dup with (pf := pf0)...
       eapply no_dup_split_no_dup_l with (pf1 := pf0)(pf2 := pf3) (pf := pf1)...
       eapply no_dup_cons_removeEntry...
       assert (DIS : disjoint (domain g0) (domain ne0)).
       subst; eapply new_entries_disjoint.
        unfold sl_pos, pos in *; intros.
        specialize SLP with x1 x2;
          unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL; specialize INCL with (x1,x2); intuition.
         assert (MAX2: max(domain g0) >= max (secLabs q)).
        eapply incl_preserves_max, incl_tran with (m := secLabs p1)... 
        eapply typeCheck_no_dup with (pf := pf0)...
        lia.
         assert (NIN: ~In (b1, b2) (domain ne0)).
        intros ABS.
        assert (INB: In (b1, b2) (domain g0)).
        eapply in_g_in_domain...
        eapply disjoint_absurd...
        eapply disjoint_commute, disjoint_cons_removeEntry...

        remember (newEntries g1 (secLabs (dep_relabel q (domain g1) nd_pf1)) (max (domain g1))) as ne1.
        assert (nd_pfk1': NoDup (domain (ne1 ++  ((b1, b2, vis, tb1) ::removeEntry (b1, b2)g1)))).
        erewrite domain_distr. eapply distr_no_dup.
        subst ne1; eapply newEntries_no_dup.
        eapply wf_rewrite,prop27,incl_incl2.
       eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
       eauto.
       eapply incl_tran with (m := secLabs p1)...
       eapply incl_iff with (m1 := (domain g0)).
       eapply typeCheck_no_dup with (pf := pf0)...
       intros; eapply split_domain_l...
       eauto.
       eapply no_dup_cons_removeEntry...
       assert (DIS : disjoint (domain g1) (domain ne1)).
       subst ne1; eapply new_entries_disjoint.
        unfold sl_pos, pos in *; intros.
        specialize SLP with x1 x2;
          unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL; specialize INCL with (x1,x2); intuition.
         assert (MAX2: max(domain g1) >= max (secLabs q)).
        eapply incl_preserves_max, incl_tran with (m := secLabs p1)... assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        eapply incl_iff with (m1 := domain g0)...
        lia.
         assert (NIN: ~In (b1, b2) (domain ne1)).
        intros ABS.
        assert (INB: In (b1, b2) (domain g1)).
        eapply in_g_in_domain...
        eapply disjoint_absurd...
        eapply disjoint_commute, disjoint_cons_removeEntry...
        
        assert (TB3: exists tb3', typeOf  ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1, b2) tb3' /\ type_plus tb0 tb3' tb1).
        eapply split_type_plus with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
        destruct TB3 as (tb3' & TB3 & TP3).
        assert (tb3' = tb3).
        inversion TB3. inversion H. inversion H6...
        assert (~In (b1, b2, f, tb3') (removeEntry (b1, b2) g3)). eapply no_dup_not_in_removeEntry...
        contradiction.
        subst tb3'.
         assert (FB3:  exists f3' : flag, flagOf  ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1, b2) f3' /\ flag_plus hid f3' hid).
         eapply split_flag_plus with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
         destruct FB3 as (f3' &FYP3 & FP3).
         assert (f3 = f3').
          inversion FYP3; inversion H. inversion H6...
        assert (~In (b1, b2, f3', t0) (removeEntry (b1, b2) g3)). eapply no_dup_not_in_removeEntry...
        contradiction.
         subst f3'.
         assert (is_unrestricted tb1 -> tb0 = tb3 /\ tb3 = tb1).
         intros ISUN. destruct ISUN as (q1 &tt &ISUN).
         subst tb1.
         assert (EX0: exists p1 : pol, typeOf ((b1, b2, hid, tb0) :: removeEntry (b1, b2) g0) (b1, b2) (Chan un p1 tt)).
         eapply tsuper_payload with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
         assert (EX3:  exists p2 : pol, typeOf ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1, b2) (Chan un p2 tt)).
         eapply tsuper_payload_r with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
         destruct EX0 as (pp0 & TB0).
         destruct EX3 as (pp3 & TB3').
         assert (tb0 = Chan un pp0 tt).
         eapply type_of_map with (g := ((b1, b2, hid, tb0) :: removeEntry (b1, b2) g0))...
         assert (tb3 = Chan un pp3 tt).
         eapply type_of_map with (g := ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3))...
         subst tb0 tb3.
         assert (pp0 = pp3 /\ pp3 = q1).
         eapply split_plus_un...
         destruct H; subst pp0 pp3...

           assert (ND:=nd_pfk0').
         rewrite Heqne0,domain_distr,no_dup_iff in ND;
           destruct ND as (ND1 &ND2 &DIS).
         assert (nd_pfk0'': NoDup
    (domain
       ( (b1, b2, hid, tb0) ::
           removeEntry (b1, b2)(newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0)) ++
           (b1, b2, vis, tb0)::removeEntry (b1, b2) g0)))).
         erewrite removeEntry_app_shift;
           simpl; try rewrite pairEq_eq_true.
       
         econstructor; try intros ABS;
           try rewrite domain_distr in ABS;
           try eapply in_app_iff in ABS as [ABS1|ABS2].
         simpl in DIS; try eapply disjoint_absurd...
         eapply in_domain_in_g in ABS2 as (ff &tt &ABS2).
         assert (NIN: ~In(b1, b2, ff, tt) (removeEntry (b1, b2) g0)).
         eapply no_dup_not_in_removeEntry...
         contradiction.
         rewrite Heqne0 in *.
         erewrite domain_distr in nd_pfk0';
           simpl in nd_pfk0';

           eapply NoDup_remove in nd_pfk0' as [ND _];
           rewrite domain_distr...
         intros ABS.
         eapply disjoint_absurd...
         
         
         
         eapply no_dup_isMap in nd_pfk0'' as pfk0''.
        try rewrite NEEQ1; eapply split_comm,
           split_iff2 with (pf2 := pfk0'');
          try eapply split_comm, tEnv_split_add_fp;
          try eassumption.

        
        eapply split_distr.
        subst ne1; 
        eapply split_newEntries...
        eapply tEnv_split_add_vis...

        (* forall x : name * name * flag * piType,
  In x
    ((b1, b2, hid, tb0)
     :: removeEntry (b1, b2)
          (ne0 ++
           (b1, b2, vis, tb0) :: removeEntry (b1, b2) g0)) <->
  In x (ne0 ++ (b1, b2, hid, tb0) :: removeEntry (b1, b2) g0) *)
        rewrite <-Heqne0.
        specialize in_app_removeEntry_iff
          with (b1 := b1) (b2 := b2) (f := hid) (t := tb0)
               (w := ne0) (g := g0) as APPIFF.
        assert ( NoDup (domain (ne0 ++ g0))).
        subst ne0; try rewrite domain_distr;
          try eapply no_dup_iff; repeat split;
          try eapply disjoint_commute;
          try eapply new_entries_disjoint;try eapply sl_pos_repl;
          try eapply incl_preserves_max,incl_tran,typeCheck_no_dup;
          try eassumption.
        assert (   ~ In (b1, b2) (domain ne0)).
        intros ABS;
          subst ne0;
        try eapply disjoint_absurd...
        intros; split; introv IN; try rewrite <-  APPIFF;
          try assumption.
        assert (IN2 := IN).
        rewrite removeEntry_app_shift in IN;
          simpl in IN; try rewrite pairEq_eq_true in IN;
          intuition; subst...
        destruct x. destruct p .
        assert (DIFFx: p <> (b1,b2)).
        introv ABS; subst.
        eapply in_g_in_domain in H5;
          erewrite domain_distr,in_app_iff in H5;
          destruct H5 as [ABS1 |ABS2]; try contradiction.
        eapply in_domain_in_g in ABS2 as (ff&tt&ABS2).
        assert (~In (b1, b2, ff, tt) (removeEntry (b1, b2) g0)).
        eapply no_dup_not_in_removeEntry...
        contradiction.
         right. 
         eapply removeEntry_in...
         eapply in_app_iff in H5 as [APP1 | APP2];
           eapply in_app_iff...
         
       
         
         erewrite <-APPIFF in IN; try assumption.
         inv IN...
        destruct x,p.
         assert (DIFFx: p <> (b1,b2)).
         introv ABS; subst.
         assert (~In (b1, b2, f, p0)
         (removeEntry (b1, b2)
            (newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0)) ++
               g0))).
         eauto.
         contradiction.
        eapply in_removeEntry in H5 as K;
          eapply in_app_iff in K as [K1 | K2];
          right;
        eapply removeEntry_in; try assumption.
        eapply in_app_iff; left...
        eapply in_app_iff; repeat right.
        eapply removeEntry_in...

        eauto.

        (* typeCheck (ne3 ++ (b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) pfk3 p3 *)
        assert (nd_pfne3g3: NoDup (domain (ne3 ++ (b1, b2, f3, tb3) :: removeEntry (b1, b2) g3))).
        erewrite domain_distr. eapply distr_no_dup.
        subst; eapply newEntries_no_dup...
        eapply wf_rewrite,prop27,incl_incl2.
        eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
        eauto.
        eapply incl_tran with (m := secLabs p1)...
        assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        eapply incl_iff with (m1 := domain g0);
          try eassumption.
        
        intros; eapply split_domain_m...
        eauto.
        subst; erewrite disjoint_commute; eapply disjoint_iff with (l1 := domain g3). eapply new_entries_disjoint.
        unfold sl_pos, pos in *; intros.
        specialize SLP with x1 x2;
          unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL; specialize INCL with (x1,x2); intuition.
        
        assert (MAX: max(domain g1) >= max (secLabs q)).
        eapply incl_preserves_max, incl_tran with (m := secLabs p1)... assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        eapply incl_iff with (m1 := domain g0)...
        erewrite split_max with (pf := pf1). lia.
        eapply split_comm...
        eapply in_removeEntry_cons_iff,in_g_in_domain...
        eapply no_dup_isMap in nd_pfne3g3 as pfne3g3.
        
        
        eapply typeCheck_impl with (pf1 := pfne3g3).
        eauto. eauto.
        eapply typeCheck_weak2.
        erewrite <-domain_distr...
        eapply typeCheck_impl with (pf1 := pf3),in_removeEntry_cons_iff_0...
        (* cons ne3 ?pfk *)
        assert (INVNE: forall c1 c2 ff tt,
                   In (c1, c2, ff, tt) ne3 ->
                   In (c1, c2 - max (domain g3)) (secLabs q) /\ In (c1, c2 - max (domain g3), ff, tt) g3).
        intros.
        eapply inverse_newEntries.
        
        eauto.
        (* sl_pos rp *)
                 eapply sl_pos_par_l in SLP;
                   unfold sl_pos in SLP;
                   unfold sl_pos.
                 eapply incl_pos with (l2 :=(secLabs p1))...
        (* incl (secLabs rp) (domain g3) *)
        eapply incl_tran with (m := secLabs p1).
        assumption.
        eapply incl_iff with (m1 := domain g0).
        eapply typeCheck_no_dup with (pf := pf0)...
        intros. eapply split_domain_m... 
        (*In (c1, c2, ff, tt)
    (newEntries g3
       (map (fun x : name * name => (fst x, snd x + max (domain g3))) (secLabs rp))
       (max (domain g3)))*)
        subst. erewrite <-identif_seclabs_of_dep_relabel...
        eapply cons_char.
        destruct ne3. left...
        right. intros.
        specialize INVNE with c1 c2 ff tt.
        apply INVNE in H; clear INVNE.
        destruct H as [INSL IN3'].
        remember (c2 - max (domain g3)) as c''.
        assert (IN2: exists t, In (c1, c'',hid, t) g0).
        eapply typeCheck_hid...
        destruct IN2 as [tt0 IN2].
        assert (ff = ill).
        assert (IN1: In (c1, c'') (secLabs p1)).
        eapply INCL...
        assert (flagOf g3 (c1, c'') ill).
        eapply finv_hid_r,split_comm...
        eapply flag_of_map with (g := g3)...
        subst ff.
        assert (F1': flagOf g1 (c1, c'')  hid).
        eapply fsub_hid... 
        inversion F1'. subst g4 n f.
        eapply typeCheck_ill with (p := p3)...
        

        subst ne3;
          rewrite identif_seclabs_of_dep_relabel in *;
          eapply Peirce; intros ABS;
          eapply not_disjoint in ABS as ([x1 x2] &ABS1 &ABS2);
          eapply in_bv_lt_max with (pf := pf3) in ABS1;
          eapply in_domain_in_g in ABS2 as (ff &tt &ABS2);
          eapply newEntries_gte_max in ABS2;
          try lia;
          try eassumption.
        

      (*   forall x : name * name * flag * piType,
  In x (ne3 ++ (b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) <->
  In x
    ((b1, b2, f3, tb3)
       :: removeEntry (b1, b2) (ne3 ++ (b1, b2, vis, tb3) :: removeEntry (b1, b2) g3)) *)
    rewrite Heqne3.
        specialize in_app_removeEntry_iff
          with (b1 := b1) (b2 := b2) (f := f3) (t := tb3)
               (w := ne3) (g := g3) as APPIFF.
        assert (ND3: NoDup (domain (ne3 ++ g3))).
        assert (TC1 := H2).
        eapply typeCheck_no_dup in TC1 as [INCL0 ND1].
        assert (INCL1': incl (secLabs p1) (domain g3)).
        eapply incl_iff; try eassumption.
        intros; eapply split_domain_m...
         subst ne3; try rewrite domain_distr;
          try eapply no_dup_iff; repeat split;
          try eapply disjoint_commute;
           try eapply new_entries_disjoint;
           try eapply sl_pos_repl;
           try eapply incl_preserves_max,incl_tran;
           try eapply newEntries_no_dup;
           try eapply prop27;
           try eapply incl_incl2,incl_tran;
           try eapply replication_no_dup;
           try eassumption.
         assumption.
         assert (NIN3:   ~ In (b1, b2) (domain ne3)).
         rewrite domain_distr in ND3;
           eapply no_dup_iff in ND3 as (ND1 &ND3 &DIS3).
         intros ABS;
        try eapply disjoint_absurd... 
        intros; split; introv IN; try rewrite <-  APPIFF;
          try assumption.
        assert (IN2 := IN).
        rewrite removeEntry_app_shift.
        assert (EQ: removeEntry (b1, b2) ((b1, b2, vis, tb3) :: removeEntry (b1, b2) g3) = removeEntry (b1, b2) g3).
        simpl; try rewrite pairEq_eq_true...
        
        rewrite EQ.
        eapply in_app_iff in IN2 as [APP1 | APP2].
        right. eapply in_app_iff...
        inv APP2...
        repeat right; eapply in_app_iff...
        intros ABS.
        subst ne3...

        inv IN; eapply in_app_iff...
        destruct x,p.
         assert (DIFFx: p <> (b1,b2)).
         introv ABS; subst.
         assert (~In (b1, b2, f, p0)
         (removeEntry (b1, b2)
             (newEntries g3 (secLabs (dep_relabel q (domain g3) nd_pf3)) (max (domain g3)) ++
                (b1, b2, vis, tb3) :: removeEntry (b1, b2) g3))).
         eauto.
         contradiction.
        eapply in_removeEntry,in_app_iff in H
            as [APP1|APP2].
        left...
        inv APP2; try inv H; try contradiction.
        repeat right...

        (**) assert (IH: typeCheck k0 pfk0 p2)... 

           destruct EQK1 as [(EQK1 &EQ2) | (EQK1 &EQ2)].
           subst fb0.
           assert (f1 = hid).
           destruct f1; try tauto; try contradiction.
           assert (ABS2:
                    exists t2 : flag, flagOf  ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1,b2) t2 /\ flag_plus hid t2 vis).
           eapply split_flag_plus with
             (pf1 := pf') (pf2 := pf'') (pf := pf''')...
           destruct ABS2 as (ff2 &_ &FP); try inv FP...
           subst f1.

           destruct NE1EQ as [NE1NIL | REPL1].
           destruct NEEQ as [NENIL | REPL].
        
        assert (nd_pfk3: NoDup (domain ((b1, b2, f3, tb3) :: (removeEntry (b1, b2) g3)))).
        eapply no_dup_cons_removeEntry...
        eapply no_dup_isMap in nd_pfk3 as pfk3.
        
        gen pfk0. subst; simpl in *; rewrite pairEq_eq_true in *. intros.

         assert (FP:
                    exists t2 : flag, flagOf  ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1,b2) t2 /\ flag_plus hid t2 hid).
           eapply split_flag_plus with
             (pf1 := pf') (pf2 := pf'') (pf := pf''')...
           destruct FP as (ff2 &FYP &FP).
           inv FYP.
           assert (EQ: ff2 = f3 /\ t0 = tb3).
           eapply in_isMap...
           destruct EQ; subst ff2.

            assert (TP:
                     exists t2, typeOf  ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1,b2) t2 /\ type_plus tb0 t2 tb1).
             eapply split_type_plus with
             (pf1 := pf') (pf2 := pf'') (pf := pf''')...
           destruct TP as (tt2 &TYP2 &TP).
           assert (EQ: tt2 = tb3).
           eapply type_of_map with (g := (b1, b2, f3, tb3) :: removeEntry (b1, b2) g3)...
           destruct EQ; subst tt2.
           eapply TPar with (pf1 := pfk0) (pf2 := pfk3);
             try assumption.
        eapply tEnv_split_add_fp; try assumption.

        introv ISUN; destruct  ISUN as (ff &tt &ISUN); subst tb1; inv TP; try contradiction.
        assert (EQP: p0=p4 /\ p4 = (pol_cup p0 p4)).
        eapply split_plus_un with (b1 := b1) (b2 := b2)...
        destruct EQP; subst; rewrite <-H4...

        eauto.
        eapply typeCheck_impl with (pf1 := pf3),
        in_removeEntry_cons_iff_0...

        
        (* REPL CASE*)

        assert (ne = ne1).
          destruct REPL as [q [REPL [INCL NEEQ]]].

                   
        assert (ne1 = newEntries g1
                                 (secLabs (dep_relabel q (domain g1) nd_pf1))
                                 (max (domain g1))).
        assert (W0:  incl (secLabs p1) (domain (hid_proj g1))).
        eapply typeCheck_hid_proj_par...
        (*assert (IN0: incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup...
        eapply incl_iff with (m2 := domain g) in IN0.
        unfold incl in *; intros a IN1; specialize IN0 with a;
          eapply IN0 in IN1 as K; eapply in_domain_in_g in K as (ff &tt &K). Search secLabs hid. *)
        assert (W1:  NoDup (secLabs p1)).
        eapply typeCheck_no_dup with (pf := pf0)...
        assert (W2: In (a1, a2, vis, Chan un io t) g1).
        eapply tsub_un with (pf := pf1) in IN0a as INa. inversion INa; subst; clear INa.
        eapply fsub_vis with (pf := pf1) in IN0a as INa. 
        assert (f = vis). eapply flag_of_map with (g := g1)...
        subst...
        eauto.
        eauto.
        assert (W3 :  In (b1, b2) (domain g1)). eapply in_g_in_domain...
        eapply lts_un_tau_action_newEntries_2 with (b1 := b1) (b2 := b2)...
        subst; right;simpl; try rewrite pairEq_eq_true...
        
        
        assert (ne = nil).
        subst; eapply newEntries_nil with (g := g1).
        eauto.
        intros. assert ( In x (domain g0) <-> In x (domain g1)).
        eapply split_domain_l...
        intuition auto.
        assert (MAX: max (domain g0) = max (domain g1)).
        eapply max_same_domain...
        erewrite identif_seclabs_of_dep_relabel,MAX,<-identif_seclabs_of_dep_relabel...
        subst...
        
        subst.
        gen pfk0. subst; simpl in *; rewrite pairEq_eq_true in *. intros.
        
         assert (nd_pfk3: NoDup (domain ((b1, b2, f3, tb3) :: (removeEntry (b1, b2) g3)))).
        eapply no_dup_cons_removeEntry...
        eapply no_dup_isMap in nd_pfk3 as pfk3.
        eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
        subst.
        eapply split_cons_remove_3...
        eauto.
        eapply typeCheck_impl with (pf1 := pf3),in_removeEntry_cons_iff_0...

        destruct NEEQ as [NENIL | REPL].
        assert (ne1 = ne).
        destruct REPL1 as [q [REPL [INCL NEEQ]]].
        assert (ne = newEntries g0
                                 (secLabs (dep_relabel q (domain g0) nd_pf0))
                                 (max (domain g0))).
         assert (W0:  incl (secLabs p1) (domain (hid_proj g0)))...
        
        assert (W1:  NoDup (secLabs p1)).
        eapply typeCheck_no_dup with (pf := pf0)...
        assert (W2: In (a1, a2, vis, Chan un io t) g1).
        eapply tsub_un with (pf := pf1) in IN0a as INa. inversion INa; subst; clear INa.
        eapply fsub_vis with (pf := pf1) in IN0a as INa. 
        assert (f = vis). eapply flag_of_map with (g := g1)...
        subst...
        eauto.
        eauto.
        assert (W3 :  In (b1, b2) (domain g0)). eapply in_g_in_domain...
        eapply lts_un_tau_action_newEntries_2 with (b1 := b1) (b2 := b2)...

        
        assert (ne1 = nil).
        subst ne1. eapply newEntries_nil with (g := g0).
        eauto.
        intros; eapply split_domain_l...
        intuition auto.
        assert (MAX: max (domain g1) = max (domain g0)).
        eapply max_same_domain...
        erewrite identif_seclabs_of_dep_relabel,MAX,<-identif_seclabs_of_dep_relabel, <-H...
        subst...

        subst.

        gen pfk0; simpl in *;
          rewrite pairEq_eq_true in *; intros.
        assert (nd_pfk3: NoDup (domain ((b1, b2, f3, tb3) :: (removeEntry (b1, b2) g3)))).
        eapply no_dup_cons_removeEntry...
        eapply no_dup_isMap in nd_pfk3 as pfk3.
        eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
        subst.
        eapply split_cons_remove_3...
        eauto.
        eapply typeCheck_impl with (pf1 := pf3),in_removeEntry_cons_iff_0...

        (* replicated case *)
        destruct REPL1 as [q1 [REPL1 [INCL1 NEEQ1]]].
        destruct REPL as [q [REPL [INCL NEEQ]]].
        assert (q = q1). eapply replication_unique...
        subst q1.

        remember (newEntries g3 (secLabs (dep_relabel q (domain g3) nd_pf3)) (max (domain g3))) as ne3.
        assert (nd_pfk3: NoDup (domain (ne3 ++ (b1, b2, f3, tb3) :: (removeEntry (b1, b2) g3)))).
        erewrite domain_distr. eapply distr_no_dup.
        subst. eapply newEntries_no_dup.
        eapply wf_rewrite,prop27,incl_incl2.
       eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
       eauto.
       eapply incl_tran with (m := secLabs p1)...
       eapply incl_iff with (m1 := (domain g0)).
       eapply typeCheck_no_dup with (pf := pf0)...
       intros; eapply split_domain_m...
       eauto.
       eapply no_dup_cons_removeEntry...
       assert (DIS : disjoint (domain g3) (domain ne3)).
       subst; eapply new_entries_disjoint.
        unfold sl_pos, pos in *; intros.
        specialize SLP with x1 x2;
          unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL; specialize INCL with (x1,x2); intuition.
         assert (MAX2: max(domain g3) >= max (secLabs q)).
        eapply incl_preserves_max, incl_tran with (m := secLabs p1)... assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        eapply incl_iff with (m1 := domain g0);
          try eassumption.
        intros; eapply split_domain_m...  
        lia.
        assert (NIN: ~In (b1, b2) (domain ne3)).
        intros ABS.
        assert (INB: In (b1, b2) (domain g3)).
        eapply in_g_in_domain...
        eapply disjoint_absurd...  
        eapply disjoint_commute, disjoint_cons_removeEntry...
        apply no_dup_isMap in nd_pfk3 as pfk3.
        rewrite NEEQ,removeEntry_app_shift in EQK0;
          simpl in EQK0; try rewrite pairEq_eq_true in EQK0.
        
        eapply TPar with (pf1 := pfk0) (pf2 := pfk3);
          try assumption.
        subst.
        assert (nd_pfk0': NoDup (domain (newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0)) ++ (b1, b2, hid, tb0) ::  removeEntry (b1, b2) g0))).
        assert (TC1 := H2).
        eapply typeCheck_no_dup in TC1 as [INCL0 ND1];
          try eassumption.
        assert (INCL1': incl (secLabs p1) (domain g3)).
        eapply incl_iff; try eassumption.
        intros; eapply split_domain_m...
        rewrite domain_distr,no_dup_iff; repeat split;
          try eapply newEntries_no_dup;
           try eapply prop27;
           try eapply incl_incl2,incl_tran;
          try eapply replication_no_dup;
          try eapply no_dup_cons_removeEntry;
          try eassumption.
        assert (DIS2 :
                 disjoint
    (domain (newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0))))
    (domain  g0)).
        try eapply disjoint_commute,  new_entries_disjoint;
           try eapply sl_pos_repl;
          try eapply incl_preserves_max,incl_tran;
          try eassumption.
        eapply disjoint_commute,disjoint_iff; try eapply disjoint_commute... 
        
        eapply no_dup_isMap in nd_pfk0' as pfk0'.
        eapply split_comm, split_iff2 with (pf2 := pfk0');
          try assumption.
        eapply split_comm, split_distr.
        eapply split_newEntries...
        eapply split_cons_remove_3...

        (*  forall x : name * name * flag * piType,
  In x
    (newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0)) ++
     (b1, b2, hid, tb0) :: removeEntry (b1, b2) g0) <->
  In x
    ((b1, b2, hid, tb0)
     :: newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0)) ++
        removeEntry (b1, b2) g0) *)
        remember (newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0)))as ne0.
        eapply Permutation_iff,Permutation.Permutation_sym,Permutation.Permutation_middle.
        
        (* typeCheck (ne3 ++ (b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) pfk3 p3 *)
        assert (nd_pfne3g3: NoDup (domain (ne3 ++ g3))).
        erewrite domain_distr. eapply distr_no_dup.
        subst; eapply newEntries_no_dup...
        eapply wf_rewrite,prop27,incl_incl2.
        eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
        eauto.
        eapply incl_tran with (m := secLabs p1)...
        assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        eapply incl_iff with (m1 := domain g0);
          try eassumption.
        intros; eapply split_domain_m...
        eauto.
        subst; erewrite disjoint_commute; eapply new_entries_disjoint.
        unfold sl_pos, pos in *; intros.
        specialize SLP with x1 x2;
          unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL; specialize INCL with (x1,x2); intuition.
        assert (MAX: max(domain g1) >= max (secLabs q)).
        eapply incl_preserves_max, incl_tran with (m := secLabs p1)... assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        eapply incl_iff with (m1 := domain g0)...
        erewrite split_max with (pf := pf1). lia.
        eapply split_comm...
        eapply no_dup_isMap in nd_pfne3g3 as pfne3g3.
        
        
        eapply typeCheck_impl with (pf1 := pfne3g3).
        eauto. eauto.
        eapply typeCheck_weak2.
        erewrite <-domain_distr...
        eauto.
        (* cons ne3 ?pfk *)
        assert (INVNE: forall c1 c2 ff tt,
                   In (c1, c2, ff, tt) ne3 ->
                   In (c1, c2 - max (domain g3)) (secLabs q) /\ In (c1, c2 - max (domain g3), ff, tt) g3).
        intros.
        eapply inverse_newEntries.
        eauto.
        (* sl_pos rp *)
                 eapply sl_pos_par_l in SLP;
                   unfold sl_pos in SLP;
                   unfold sl_pos.
                 eapply incl_pos with (l2 :=(secLabs p1))...
        (* incl (secLabs rp) (domain g3) *)
        eapply incl_tran with (m := secLabs p1).
        assumption.
        eapply incl_iff with (m1 := domain g0).
        eapply typeCheck_no_dup with (pf := pf0)...
        intros. eapply split_domain_m... 
        (*In (c1, c2, ff, tt)
    (newEntries g3
       (map (fun x : name * name => (fst x, snd x + max (domain g3))) (secLabs rp))
       (max (domain g3)))*)
        subst. erewrite <-identif_seclabs_of_dep_relabel...
        eapply cons_char.
        destruct ne3. left...
        right. intros.
        specialize INVNE with c1 c2 ff tt.
        apply INVNE in H; clear INVNE.
        destruct H as [INSL IN3'].
        remember (c2 - max (domain g3)) as c''.
        assert (IN2: exists t, In (c1, c'',hid, t) g0).
        eapply typeCheck_hid...
        destruct IN2 as [tt0 IN2].
        assert (ff = ill).
        assert (IN1: In (c1, c'') (secLabs p1)).
        eapply INCL...
        assert (flagOf g3 (c1, c'') ill).
        eapply finv_hid_r,split_comm...
        eapply flag_of_map with (g := g3)...
        subst ff.
        assert (F1': flagOf g1 (c1, c'')  hid).
        eapply fsub_hid... 
        inversion F1'. subst g4 n f.
        eapply typeCheck_ill with (p := p3)...

        subst ne3;
          rewrite identif_seclabs_of_dep_relabel in *;
          eapply Peirce; intros ABS;
          eapply not_disjoint in ABS as ([x1 x2] &ABS1 &ABS2);
          eapply in_bv_lt_max with (pf := pf3) in ABS1;
          eapply in_domain_in_g in ABS2 as (ff &tt &ABS2);
          eapply newEntries_gte_max in ABS2;
          try lia;
          try eassumption.
        
        eapply in_app_removeEntry_iff_0...

        intros ABS.
        assert (DIS: disjoint (domain
                                 (newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0)))) (domain g0)).
        eapply disjoint_commute, new_entries_disjoint;
          try eassumption.
        eapply sl_pos_par_l in SLP;
          unfold sl_pos in SLP;
          unfold sl_pos.
        eapply incl_pos with (l2 :=(secLabs p1))...
        eapply incl_preserves_max, incl_tran with (m := secLabs p1)... assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        assumption.
        eapply disjoint_absurd...

        (* last disjunction *)
           subst fb0 f1.

           destruct NE1EQ as [NE1NIL | REPL1].
           destruct NEEQ as [NENIL | REPL].
        
        assert (nd_pfk3: NoDup (domain ((b1, b2, f3, tb3) :: (removeEntry (b1, b2) g3)))).
        eapply no_dup_cons_removeEntry...
        eapply no_dup_isMap in nd_pfk3 as pfk3.
        
        gen pfk0. gen pfk1. subst; simpl in *; rewrite pairEq_eq_true in *. intros.

         assert (FP:
                    exists t2 : flag, flagOf  ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1,b2) t2 /\ flag_plus hid t2 hid).
           eapply split_flag_plus with
             (pf1 := pf') (pf2 := pf'') (pf := pf''')...
           destruct FP as (ff2 &FYP &FP).
           inv FYP.
           assert (EQ: ff2 = f3 /\ t0 = tb3).
           eapply in_isMap...
           destruct EQ; subst ff2.

            assert (TP:
                     exists t2, typeOf  ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1,b2) t2 /\ type_plus tb0 t2 tb1).
             eapply split_type_plus with
             (pf1 := pf') (pf2 := pf'') (pf := pf''')...
           destruct TP as (tt2 &TYP2 &TP).
           assert (EQ: tt2 = tb3).
           eapply type_of_map with (g := (b1, b2, f3, tb3) :: removeEntry (b1, b2) g3)...
           destruct EQ; subst tt2.
           eapply TPar with (pf1 := pfk0) (pf2 := pfk3);
             try assumption.
        eapply tEnv_split_add_fp; try assumption.

        introv ISUN; destruct  ISUN as (ff &tt &ISUN); subst tb1; inv TP; try contradiction.
        assert (EQP: p0=p4 /\ p4 = (pol_cup p0 p4)).
        eapply split_plus_un with (b1 := b1) (b2 := b2)...
        destruct EQP; subst; rewrite <-H4...

        eauto.
        eapply typeCheck_impl with (pf1 := pf3),
        in_removeEntry_cons_iff_0...

        
        (* REPL CASE*)

        assert (ne = ne1).
          destruct REPL as [q [REPL [INCL NEEQ]]].

                   
        assert (ne1 = newEntries g1
                                 (secLabs (dep_relabel q (domain g1) nd_pf1))
                                 (max (domain g1))).
        assert (W0:  incl (secLabs p1) (domain (hid_proj g1))).
        eapply typeCheck_hid_proj_par...
        assert (W1:  NoDup (secLabs p1)).
        eapply typeCheck_no_dup with (pf := pf0)...
        assert (W2: In (a1, a2, vis, Chan un io t) g1).
        eapply tsub_un with (pf := pf1) in IN0a as INa. inversion INa; subst; clear INa.
        eapply fsub_vis with (pf := pf1) in IN0a as INa. 
        assert (f = vis). eapply flag_of_map with (g := g1)...
        subst...
        eauto.
        eauto.
        assert (W3 :  In (b1, b2) (domain g1)). eapply in_g_in_domain...
        eapply lts_un_tau_action_newEntries_2 with (b1 := b1) (b2 := b2); try discriminate...

        
        
        assert (ne = nil).
        subst; eapply newEntries_nil with (g := g1).
        eauto.
        intros. assert ( In x (domain g0) <-> In x (domain g1)).
        eapply split_domain_l...
        intuition auto.
        assert (MAX: max (domain g0) = max (domain g1)).
        eapply max_same_domain...
        erewrite identif_seclabs_of_dep_relabel,MAX,<-identif_seclabs_of_dep_relabel...
        subst...
        
        subst.
        gen pfk0 pfk1. subst; simpl in *; rewrite pairEq_eq_true in *. intros.
        
         assert (nd_pfk3: NoDup (domain ((b1, b2, f3, tb3) :: (removeEntry (b1, b2) g3)))).
        eapply no_dup_cons_removeEntry...
        eapply no_dup_isMap in nd_pfk3 as pfk3.
        eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
        subst.
        eapply split_cons_remove_3...
        eauto.
        eapply typeCheck_impl with (pf1 := pf3),in_removeEntry_cons_iff_0...

        destruct NEEQ as [NENIL | REPL].
        assert (ne1 = ne).
        destruct REPL1 as [q [REPL [INCL NEEQ]]].
        assert (ne = newEntries g0
                                 (secLabs (dep_relabel q (domain g0) nd_pf0))
                                 (max (domain g0))).
         assert (W0:  incl (secLabs p1) (domain (hid_proj g0)))...
        
        assert (W1:  NoDup (secLabs p1)).
        eapply typeCheck_no_dup with (pf := pf0)...
        assert (W2: In (a1, a2, vis, Chan un io t) g1).
        eapply tsub_un with (pf := pf1) in IN0a as INa. inversion INa; subst; clear INa.
        eapply fsub_vis with (pf := pf1) in IN0a as INa. 
        assert (f = vis). eapply flag_of_map with (g := g1)...
        subst...
        eauto.
        eauto.
        assert (W3 :  In (b1, b2) (domain g0)). eapply in_g_in_domain...
        eapply lts_un_tau_action_newEntries_2 with (b1 := b1) (b2 := b2); try discriminate...


       
        
        assert (ne1 = nil).
        subst ne1. eapply newEntries_nil with (g := g0).
        eauto.
        intros; eapply split_domain_l...
        intuition auto.
        assert (MAX: max (domain g1) = max (domain g0)).
        eapply max_same_domain...
        erewrite identif_seclabs_of_dep_relabel,MAX,<-identif_seclabs_of_dep_relabel...
        subst...

        subst...

        subst.

        gen pfk0 pfk1; simpl in *;
          rewrite pairEq_eq_true in *; intros.
        assert (nd_pfk3: NoDup (domain ((b1, b2, f3, tb3) :: (removeEntry (b1, b2) g3)))).
        eapply no_dup_cons_removeEntry...
        eapply no_dup_isMap in nd_pfk3 as pfk3.
        eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
        subst.
        eapply split_cons_remove_3...
        eauto.
        eapply typeCheck_impl with (pf1 := pf3),in_removeEntry_cons_iff_0...

        (* replicated case *)
        destruct REPL1 as [q1 [REPL1 [INCL1 NEEQ1]]].
        destruct REPL as [q [REPL [INCL NEEQ]]].
        assert (q = q1). eapply replication_unique...
        subst q1.

        remember (newEntries g3 (secLabs (dep_relabel q (domain g3) nd_pf3)) (max (domain g3))) as ne3.
        assert (nd_pfk3: NoDup (domain (ne3 ++ (b1, b2, f3, tb3) :: (removeEntry (b1, b2) g3)))).
        erewrite domain_distr. eapply distr_no_dup.
        subst. eapply newEntries_no_dup.
        eapply wf_rewrite,prop27,incl_incl2.
       eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
       eauto.
       eapply incl_tran with (m := secLabs p1)...
       eapply incl_iff with (m1 := (domain g0)).
       eapply typeCheck_no_dup with (pf := pf0)...
       intros; eapply split_domain_m...
       eauto.
       eapply no_dup_cons_removeEntry...
       assert (DIS : disjoint (domain g3) (domain ne3)).
       subst; eapply new_entries_disjoint.
        unfold sl_pos, pos in *; intros.
        specialize SLP with x1 x2;
          unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL; specialize INCL with (x1,x2); intuition.
         assert (MAX2: max(domain g3) >= max (secLabs q)).
        eapply incl_preserves_max, incl_tran with (m := secLabs p1)... assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        eapply incl_iff with (m1 := domain g0);
          try eassumption.
        intros; eapply split_domain_m...  
        lia.
        assert (NIN: ~In (b1, b2) (domain ne3)).
        intros ABS.
        assert (INB: In (b1, b2) (domain g3)).
        eapply in_g_in_domain...
        eapply disjoint_absurd...  
        eapply disjoint_commute, disjoint_cons_removeEntry...
        apply no_dup_isMap in nd_pfk3 as pfk3.
        rewrite NEEQ,removeEntry_app_shift in EQK0;
          simpl in EQK0; try rewrite pairEq_eq_true in EQK0.
        
        eapply TPar with (pf1 := pfk0) (pf2 := pfk3);
          try assumption.
        subst.
        assert (nd_pfk0': NoDup (domain (newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0)) ++ (b1, b2, hid, tb0) ::  removeEntry (b1, b2) g0))).
         assert (TC1 := H2).
        eapply typeCheck_no_dup in TC1 as [INCL0 ND1];
          try eassumption.
        assert (INCL1': incl (secLabs p1) (domain g3)).
        eapply incl_iff; try eassumption.
        intros; eapply split_domain_m...
        rewrite domain_distr,no_dup_iff; repeat split;
          try eapply newEntries_no_dup;
           try eapply prop27;
           try eapply incl_incl2,incl_tran;
          try eapply replication_no_dup;
          try eapply no_dup_cons_removeEntry;
          try eassumption.
        assert (DIS2 :
                 disjoint
    (domain (newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0))))
    (domain  g0)).
        try eapply disjoint_commute,  new_entries_disjoint;
           try eapply sl_pos_repl;
          try eapply incl_preserves_max,incl_tran;
          try eassumption.
        eapply disjoint_commute,disjoint_iff; try eapply disjoint_commute... 
        
        eapply no_dup_isMap in nd_pfk0' as pfk0'.
        assert (nd_pfk1': NoDup (domain ((newEntries g1 (secLabs (dep_relabel q (domain g1) nd_pf1)) (max (domain g1))) ++ (b1, b2, hid, tb1) ::  removeEntry (b1, b2) g1))).
         assert (TC1 := H2).
        eapply typeCheck_no_dup in TC1 as [INCL0 ND1];
          try eassumption.
        assert (INCL1': incl (secLabs p1) (domain g3)).
        eapply incl_iff; try eassumption.
        intros; eapply split_domain_m...
        rewrite domain_distr,no_dup_iff; repeat split;
          try eapply newEntries_no_dup;
           try eapply prop27;
           try eapply incl_incl2,incl_tran;
          try eapply replication_no_dup;
          try eapply no_dup_cons_removeEntry;
          try eassumption.
        eapply incl_iff; try eassumption;
          intros; try eapply split_domain_r;
          try eassumption.
        assert (DIS2 :
                 disjoint
    (domain (newEntries g1 (secLabs (dep_relabel q (domain g1) nd_pf1)) (max (domain g1))))
    (domain  g1)).
        try eapply disjoint_commute,  new_entries_disjoint;
           try eapply sl_pos_repl;
          try eapply incl_preserves_max,incl_tran;
          try eassumption;
            eapply incl_iff; try eassumption;
          intros; try eapply split_domain_r;
          try eassumption.
        eapply disjoint_commute,disjoint_iff; try eapply disjoint_commute... 
         eapply no_dup_isMap in nd_pfk1' as pfk1'.
         eapply split_comm, split_iff2 with (pf2 := pfk0');
           try assumption.
         try eapply split_iff with (pf := pfk1');
           try assumption.
        eapply split_comm, split_distr.
        eapply split_newEntries...
        eapply split_cons_remove_3...

        (*  forall x : name * name * flag * piType,
  In x (ne1 ++ (b1, b2, hid, tb1) :: removeEntry (b1, b2) g1) <->
  In x
    ((b1, b2, hid, tb1)
     :: removeEntry (b1, b2) (ne1 ++ (b1, b2, vis, tb1) :: removeEntry (b1, b2) g1)) *)
        remember (newEntries g1 (secLabs (dep_relabel q (domain g1) nd_pf1)) (max (domain g1)))as ne1.
        rewrite removeEntry_app_shift; unfold removeEntry; fold removeEntry;
          try rewrite pairEq_eq_true.
        eapply Permutation_iff,Permutation.Permutation_sym,Permutation.Permutation_middle.
        intros ABS; rewrite domain_distr in nd_pfk1';
          eapply no_dup_iff in nd_pfk1' as (ND1 &ND2&DIS);
          try eapply disjoint_absurd...
        (* forall x : name * name * flag * piType,
  In x
    (newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0)) ++
     (b1, b2, hid, tb0) :: removeEntry (b1, b2) g0) <->
  In x
    ((b1, b2, hid, tb0)
     :: newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0)) ++
        removeEntry (b1, b2) g0)*)
        remember (newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0)))as ne0.
        eapply Permutation_iff,Permutation.Permutation_sym,Permutation.Permutation_middle.
        
        (* typeCheck (ne3 ++ (b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) pfk3 p3 *)
        assert (nd_pfne3g3: NoDup (domain (ne3 ++ g3))).
        erewrite domain_distr. eapply distr_no_dup.
        subst; eapply newEntries_no_dup...
        eapply wf_rewrite,prop27,incl_incl2.
        eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
        eauto.
        eapply incl_tran with (m := secLabs p1)...
        assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        eapply incl_iff with (m1 := domain g0);
          try eassumption.
        intros; eapply split_domain_m...
        eauto.
        subst; erewrite disjoint_commute; eapply new_entries_disjoint.
        unfold sl_pos, pos in *; intros.
        specialize SLP with x1 x2;
          unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL; specialize INCL with (x1,x2); intuition.
        assert (MAX: max(domain g1) >= max (secLabs q)).
        eapply incl_preserves_max, incl_tran with (m := secLabs p1)... assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        eapply incl_iff with (m1 := domain g0)...
        erewrite split_max with (pf := pf1). lia.
        eapply split_comm...
        eapply no_dup_isMap in nd_pfne3g3 as pfne3g3.
        
        
        eapply typeCheck_impl with (pf1 := pfne3g3).
        eauto. eauto.
        eapply typeCheck_weak2.
        erewrite <-domain_distr...
        eauto.
        (* cons ne3 ?pfk *)
        assert (INVNE: forall c1 c2 ff tt,
                   In (c1, c2, ff, tt) ne3 ->
                   In (c1, c2 - max (domain g3)) (secLabs q) /\ In (c1, c2 - max (domain g3), ff, tt) g3).
        intros.
        eapply inverse_newEntries.
        eauto.
        (* sl_pos rp *)
                 eapply sl_pos_par_l in SLP;
                   unfold sl_pos in SLP;
                   unfold sl_pos.
                 eapply incl_pos with (l2 :=(secLabs p1))...
        (* incl (secLabs rp) (domain g3) *)
        eapply incl_tran with (m := secLabs p1).
        assumption.
        eapply incl_iff with (m1 := domain g0).
        eapply typeCheck_no_dup with (pf := pf0)...
        intros. eapply split_domain_m... 
        (*In (c1, c2, ff, tt)
    (newEntries g3
       (map (fun x : name * name => (fst x, snd x + max (domain g3))) (secLabs rp))
       (max (domain g3)))*)
        subst. erewrite <-identif_seclabs_of_dep_relabel...
        eapply cons_char.
        destruct ne3. left...
        right. intros.
        specialize INVNE with c1 c2 ff tt.
        apply INVNE in H; clear INVNE.
        destruct H as [INSL IN3'].
        remember (c2 - max (domain g3)) as c''.
        assert (IN2: exists t, In (c1, c'',hid, t) g0).
        eapply typeCheck_hid...
        destruct IN2 as [tt0 IN2].
        assert (ff = ill).
        assert (IN1: In (c1, c'') (secLabs p1)).
        eapply INCL...
        assert (flagOf g3 (c1, c'') ill).
        eapply finv_hid_r,split_comm...
        eapply flag_of_map with (g := g3)...
        subst ff.
        assert (F1': flagOf g1 (c1, c'')  hid).
        eapply fsub_hid... 
        inversion F1'. subst g4 n f.
        eapply typeCheck_ill with (p := p3)...

        subst ne3;
          rewrite identif_seclabs_of_dep_relabel in *;
          eapply Peirce; intros ABS;
          eapply not_disjoint in ABS as ([x1 x2] &ABS1 &ABS2);
          eapply in_bv_lt_max with (pf := pf3) in ABS1;
          eapply in_domain_in_g in ABS2 as (ff &tt &ABS2);
          eapply newEntries_gte_max in ABS2;
          try lia;
          try eassumption.
        
        eapply in_app_removeEntry_iff_0...

        intros ABS.
        assert (DIS: disjoint (domain
                                 (newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0)))) (domain g0)).
        eapply disjoint_commute, new_entries_disjoint;
          try eassumption.
        eapply sl_pos_par_l in SLP;
          unfold sl_pos in SLP;
          unfold sl_pos.
        eapply incl_pos with (l2 :=(secLabs p1))...
        eapply incl_preserves_max, incl_tran with (m := secLabs p1)... assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        assumption.
        eapply disjoint_absurd...
      
        (**)
          introv PNEQ; rewrite <-pairEq_neq in PNEQ.

          
          destruct EQK1 as [(EQK1 &DIFF1)| (EQK1 &DIFF1)];
            destruct NE1EQ as [NIL1 | REPL1];subst.
          (***) eapply TPar with (g2 := g3) (pf1 := pfk0);
                try eassumption.
              destruct EQK0 as [(EQK0 &DIFF0)| (EQK0 &DIFF0)];
            destruct NEEQ as [NEEQ0 | REPL0]; subst k0.

              subst ne; simpl.
              eapply split_iff with (pf := pf1);
                try eassumption.
              eapply split_comm.
              eapply split_iff2 with (pf2 := pf0);
                try eassumption.
              eapply split_comm...
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.

              destruct REPL0 as (q &REPL0 &INCL0 &NEEQ0).

              assert (ne = nil).
              destruct ne; try tauto.
              destruct fc.
              move LTS1 at bottom.
              simpl in LTS1.
              assert (REM:
                       removeEntry (c1, c2) g1 =
                         removeEntry (c1, c2) (nil ++ (c1, c2, vis, tc):: removeEntry (c1, c2)g1)).
              simpl; rewrite pairEq_eq_true...
              gen nd_pf1; rewrite REM; intros.
              
              eapply lts_un_tau_action_newEntries_1h in LTS1;
                try eassumption.
              assert (EQSL:  secLabs (dep_relabel q (domain g1) nd_pf1) =
                         secLabs (dep_relabel q (domain g0) nd_pf0)).
              repeat rewrite identif_seclabs_of_dep_relabel.
              erewrite max_same_domain...
              rewrite EQSL,LTS1,newEntries_nil_nil in *;
                try discriminate...
              
              assert (TC1 := H2).
              eapply typeCheck_hid_proj in TC1;
                try eapply incl_tran,split_incl_hid_proj...
              eapply typeCheck_no_dup in H2 as (_ &IH)...
              assert (TMP := IN0a);
                eapply tsub_un with (g := g1) in TMP;
                try inv TMP.
              assert (flagOf g1 (a1,a2) vis).
              eapply fsub_vis...
              inv H0.
              assert (f = vis).
              eapply flag_of_map with (g := g1)...
              subst...
              eauto.
              eauto.

              contradiction.

               eapply lts_un_tau_action_newEntries_1 in LTS1;
                try eassumption.
              assert (EQSL:  secLabs (dep_relabel q (domain g1) nd_pf1) =
                         secLabs (dep_relabel q (domain g0) nd_pf0)).
              repeat rewrite identif_seclabs_of_dep_relabel.
              erewrite max_same_domain...
              rewrite EQSL,LTS1,newEntries_nil_nil in *;
                try discriminate...

               assert (TC1 := H2).
              eapply typeCheck_hid_proj in TC1;
                try eapply incl_tran,split_incl_hid_proj...
              eapply typeCheck_no_dup in H2 as (_ &IH)...
              assert (TMP := IN0a);
                eapply tsub_un with (g := g1) in TMP;
                try inv TMP.
              assert (flagOf g1 (a1,a2) vis).
              eapply fsub_vis...
              inv H0.
              assert (f = vis).
              eapply flag_of_map with (g := g1)...
              subst...
              eauto.
              eauto.
              
              subst ne; gen pfk0; simpl; rewrite H in *; simpl; introv.
              try eapply split_iff with (pf := pf1);
                try eassumption.
              eapply split_comm.
              eapply split_iff2 with (pf2 := pf0);
                try eassumption.
              eapply split_comm...
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.

              

              
              subst ne; gen pfk0; simpl; try rewrite pairEq_eq_true; introv.
              eapply split_iff with (pf := pf1); try eassumption.
              eapply split_comm.
              eapply split_iff2 with (pf2 := pf0);
                try eassumption.
              eauto.
              eapply split_comm...
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.

               destruct REPL0 as (q &REPL0 &INCL0 &NEEQ0).

              assert (ne = nil).
              destruct ne; try tauto.

              destruct fc.
              move LTS1 at bottom.
              simpl in LTS1.
              assert (REM:
                       removeEntry (c1, c2) g1 =
                         removeEntry (c1, c2) (nil ++ (c1, c2, vis, tc):: removeEntry (c1, c2)g1)).
              simpl; rewrite pairEq_eq_true...

              gen nd_pf1; rewrite REM; intros.
              
              eapply lts_un_tau_action_newEntries_1h in LTS1;
                try eassumption.

               assert (EQSL:  secLabs (dep_relabel q (domain g1) nd_pf1) =
                         secLabs (dep_relabel q (domain g0) nd_pf0)).
              repeat rewrite identif_seclabs_of_dep_relabel.
              erewrite max_same_domain...
              rewrite EQSL,LTS1,newEntries_nil_nil in *;
                try discriminate...

               assert (TC1 := H2).
              eapply typeCheck_hid_proj in TC1;
                try eapply incl_tran,split_incl_hid_proj...
              eapply typeCheck_no_dup in H2 as (_ &IH)...
              assert (TMP := IN0a);
                eapply tsub_un with (g := g1) in TMP;
                try inv TMP.
              assert (flagOf g1 (a1,a2) vis).
              eapply fsub_vis...
              inv H0.
              assert (f = vis).
              eapply flag_of_map with (g := g1)...
              subst...
              eauto.
              eauto.

              contradiction.

              
              
             
              
              eapply lts_un_tau_action_newEntries_1 in LTS1;
                try eassumption.
              assert (EQSL:  secLabs (dep_relabel q (domain g1) nd_pf1) =
                         secLabs (dep_relabel q (domain g0) nd_pf0)).
              repeat rewrite identif_seclabs_of_dep_relabel.
              erewrite max_same_domain...
              rewrite EQSL,LTS1,newEntries_nil_nil in *;
                try discriminate...

               assert (TC1 := H2).
              eapply typeCheck_hid_proj in TC1;
                try eapply incl_tran,split_incl_hid_proj...
              eapply typeCheck_no_dup in H2 as (_ &IH)...
              assert (TMP := IN0a);
                eapply tsub_un with (g := g1) in TMP;
                try inv TMP.
              assert (flagOf g1 (a1,a2) vis).
              eapply fsub_vis...
              inv H0.
              assert (f = vis).
              eapply flag_of_map with (g := g1)...
              subst...
              eauto.
              eauto.

              subst ne; gen pfk0; simpl; rewrite H in *; simpl;
                try rewrite pairEq_eq_true; introv.
              try eapply split_iff with (pf := pf1);
                try eassumption.
              eapply split_comm.
              eapply split_iff2 with (pf2 := pf0);
                try eassumption.
              eauto.
              eapply split_comm...
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.

              eauto.

              
          (***)
            destruct REPL1 as (q &REPL1 &INCL1 &NEEQ1).
            remember (newEntries g3 (secLabs (dep_relabel q (domain g3) nd_pf3)) (max (domain g3))) as ne3.
            assert
              (nd_pfk2 :
                NoDup(domain (ne3 ++ g3))).
            assert (TC1 := H2).
            eapply typeCheck_no_dup in TC1 as [INCL0 ND1].
            assert (INCL1': incl (secLabs p1) (domain g3)).
            eapply incl_iff; try eassumption.
            intros; eapply split_domain_m...
            subst ne3; try rewrite domain_distr;
              try eapply no_dup_iff; repeat split;
              try eapply disjoint_commute;
              try eapply new_entries_disjoint;
              try eapply sl_pos_repl;
              try eapply incl_preserves_max,incl_tran;
              try eapply newEntries_no_dup;
              try eapply prop27;
              try eapply incl_incl2,incl_tran;
              try eapply replication_no_dup;
              try eassumption.
            assumption.
            assert (ND3 := nd_pfk2).
            assert (NIN3:   ~ In (b1, b2) (domain ne3)).
            rewrite domain_distr in ND3;
              eapply no_dup_iff in ND3 as (ND1 &ND3 &DIS3).
            intros ABS;
              try eapply disjoint_absurd...
            
            eapply no_dup_isMap in nd_pfk2 as pfk2.
            destruct NEEQ as [NIL0 | REPL0].
            eapply TPar with (pf1 := pfk0) (pf2 := pf3);
              try eassumption.

            subst ne.

            assert (ne1 = nil).
            destruct ne1; try tauto.
            destruct EQK0 as [(EQ0 &DIFF0) |(EQ0 &DIFF0)];
              subst k0.
            destruct fb0.

             move LTS0 at bottom.
              simpl in LTS0.
              assert (REM:
                       removeEntry (b1, b2) g0 =
                         removeEntry (b1, b2) (nil ++ (b1, b2, vis, tb0):: removeEntry (b1, b2)g0)).
              simpl; rewrite pairEq_eq_true...

              gen nd_pf0; rewrite REM; intros.
              
              eapply lts_un_tau_action_newEntries_1h in LTS0;
                try eassumption.

               assert (EQSL:  secLabs (dep_relabel q (domain g1) nd_pf1) =
                         secLabs (dep_relabel q (domain g0) nd_pf0)).
              repeat rewrite identif_seclabs_of_dep_relabel.
              erewrite max_same_domain...
              rewrite EQSL,LTS0,newEntries_nil_nil in *;
                try discriminate...

               assert (TC1 := H2).
              eapply typeCheck_hid_proj in TC1...
              eapply typeCheck_no_dup in H2 as (_ &IH)...
              eauto.

              contradiction.

              
              eapply lts_un_tau_action_newEntries_1 in LTS0;
                try eassumption.

               assert (EQSL:  secLabs (dep_relabel q (domain g1) nd_pf1) =
                         secLabs (dep_relabel q (domain g0) nd_pf0)).
              repeat rewrite identif_seclabs_of_dep_relabel.
              erewrite max_same_domain...
              rewrite EQSL,LTS0,newEntries_nil_nil in *;
                try discriminate...

               assert (TC1 := H2).
              eapply typeCheck_hid_proj in TC1...
              eapply typeCheck_no_dup in H2 as (_ &IH)...
              eauto.

              subst fb0.
              move LTS0 at bottom.

            
              try eapply lts_un_tau_action_newEntries_1h in LTS0;
              try eassumption.
            assert (EQSL:  secLabs (dep_relabel q (domain g1) nd_pf1) =
                             secLabs (dep_relabel q (domain g0) nd_pf0)).
            repeat rewrite identif_seclabs_of_dep_relabel.
            erewrite max_same_domain...
            rewrite EQSL,LTS0,newEntries_nil_nil in *;
              try discriminate...
             assert (TC1 := H2).
              eapply typeCheck_hid_proj in TC1...
              eapply typeCheck_no_dup in H2 as (_ &IH)...
              eauto.


              subst.

              
              
                destruct EQK0 as [(EQ0 &DIFF0) |(EQ0 &DIFF0)];
                  subst k0;gen pfk1; try rewrite H; simpl;introv.

                try eapply split_iff with (pf := pf1);
                  try eassumption.
                eauto.
              eapply split_comm.
              eapply split_iff2 with (pf2 := pf0);
                try eassumption.
              eapply split_comm...
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.

              gen pfk0; simpl; rewrite pairEq_eq_true; simpl; introv.
              try eapply split_iff with (pf := pf1); try eassumption.
              eauto.
              eapply split_comm.
              eapply split_iff2 with (pf2 := pf0); try eassumption.
              eauto.
              eapply split_comm...
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.
              eauto.

               destruct REPL0 as (q' &REPL0 &INCL0 &NEEQ0).
               assert (q = q').
               eapply replication_unique...
               subst q'.
               move NEEQ0 at bottom.

        (*typeCheck (ne1 ++ (c1, c2, fc, tc) :: removeEntry (c1, c2) g1) pfk1 (dPar p2 p3)*)
               eapply TPar with (pf1 := pfk0) (pf2 := pfk2).

               (* tEnv_split k0 (ne3 ++ g3) (ne1 ++ (c1, c2, fc, tc) :: removeEntry (c1, c2) g1) pfk0 pfk2
    pfk1*)
               destruct EQK0 as
                 [(K0EQ &NILL) | (KOEQ1 &HID)];
                 subst k0.

               (*tEnv_split (ne ++ (b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0) 
    (ne3 ++ g3) (ne1 ++ (c1, c2, fc, tc) :: removeEntry (c1, c2) g1) pfk0 pfk2 pfk1*)
               
               assert (ND0: NoDup (domain (ne ++ g0))).
               rewrite domain_distr,no_dup_iff; repeat split.
               subst ne; try eapply newEntries_no_dup.
               eapply wf_rewrite,prop27,incl_incl2.
               eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
               eauto.
               eapply incl_tran with (m := secLabs p1)...
               eapply incl_iff with (m1 := (domain g0)).
               eapply typeCheck_no_dup with (pf := pf0)...
               intros; tauto. eauto. eauto.
               subst; eapply disjoint_commute, new_entries_disjoint.
               unfold sl_pos, pos in *; intros.
               specialize SLP with x1 x2;
                 unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL0; specialize INCL0 with (x1,x2); intuition.
               eapply incl_preserves_max, incl_tran with (m := secLabs p1)... 
               eapply typeCheck_no_dup with (pf := pf0)...
               
               
               assert (ND1: NoDup (domain (ne1 ++ g1))).
               rewrite domain_distr,no_dup_iff; repeat split.
               subst ne1; try eapply newEntries_no_dup.
               eapply wf_rewrite,prop27,incl_incl2.
               eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
               eauto.
               eapply incl_tran with (m := secLabs p1)...
               eapply incl_iff with (m1 := (domain g0)).
               eapply typeCheck_no_dup with (pf := pf0)...
               intros; eapply split_domain_r, split_comm...
               eauto. eauto.
               subst; eapply disjoint_commute, new_entries_disjoint.
               unfold sl_pos, pos in *; intros.
               specialize SLP with x1 x2;
                 unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL0; specialize INCL0 with (x1,x2); intuition.
               eapply incl_preserves_max, incl_tran with (m := secLabs p1)...
               assert (INCL2: incl (secLabs p1) (domain g0))...
               eapply typeCheck_no_dup with (pf := pf0)...
               eapply incl_iff...

               assert (TS1 := H1).
               assert (PF0:= ND0).
               eapply no_dup_isMap in PF0; rewrite NEEQ0 in PF0.
               assert (PF1:= ND1).
               eapply no_dup_isMap in PF1;
                 rewrite NEEQ1 in PF1.
               eapply split_newEntries
                 with (p:=q)
                      (nd_pf1 := nd_pf0)
                      (nd_pf2 := nd_pf3)
                      (nd_pf := nd_pf1)
                 in H1 as TSN; try eassumption.
               
               eapply split_comm,split_iff2 with
                 (g2 := ne ++ g0); try eassumption.

               eapply split_comm,split_iff with (g := ne1 ++ g1);
                 try eassumption.

               eapply split_distr.
               subst; eapply split_pf; try eassumption.
               eauto.

               (*forall x : name * name * flag * piType,
  In x (ne1 ++ g1) <-> In x (ne1 ++ (c1, c2, fc, tc) :: removeEntry (c1, c2) g1)*)
              
               eapply Permutation_iff,Permutation.Permutation_app_head,Permutation.NoDup_Permutation; try eapply no_dup_g; try eapply no_dup_cons_removeEntry;
                 try eassumption.
               intros; rewrite <-in_removeEntry_cons_iff_0...
               tauto.

               (* forall x : name * name * flag * piType,
  In x (ne ++ g0) <-> In x (ne ++ (b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0)*)
               
               eapply Permutation_iff,Permutation.Permutation_app_head,Permutation.NoDup_Permutation; try eapply no_dup_g; try eapply no_dup_cons_removeEntry;
                 try eassumption.
               intros; rewrite <-in_removeEntry_cons_iff_0...
               tauto.

               (* tEnv_split
    ((b1, b2, fb0, tb0)
     :: removeEntry (b1, b2) (ne ++ (b1, b2, vis, tb0) :: removeEntry (b1, b2) g0))
    (ne3 ++ g3) (ne1 ++ (c1, c2, fc, tc) :: removeEntry (c1, c2) g1) pfk0 pfk2 pfk1 *)

               
               assert (DIS: disjoint (domain g0) (domain ne) ).
               subst ne; eapply new_entries_disjoint.
                unfold sl_pos, pos in *; intros.
               specialize SLP with x1 x2;
                 unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL0; specialize INCL0 with (x1,x2); intuition.
               eapply incl_preserves_max, incl_tran with (m := secLabs p1)...
               assert (INCL2: incl (secLabs p1) (domain g0))...
               eapply typeCheck_no_dup with (pf := pf0)...

               assert (ND0: NoDup (domain (ne ++ g0))).
               rewrite domain_distr,no_dup_iff; repeat split.
               subst ne; try eapply newEntries_no_dup.
               eapply wf_rewrite,prop27,incl_incl2.
               eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
               eauto.
               eapply incl_tran with (m := secLabs p1)...
               eapply incl_iff with (m1 := (domain g0)).
               eapply typeCheck_no_dup with (pf := pf0)...
               intros; tauto.
               eauto. eauto. eapply disjoint_commute... 

               assert (NIN:
                        In (b1, b2) (domain ne) -> False).
               intros ABS.
               eapply disjoint_absurd...

               
               
               gen pfk0.
               rewrite removeEntry_app_shift;
                 try eassumption;
                 simpl;
                 try rewrite pairEq_eq_true;
                 introv.

               assert (ND0':
                        NoDup (domain (ne ++ (b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0))).
               rewrite domain_distr in *; simpl in *; rewrite no_dup_iff in *; repeat split.
               intuition.
               eapply no_dup_cons_removeEntry; intuition.
               eapply disjoint_commute,disjoint_iff with (l1 := domain g0);
                 try eapply disjoint_commute.
               intuition.
               intros. try rewrite in_removeEntry_cons_iff with (b1 := b1) (b2 := b2) (f := ill) (t := Top);
                 unfold domain; fold domain; try tauto.
               eauto.

               eapply split_comm,split_iff2
                 with (g2 :=
                         ne ++ (b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0); try eassumption.

               simpl;rewrite domain_distr; econstructor;
                 try intros ABS; try eapply in_app_iff in ABS as [ABS1 | ABS2]; try contradiction;
                 try eapply in_domain_in_g in ABS2 as
                   (ff &tt &ABS2);
                 try eapply no_dup_iff.
               assert (~ In (b1, b2, ff, tt) (removeEntry (b1, b2) g0)).
               eapply no_dup_not_in_removeEntry...
               contradiction.
               rewrite domain_distr,no_dup_iff in *; intuition; try eapply disjoint_eqd_removeEntry...

               eapply split_comm.

               (* tEnv_split (ne ++ (b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0) 
    (ne3 ++ g3) (ne1 ++ (c1, c2, fc, tc) :: removeEntry (c1, c2) g1) 
    ?pf213 pfk2 pfk1*)

                assert (ND1: NoDup (domain (ne1 ++ g1))).
               rewrite domain_distr,no_dup_iff; repeat split.
               subst ne1; try eapply newEntries_no_dup.
               eapply wf_rewrite,prop27,incl_incl2.
               eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
               eauto.
               eapply incl_tran with (m := secLabs p1)...
               eapply incl_iff with (m1 := (domain g0)).
               eapply typeCheck_no_dup with (pf := pf0)...
               intros; eapply split_domain_r, split_comm...
               eauto. eauto.
               subst; eapply disjoint_commute, new_entries_disjoint.
               unfold sl_pos, pos in *; intros.
               specialize SLP with x1 x2;
                 unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL0; specialize INCL0 with (x1,x2); intuition.
               eapply incl_preserves_max, incl_tran with (m := secLabs p1)...
               assert (INCL2: incl (secLabs p1) (domain g0))...
               eapply typeCheck_no_dup with (pf := pf0)...
               eapply incl_iff...

               assert (TS1 := H1).
               assert (PF0:= ND0).
               eapply no_dup_isMap in PF0; rewrite NEEQ0 in PF0.
               assert (PF1:= ND1).
               eapply no_dup_isMap in PF1;
                 rewrite NEEQ1 in PF1.
               eapply split_newEntries
                 with (p:=q)
                      (nd_pf1 := nd_pf0)
                      (nd_pf2 := nd_pf3)
                      (nd_pf := nd_pf1)
                 in H1 as TSN; try eassumption.
               
               eapply split_comm,split_iff2 with
                 (g2 := ne ++ g0); try eassumption.

               eapply split_comm,split_iff with (g := ne1 ++ g1);
                 try eassumption.

               eapply split_distr.
               subst; eapply split_pf; try eassumption.
               eauto.

               (*forall x : name * name * flag * piType,
  In x (ne1 ++ g1) <-> In x (ne1 ++ (c1, c2, fc, tc) :: removeEntry (c1, c2) g1)*)
               eapply Permutation_iff,Permutation.Permutation_app_head,Permutation.NoDup_Permutation; try eapply no_dup_g; try eapply no_dup_cons_removeEntry;
                 try eassumption.
               intros; rewrite <-in_removeEntry_cons_iff_0...
               tauto.

               (* forall x : name * name * flag * piType,
  In x (ne ++ g0) <-> In x (ne ++ (b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0)*)
               
               eapply Permutation_iff,Permutation.Permutation_app_head,Permutation.NoDup_Permutation; try eapply no_dup_g; try eapply no_dup_cons_removeEntry;
                 try eassumption.
               intros; rewrite <-in_removeEntry_cons_iff_0...
               tauto.

               (* forall x : name * name * flag * piType,
  In x (ne ++ g0) <-> In x (ne ++ (b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0)*)
               
               eapply Permutation_iff,
                 Permutation.Permutation_sym,
                 Permutation.Permutation_middle.

               (*  typeCheck k0 pfk0 p2 *)
               eapply IHLTS...

               (* typeCheck (ne3 ++ g3) pfk2 p3*)
               eapply typeCheck_weak2;
                 try rewrite domain_distr in *;
                 try eassumption.
               apply Peirce; intros ABS;
                 eapply gcons_abs
                 in ABS
                   as (x1 &x2 &ff &pp &tt &ABS &NEEMPTY).
               assert (INCLH:
                        incl (secLabs q) (domain (hid_proj g0))).
               eapply incl_tran...
              rewrite Heqne3, identif_seclabs_of_dep_relabel
                in ABS;
                try eapply inverse_newEntries
                in ABS
                  as [ABS1 ABS2].
                try eapply INCLH,hid_proj_flagOf in ABS1.
                inv ABS1.
                remember (max (domain g3)) as M.
                assert (FYP: flagOf g3 (x1, x2 - M) ill).
                eapply finv_hid_r;
                  try eapply split_comm;
                  try eassumption.
                inv FYP.
                assert (EQ: ff = ill /\ Chan lin pp tt = t1).
                eapply in_isMap with (g := g3)...
                destruct EQ; subst.
                eapply typeCheck_ill
                  in ABS2
                    as [ABS' | [(t' &ABS'') |
                                 (p' &t' &ABS''')]];
                  subst;
                  try inv ABS'';
                  try discriminate;
                  try contradiction.

                eauto.
                eauto.
                eauto.
                unfold sl_pos, pos in *; intros.
                specialize SLP with x0 x3;
                  unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL0; specialize INCL0 with (x0,x3); intuition.
                eapply incl_tran with (m := secLabs p1)...
                assert (INCL2: incl (secLabs p1) (domain g0))...
                eapply typeCheck_no_dup with (pf := pf0)...
                eapply incl_iff with (m1 := domain g0);
                  try eassumption.
                intros. eapply split_domain_m...

                subst ne3;
                  rewrite identif_seclabs_of_dep_relabel in *;
                  eapply Peirce; intros ABS;
                  eapply not_disjoint in ABS as ([x1 x2] &ABS1 &ABS2);
                  eapply in_bv_lt_max with (pf := pf3) in ABS1;
                  eapply in_domain_in_g in ABS2 as (ff &tt &ABS2);
                  eapply newEntries_gte_max in ABS2;
                  try lia;
                  try eassumption.

          (***) (* typeCheck
    ((c1, c2, hid, tc)
     :: removeEntry (c1, c2) (nil ++ (c1, c2, vis, tc) :: removeEntry (c1, c2) g1)) pfk1
    (dPar p2 p3)  *)
             eapply TPar with (g2 := g3) (pf1 := pfk0);
                try eassumption.
              destruct EQK0 as [(EQK0 &DIFF0)| (EQK0 &DIFF0)];
            destruct NEEQ as [NEEQ0 | REPL0]; subst k0.

              subst ne; simpl.
              eapply split_iff with (pf := pf1);
                try eassumption.
              eapply split_comm.
              eapply split_iff2 with (pf2 := pf0);
                try eassumption.
              eapply split_comm...
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.
              intros; try rewrite in_removeEntry_cons_iff_0...
              rewrite pairEq_eq_true.
              tauto.

              destruct REPL0 as (q &REPL0 &INCL0 &NEEQ0).

              assert (ne = nil).
              destruct ne; try tauto.
              
              eapply lts_un_tau_action_newEntries_1h in LTS1;
                try eassumption.
              assert (EQSL:  secLabs (dep_relabel q (domain g1) nd_pf1) =
                         secLabs (dep_relabel q (domain g0) nd_pf0)).
              repeat rewrite identif_seclabs_of_dep_relabel.
              erewrite max_same_domain...
              rewrite EQSL,LTS1,newEntries_nil_nil in *;
                try discriminate...
              
              assert (TC1 := H2).
              eapply typeCheck_hid_proj in TC1;
                try eapply incl_tran,split_incl_hid_proj...
              eapply typeCheck_no_dup in H2 as (_ &IH)...
              assert (TMP := IN0a);
                eapply tsub_un with (g := g1) in TMP;
                try inv TMP.
              assert (flagOf g1 (a1,a2) vis).
              eapply fsub_vis...
              inv H0.
              assert (f = vis).
              eapply flag_of_map with (g := g1)...
              subst...
              eauto.
              eauto.

            
              
              subst ne; gen pfk0; simpl; rewrite H in *; simpl; introv.
              try eapply split_iff with (pf := pf1);
                try eassumption.
              eapply split_comm.
              eapply split_iff2 with (pf2 := pf0);
                try eassumption.
              eapply split_comm...
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.
              intros; try rewrite in_removeEntry_cons_iff_0...
              rewrite pairEq_eq_true.
              tauto.

              

              
              subst ne; gen pfk0; simpl; try rewrite pairEq_eq_true; introv.
              eapply split_iff with (pf := pf1); try eassumption.
              eapply split_comm.
              eapply split_iff2 with (pf2 := pf0);
                try eassumption.
              eauto.
              eapply split_comm...
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.
              intros; try rewrite in_removeEntry_cons_iff_0...
              try rewrite pairEq_eq_true.
              tauto.

               destruct REPL0 as (q &REPL0 &INCL0 &NEEQ0).

              assert (ne = nil).
              destruct ne; try tauto.

              
              eapply lts_un_tau_action_newEntries_1h in LTS1;
                try eassumption.

               assert (EQSL:  secLabs (dep_relabel q (domain g1) nd_pf1) =
                         secLabs (dep_relabel q (domain g0) nd_pf0)).
              repeat rewrite identif_seclabs_of_dep_relabel.
              erewrite max_same_domain...
              rewrite EQSL,LTS1,newEntries_nil_nil in *;
                try discriminate...

               assert (TC1 := H2).
              eapply typeCheck_hid_proj in TC1;
                try eapply incl_tran,split_incl_hid_proj...
              eapply typeCheck_no_dup in H2 as (_ &IH)...
              assert (TMP := IN0a);
                eapply tsub_un with (g := g1) in TMP;
                try inv TMP.
              assert (flagOf g1 (a1,a2) vis).
              eapply fsub_vis...
              inv H0.
              assert (f = vis).
              eapply flag_of_map with (g := g1)...
              subst...
              eauto.
              eauto.

              subst ne; gen pfk0; simpl; rewrite H in *; simpl;
                try rewrite pairEq_eq_true; introv.
              try eapply split_iff with (pf := pf1);
                try eassumption.
              eapply split_comm.
              eapply split_iff2 with (pf2 := pf0);
                try eassumption.
              eauto.
              eapply split_comm...
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.
              intros; try rewrite in_removeEntry_cons_iff_0...
              try rewrite pairEq_eq_true.
              tauto.

              eauto.

              
          (***)
            destruct REPL1 as (q &REPL1 &INCL1 &NEEQ1).
            remember (newEntries g3 (secLabs (dep_relabel q (domain g3) nd_pf3)) (max (domain g3))) as ne3.
            assert
              (nd_pfk2 :
                NoDup(domain (ne3 ++ g3))).
            assert (TC1 := H2).
            eapply typeCheck_no_dup in TC1 as [INCL0 ND1].
            assert (INCL1': incl (secLabs p1) (domain g3)).
            eapply incl_iff; try eassumption.
            intros; eapply split_domain_m...
            subst ne3; try rewrite domain_distr;
              try eapply no_dup_iff; repeat split;
              try eapply disjoint_commute;
              try eapply new_entries_disjoint;
              try eapply sl_pos_repl;
              try eapply incl_preserves_max,incl_tran;
              try eapply newEntries_no_dup;
              try eapply prop27;
              try eapply incl_incl2,incl_tran;
              try eapply replication_no_dup;
              try eassumption.
            assumption.
            assert (ND3 := nd_pfk2).
            assert (NIN3:   ~ In (b1, b2) (domain ne3)).
            rewrite domain_distr in ND3;
              eapply no_dup_iff in ND3 as (ND1 &ND3 &DIS3).
            intros ABS;
              try eapply disjoint_absurd...
            
            eapply no_dup_isMap in nd_pfk2 as pfk2.
            destruct NEEQ as [NIL0 | REPL0].
            eapply TPar with (pf1 := pfk0) (pf2 := pf3);
              try eassumption.

            subst ne.

            assert (ne1 = nil).
            destruct ne1; try tauto.
            destruct EQK0 as [(EQ0 &DIFF0) |(EQ0 &DIFF0)];
              subst k0.
            destruct fb0.

             move LTS0 at bottom.
              simpl in LTS0.
              assert (REM:
                       removeEntry (b1, b2) g0 =
                         removeEntry (b1, b2) (nil ++ (b1, b2, vis, tb0):: removeEntry (b1, b2)g0)).
              simpl; rewrite pairEq_eq_true...

              gen nd_pf0; rewrite REM; intros.
              
              eapply lts_un_tau_action_newEntries_1h in LTS0;
                try eassumption.

               assert (EQSL:  secLabs (dep_relabel q (domain g1) nd_pf1) =
                         secLabs (dep_relabel q (domain g0) nd_pf0)).
              repeat rewrite identif_seclabs_of_dep_relabel.
              erewrite max_same_domain...
              rewrite EQSL,LTS0,newEntries_nil_nil in *;
                try discriminate...

               assert (TC1 := H2).
              eapply typeCheck_hid_proj in TC1...
              eapply typeCheck_no_dup in H2 as (_ &IH)...
              eauto.

              contradiction.

              
              eapply lts_un_tau_action_newEntries_1 in LTS0;
                try eassumption.

               assert (EQSL:  secLabs (dep_relabel q (domain g1) nd_pf1) =
                         secLabs (dep_relabel q (domain g0) nd_pf0)).
              repeat rewrite identif_seclabs_of_dep_relabel.
              erewrite max_same_domain...
              rewrite EQSL,LTS0,newEntries_nil_nil in *;
                try discriminate...

               assert (TC1 := H2).
              eapply typeCheck_hid_proj in TC1...
              eapply typeCheck_no_dup in H2 as (_ &IH)...
              eauto.

              subst fb0.
              move LTS0 at bottom.

            
              try eapply lts_un_tau_action_newEntries_1h in LTS0;
              try eassumption.
            assert (EQSL:  secLabs (dep_relabel q (domain g1) nd_pf1) =
                             secLabs (dep_relabel q (domain g0) nd_pf0)).
            repeat rewrite identif_seclabs_of_dep_relabel.
            erewrite max_same_domain...
            rewrite EQSL,LTS0,newEntries_nil_nil in *;
              try discriminate...
             assert (TC1 := H2).
              eapply typeCheck_hid_proj in TC1...
              eapply typeCheck_no_dup in H2 as (_ &IH)...
              eauto.


              subst.

              
              
                destruct EQK0 as [(EQ0 &DIFF0) |(EQ0 &DIFF0)];
                  subst k0;gen pfk1; try rewrite H; simpl;introv.

                try eapply split_iff with (pf := pf1);
                  try eassumption.
                try rewrite pairEq_eq_true.
                eauto.
              eapply split_comm.
              eapply split_iff2 with (pf2 := pf0);
                try eassumption.
              eapply split_comm...
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.
              intros; try rewrite in_removeEntry_cons_iff_0...
              try rewrite pairEq_eq_true...
              tauto.

              gen pfk0; simpl; rewrite pairEq_eq_true; simpl; introv.
              try eapply split_iff with (pf := pf1); try eassumption.
              try rewrite pairEq_eq_true... 
              eapply split_comm.
              eapply split_iff2 with (pf2 := pf0); try eassumption.
              eauto.
              eapply split_comm...
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.
              intros; try rewrite in_removeEntry_cons_iff_0...
              try rewrite pairEq_eq_true.
              tauto.
              eauto.

               destruct REPL0 as (q' &REPL0 &INCL0 &NEEQ0).
               assert (q = q').
               eapply replication_unique...
               subst q'.
               move NEEQ0 at bottom.

        (*typeCheck (ne1 ++ (c1, c2, fc, tc) :: removeEntry (c1, c2) g1) pfk1 (dPar p2 p3)*)
               eapply TPar with (pf1 := pfk0) (pf2 := pfk2).

               (* tEnv_split k0 (ne3 ++ g3) (ne1 ++ (c1, c2, fc, tc) :: removeEntry (c1, c2) g1) pfk0 pfk2
    pfk1*)
               destruct EQK0 as
                 [(K0EQ &NILL) | (KOEQ1 &HID)];
                 subst k0.

               (*tEnv_split (ne ++ (b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0) 
    (ne3 ++ g3) (ne1 ++ (c1, c2, fc, tc) :: removeEntry (c1, c2) g1) pfk0 pfk2 pfk1*)
               
               assert (ND0: NoDup (domain (ne ++ g0))).
               rewrite domain_distr,no_dup_iff; repeat split.
               subst ne; try eapply newEntries_no_dup.
               eapply wf_rewrite,prop27,incl_incl2.
               eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
               eauto.
               eapply incl_tran with (m := secLabs p1)...
               eapply incl_iff with (m1 := (domain g0)).
               eapply typeCheck_no_dup with (pf := pf0)...
               intros; tauto. eauto. eauto.
               subst; eapply disjoint_commute, new_entries_disjoint.
               unfold sl_pos, pos in *; intros.
               specialize SLP with x1 x2;
                 unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL0; specialize INCL0 with (x1,x2); intuition.
               eapply incl_preserves_max, incl_tran with (m := secLabs p1)... 
               eapply typeCheck_no_dup with (pf := pf0)...
               
               
               assert (ND1: NoDup (domain (ne1 ++ g1))).
               rewrite domain_distr,no_dup_iff; repeat split.
               subst ne1; try eapply newEntries_no_dup.
               eapply wf_rewrite,prop27,incl_incl2.
               eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
               eauto.
               eapply incl_tran with (m := secLabs p1)...
               eapply incl_iff with (m1 := (domain g0)).
               eapply typeCheck_no_dup with (pf := pf0)...
               intros; eapply split_domain_r, split_comm...
               eauto. eauto.
               subst; eapply disjoint_commute, new_entries_disjoint.
               unfold sl_pos, pos in *; intros.
               specialize SLP with x1 x2;
                 unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL0; specialize INCL0 with (x1,x2); intuition.
               eapply incl_preserves_max, incl_tran with (m := secLabs p1)...
               assert (INCL2: incl (secLabs p1) (domain g0))...
               eapply typeCheck_no_dup with (pf := pf0)...
               eapply incl_iff...

               assert (TS1 := H1).
               assert (PF0:= ND0).
               eapply no_dup_isMap in PF0; rewrite NEEQ0 in PF0.
               assert (PF1:= ND1).
               eapply no_dup_isMap in PF1;
                 rewrite NEEQ1 in PF1.
               eapply split_newEntries
                 with (p:=q)
                      (nd_pf1 := nd_pf0)
                      (nd_pf2 := nd_pf3)
                      (nd_pf := nd_pf1)
                 in H1 as TSN; try eassumption.
               
               eapply split_comm,split_iff2 with
                 (g2 := ne ++ g0); try eassumption.

               eapply split_comm,split_iff with (g := ne1 ++ g1);
                 try eassumption.

               eapply split_distr.
               subst; eapply split_pf; try eassumption.
               eauto.

               (* forall x : name * name * flag * piType,
  In x (ne1 ++ g1) <->
  In x
    ((c1, c2, hid, tc)
     :: removeEntry (c1, c2) (ne1 ++ (c1, c2, vis, tc) :: removeEntry (c1, c2) g1))*)

               rewrite removeEntry_app_shift;
                 unfold removeEntry; fold removeEntry;
                 try rewrite pairEq_eq_true.

               assert (IFF2: forall x, In x ((c1, c2, hid, tc) :: ne1 ++ removeEntry (c1, c2) g1) <->
                                         In x ( ne1 ++ (c1, c2, hid, tc) ::removeEntry (c1, c2) g1)).
               eapply Permutation_iff,Permutation.Permutation_middle.
               intros; rewrite IFF2.
               assert (IFF3:
                        In x (ne1 ++ (c1, c2, hid, tc) :: removeEntry (c1, c2) g1) <-> In x (ne1 ++ g1)).
               rewrite in_app_iff.
               rewrite <-in_removeEntry_cons_iff_0,<-in_app_iff...
               tauto.
               rewrite <-IFF3.
               tauto.

               intros ABS.
               
               assert (DIS: disjoint (domain g1) (domain ne1)).
               subst ne1; eapply new_entries_disjoint;
                 try eapply sl_pos_repl;
                 try eapply sl_pos_par_l;
                 try eassumption.
               eapply incl_preserves_max, incl_tran;
                 try eapply secLabs_of_repl...
               eapply incl_iff with (m1 := domain g0);
                 try eapply typeCheck_no_dup...
               eapply disjoint_absurd...
               
               (* forall x : name * name * flag * piType,
  In x (ne ++ g0) <-> In x (ne ++ (b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0)*)
               
               eapply Permutation_iff,Permutation.Permutation_app_head,Permutation.NoDup_Permutation; try eapply no_dup_g; try eapply no_dup_cons_removeEntry;
                 try eassumption.
               intros; rewrite <-in_removeEntry_cons_iff_0...
               tauto.

               (* tEnv_split
    ((b1, b2, fb0, tb0)
     :: removeEntry (b1, b2) (ne ++ (b1, b2, vis, tb0) :: removeEntry (b1, b2) g0))
    (ne3 ++ g3) (ne1 ++ (c1, c2, fc, tc) :: removeEntry (c1, c2) g1) pfk0 pfk2 pfk1 *)

               
               assert (DIS: disjoint (domain g0) (domain ne) ).
               subst ne; eapply new_entries_disjoint.
                unfold sl_pos, pos in *; intros.
               specialize SLP with x1 x2;
                 unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL0; specialize INCL0 with (x1,x2); intuition.
               eapply incl_preserves_max, incl_tran with (m := secLabs p1)...
               assert (INCL2: incl (secLabs p1) (domain g0))...
               eapply typeCheck_no_dup with (pf := pf0)...

               assert (ND0: NoDup (domain (ne ++ g0))).
               rewrite domain_distr,no_dup_iff; repeat split.
               subst ne; try eapply newEntries_no_dup.
               eapply wf_rewrite,prop27,incl_incl2.
               eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
               eauto.
               eapply incl_tran with (m := secLabs p1)...
               eapply incl_iff with (m1 := (domain g0)).
               eapply typeCheck_no_dup with (pf := pf0)...
               intros; tauto.
               eauto. eauto. eapply disjoint_commute... 

               assert (NIN:
                        In (b1, b2) (domain ne) -> False).
               intros ABS.
               eapply disjoint_absurd...

               
               
               gen pfk0.
               rewrite removeEntry_app_shift;
                 try eassumption;
                 simpl;
                 try rewrite pairEq_eq_true;
                 introv.

               assert (ND0':
                        NoDup (domain (ne ++ (b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0))).
               rewrite domain_distr in *; simpl in *; rewrite no_dup_iff in *; repeat split.
               intuition.
               eapply no_dup_cons_removeEntry; intuition.
               eapply disjoint_commute,disjoint_iff with (l1 := domain g0);
                 try eapply disjoint_commute.
               intuition.
               intros. try rewrite in_removeEntry_cons_iff with (b1 := b1) (b2 := b2) (f := ill) (t := Top);
                 unfold domain; fold domain; try tauto.
               eauto.

               eapply split_comm,split_iff2
                 with (g2 :=
                         ne ++ (b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0); try eassumption.

               simpl;rewrite domain_distr; econstructor;
                 try intros ABS; try eapply in_app_iff in ABS as [ABS1 | ABS2]; try contradiction;
                 try eapply in_domain_in_g in ABS2 as
                   (ff &tt &ABS2);
                 try eapply no_dup_iff.
               assert (~ In (b1, b2, ff, tt) (removeEntry (b1, b2) g0)).
               eapply no_dup_not_in_removeEntry...
               contradiction.
               rewrite domain_distr,no_dup_iff in *; intuition; try eapply disjoint_eqd_removeEntry...

               eapply split_comm.

               (* tEnv_split (ne ++ (b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0) 
    (ne3 ++ g3) (ne1 ++ (c1, c2, fc, tc) :: removeEntry (c1, c2) g1) 
    ?pf213 pfk2 pfk1*)

                assert (ND1: NoDup (domain (ne1 ++ g1))).
               rewrite domain_distr,no_dup_iff; repeat split.
               subst ne1; try eapply newEntries_no_dup.
               eapply wf_rewrite,prop27,incl_incl2.
               eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
               eauto.
               eapply incl_tran with (m := secLabs p1)...
               eapply incl_iff with (m1 := (domain g0)).
               eapply typeCheck_no_dup with (pf := pf0)...
               intros; eapply split_domain_r, split_comm...
               eauto. eauto.
               subst; eapply disjoint_commute, new_entries_disjoint.
               unfold sl_pos, pos in *; intros.
               specialize SLP with x1 x2;
                 unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL0; specialize INCL0 with (x1,x2); intuition.
               eapply incl_preserves_max, incl_tran with (m := secLabs p1)...
               assert (INCL2: incl (secLabs p1) (domain g0))...
               eapply typeCheck_no_dup with (pf := pf0)...
               eapply incl_iff...

               assert (TS1 := H1).
               assert (PF0:= ND0).
               eapply no_dup_isMap in PF0; rewrite NEEQ0 in PF0.
               assert (PF1:= ND1).
               eapply no_dup_isMap in PF1;
                 rewrite NEEQ1 in PF1.
               eapply split_newEntries
                 with (p:=q)
                      (nd_pf1 := nd_pf0)
                      (nd_pf2 := nd_pf3)
                      (nd_pf := nd_pf1)
                 in H1 as TSN; try eassumption.
               
               eapply split_comm,split_iff2 with
                 (g2 := ne ++ g0); try eassumption.

               eapply split_comm,split_iff with (g := ne1 ++ g1);
                 try eassumption.

               eapply split_distr.
               subst; eapply split_pf; try eassumption.
               eauto.

              
               (* forall x : name * name * flag * piType,
  In x (ne1 ++ g1) <->
  In x
    ((c1, c2, hid, tc)
     :: removeEntry (c1, c2) (ne1 ++ (c1, c2, vis, tc) :: removeEntry (c1, c2) g1))*)

               rewrite removeEntry_app_shift;
                 unfold removeEntry; fold removeEntry;
                 try rewrite pairEq_eq_true.

               assert (IFF2: forall x, In x ((c1, c2, hid, tc) :: ne1 ++ removeEntry (c1, c2) g1) <->
                                         In x ( ne1 ++ (c1, c2, hid, tc) ::removeEntry (c1, c2) g1)).
               eapply Permutation_iff,Permutation.Permutation_middle.
               intros; rewrite IFF2.
               assert (IFF3:
                        In x (ne1 ++ (c1, c2, hid, tc) :: removeEntry (c1, c2) g1) <-> In x (ne1 ++ g1)).
               rewrite in_app_iff.
               rewrite <-in_removeEntry_cons_iff_0,<-in_app_iff...
               tauto.
               rewrite <-IFF3.
               tauto.

               intros ABS.
               
               assert (DIS2: disjoint (domain g1) (domain ne1)).
               subst ne1; eapply new_entries_disjoint;
                 try eapply sl_pos_repl;
                 try eapply sl_pos_par_l;
                 try eassumption.
               eapply incl_preserves_max, incl_tran;
                 try eapply secLabs_of_repl...
               eapply incl_iff with (m1 := domain g0);
                 try eapply typeCheck_no_dup...
               eapply disjoint_absurd...

               (* forall x : name * name * flag * piType,
  In x (ne ++ g0) <-> In x (ne ++ (b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0)*)
               
               eapply Permutation_iff,Permutation.Permutation_app_head,Permutation.NoDup_Permutation; try eapply no_dup_g; try eapply no_dup_cons_removeEntry;
                 try eassumption.
               intros; rewrite <-in_removeEntry_cons_iff_0...
               tauto.

               (* forall x : name * name * flag * piType,
  In x (ne ++ g0) <-> In x (ne ++ (b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0)*)
               
               eapply Permutation_iff,
                 Permutation.Permutation_sym,
                 Permutation.Permutation_middle.

               (*  typeCheck k0 pfk0 p2 *)
               eapply IHLTS...

               (* typeCheck (ne3 ++ g3) pfk2 p3*)
               eapply typeCheck_weak2;
                 try rewrite domain_distr in *;
                 try eassumption.
               apply Peirce; intros ABS;
                 eapply gcons_abs
                 in ABS
                   as (x1 &x2 &ff &pp &tt &ABS &NEEMPTY).
               assert (INCLH:
                        incl (secLabs q) (domain (hid_proj g0))).
               eapply incl_tran...
              rewrite Heqne3, identif_seclabs_of_dep_relabel
                in ABS;
                try eapply inverse_newEntries
                in ABS
                  as [ABS1 ABS2].
                try eapply INCLH,hid_proj_flagOf in ABS1.
                inv ABS1.
                remember (max (domain g3)) as M.
                assert (FYP: flagOf g3 (x1, x2 - M) ill).
                eapply finv_hid_r;
                  try eapply split_comm;
                  try eassumption.
                inv FYP.
                assert (EQ: ff = ill /\ Chan lin pp tt = t1).
                eapply in_isMap with (g := g3)...
                destruct EQ; subst.
                eapply typeCheck_ill
                  in ABS2
                    as [ABS' | [(t' &ABS'') |
                                 (p' &t' &ABS''')]];
                  subst;
                  try inv ABS'';
                  try discriminate;
                  try contradiction.

                eauto.
                eauto.
                eauto.
                unfold sl_pos, pos in *; intros.
                specialize SLP with x0 x3;
                  unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL0; specialize INCL0 with (x0,x3); intuition.
                eapply incl_tran with (m := secLabs p1)...
                assert (INCL2: incl (secLabs p1) (domain g0))...
                eapply typeCheck_no_dup with (pf := pf0)...
                eapply incl_iff with (m1 := domain g0);
                  try eassumption.
                intros. eapply split_domain_m...

                subst ne3;
                  rewrite identif_seclabs_of_dep_relabel in *;
                  eapply Peirce; intros ABS;
                  eapply not_disjoint in ABS as ([x1 x2] &ABS1 &ABS2);
                  eapply in_bv_lt_max with (pf := pf3) in ABS1;
                  eapply in_domain_in_g in ABS2 as (ff &tt &ABS2);
                  eapply newEntries_gte_max in ABS2;
                  try lia;
                  try eassumption.

                eauto.
                assert (INCLH: incl (secLabs (dPar p1 p3)) (domain (hid_proj g1))).
                eapply typeCheck_hid_proj...
                simpl in INCLH. eapply incl_app_inv...
                eapply typeCheck_no_dup with (pf := pf0)...
                assert (IN := IN0a).
                eapply tsub_un with (g := g1) in IN0a; try inv IN0a;
                  try eassumption.
                eapply fsub_vis with (g := g1) in IN;
                   try inv IN;
                  try eassumption.
                assert (f = vis).
                eapply flag_of_map with (g := g1)...
                subst...
                eauto.
                eapply typeCheck_hid_proj...
                eapply typeCheck_no_dup with (pf := pf0)...
                assumption.

        (*        
        (**) eapply sl_pos_par_l in SLP...
        (**) (* incl (secLabs p1) (domain (hid_proj g1))*)
        eapply typeCheck_hid_proj_par...
        (**) eapply typeCheck_no_dup with (g := g0)...
        (**) eapply tsub_un with (pf := pf1) in IN0a as INa. inversion INa; subst; clear INa.
        eapply fsub_vis with (pf := pf1) in IN0a as INa. 
        assert (f = vis). eapply flag_of_map with (g := g1)...
        subst...
        eauto.
        eauto.

        (**) eapply sl_pos_par_l in SLP...
        (* incl (secLabs p1) (domain (hid_proj g1))*)
        (**) eapply typeCheck_hid_proj...
        (**) eapply typeCheck_no_dup with (g := g0)...
        (**) eauto.
         *)
           






                




         (**) assert (IH: typeCheck k0 pfk0 p2)...
           (* now same thing when a is hidden. try to cut & paste from l3400 *)


        destruct m. 

        (* m = lin *)
        
        eapply lts_after_tau_linh with (t := t) in LTS0 as EX0.
        destruct EX0 as [b1 [b2 [f0 [tb0 [DIFF [IN0b [NILL EQK0]]]]]]].
        assert (LEM1: exists f1 tb1 f2 tb2,
                   In (b1, b2, f1, tb1) g3 /\ 
                   In (b1, b2, f2, tb2) g1).
        eapply split_sub...
        destruct LEM1 as [f3 [tb3 [f1 [tb1 [IN3b IN1b]]]]].
        inversion LTSPAR; subst.
        
        assert (LTS1 := H8). clear H8.
        eapply lts_after_tau_linh with (t := t) in LTS1 as EX1.
        destruct EX1 as [c1 [c2 [fc [tc [DIFF2 [IN1c [NILL2 EQK1]]]]]]].
        
        assert (pf' : isMap ((b1, b2, f0, tb0) :: removeEntry (b1, b2) g0)).
        eapply isMap_cons_2...
         assert (pf'' : isMap ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3)).
         eapply isMap_cons_2...
         assert (pf''' : isMap ((b1, b2, f1, tb1) :: removeEntry (b1, b2) g1)).
         eapply isMap_cons_2...
         assert (TS': tEnv_split ((b1, b2, f0, tb0) :: removeEntry (b1, b2) g0)
    ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3)
    ((b1, b2, f1, tb1) :: removeEntry (b1, b2) g1)
    pf' pf'' pf''').
         eapply split_cons_remove_3...

         case_eq ( pair_eq (b1, b2) (c1, c2)).
        (* (b1, b2) = (c1, c2) *)
        intros PEQ. rewrite <-pairEq_eq in PEQ; inversion PEQ; subst c1 c2.
        assert (fc = f1 /\ tc = tb1).
        eapply in_isMap with (g := g1)...
        destruct H; subst fc tc.
        assert (nd_pfk3: NoDup (domain ((a1, a2, ill, Chan lin empty t) :: (b1, b2, f3, tb3) :: removeEntry (a1, a2) (removeEntry (b1, b2) g3)))).
        eapply no_dup_cons_removeEntry_app...
        eapply no_dup_isMap in nd_pfk3 as pfk3.

        eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
        revert dependent pfk0. 
        rewrite removeEntry_shift with (b1 := b1).
        intros.
        revert dependent pfk3.
        rewrite removeEntry_shift with (b1 := b1).
        intros.
        revert dependent pfk1.
        subst k1. rewrite removeEntry_shift with (b1 := b1).
        intros.
        eapply tEnv_split_add_fp.
        eapply no_dup_cons_removeEntry...
        eauto.
        eauto.
        intros ABS; eapply not_lin_is_unrestricted in ABS; contradiction.
        eauto.
        all: try assumption.
        (*typeCheck
    ((a1, a2, vis, Chan lin empty t)
     :: (b1, b2, f0, tb0) :: removeEntry (a1, a2) (removeEntry (b1, b2) g0)) pfk0 p2
        eapply IHLTS.
        eapply sl_pos_par_l...
        eauto.
        eauto.
        eauto.*)
        (*typeCheck
    ((a1, a2, vis, Chan ill empty t)
     :: (b1, b2, f3, tb3) :: removeEntry (a1, a2) (removeEntry (b1, b2) g3)) pfk3 p3*)
        eapply typeCheck_impl with (pf1 := pf3).
        eauto.
        eauto.
        eauto.
        eapply in_removeEntry_cons_iff_1.
        eauto.
        (*In (a1, a2, ill, Chan lin empty t) g3*)
        assert (EX:  In (a1, a2, hid, Chan lin io t ) g0 /\
       In (a1, a2, ill, Chan lin empty t ) g3 /\
                       In (a1, a2, hid, Chan lin io t ) g1).
        assert (MIDDLE: In (a1, a2, vis, Chan lin io t) g0 /\
        In (a1, a2, vis, Chan lin empty t) g3 /\ In (a1, a2, vis, Chan lin io t) g1 \/
        In (a1, a2, hid, Chan lin io t) g0 /\
          In (a1, a2, ill, Chan lin empty t) g3 /\ In (a1, a2, hid, Chan lin io t) g1).
        eapply lts_middle...
        destruct MIDDLE as [(ABS1 &_ &_) | OK]...
        assert (vis = hid).
        eapply in_isMap with (g := g0)...
        discriminate.
        

        intuition.
        eauto.


        intros PNEQ. rewrite <-pairEq_neq in PNEQ.
        assert (nd_pfk3: NoDup (domain ((a1, a2, ill, Chan lin empty t) :: (b1, b2, f3, tb3) :: removeEntry (a1, a2) (removeEntry (b1, b2) g3)))).
        eapply no_dup_cons_removeEntry_app...
        eapply no_dup_isMap in nd_pfk3 as pfk3.
        eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
        subst.
       
        subst.
        revert dependent pfk0. 
        rewrite removeEntry_shift with (b1 := b1).
        intros.
        revert dependent pfk3.
        rewrite removeEntry_shift with (b1 := b1).
        intros.
        revert dependent pfk1.
        rewrite removeEntry_shift with (b1 := c1).
        intros.
        (* tEnv_split
    ((a1, a2, vis, Chan lin empty t)
     :: removeEntry (a1, a2) ((b1, b2, f0, tb0) :: removeEntry (b1, b2) g0))
    ((a1, a2, vis, Chan lin empty t)
     :: removeEntry (a1, a2) ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3))
    ((a1, a2, vis, Chan lin empty t)
     :: removeEntry (a1, a2) ((c1, c2, fc, tc) :: removeEntry (c1, c2) g1)) pfk0
    pfk3 pfk1*)
        eapply tEnv_split_add_fp.
        eapply no_dup_cons_removeEntry...
        eauto.
        eauto.
        intros ABS; eapply not_lin_is_unrestricted in ABS; contradiction.
        assert (nd_pfk1' : NoDup (domain
                                    ((b1, b2, f1, tb1) :: removeEntry (b1, b2)((c1, c2, fc, tc) :: removeEntry (c1, c2) g1)))).
        rewrite <-removeEntry_shift with (b1 := c1).
        eapply no_dup_cons_removeEntry_app...
        eauto.
        eapply no_dup_isMap in nd_pfk1' as pfk1'.
        eapply split_iff with (pf := pfk1').
        eauto.
        eauto. 
        (*tEnv_split ((b1, b2, f0, tb0) :: removeEntry (b1, b2) g0)
    ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3)
    ((b1, b2, f1, tb1)
     :: removeEntry (b1, b2) ((c1, c2, fc, tc) :: removeEntry (c1, c2) g1)) 
    ?pf16 ?pf25 pfk1'*)
        destruct f0.
        (* f0 = hid *)
        eapply fsub_hid with (pf := pf1) in IN0b as FY1. 
        inversion FY1; subst. assert (IN1b' := H); clear H.
        eapply fsuper_hid with (pf1 := pf0) (pf2 := pf3) in IN1b' as HSUB.
        destruct HSUB as [[_ FY3] | [ABS _]].
        inversion FY3; subst.  assert (IN3b' := H); clear H.
        assert (f3 = ill). eapply flag_of_map with (g := g3)...
        assert (f1 = hid). eapply flag_of_map with (g := g1)...
        subst.
        eapply split_cons_remove_2. 
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        right. eapply removeEntry_in.
        eauto.
        eauto.
        (*tEnv_split g0 g3 ((c1, c2, fc, tc) :: removeEntry (c1, c2) g1) *)
        eapply split_iff with (pf := pf1)...
        eapply in_removeEntry_cons_iff_0...
        (* ABS *)
        inversion ABS; subst.
        assert (hid = ill). eapply flag_of_map with (g := g0)...
        discriminate.
        eauto.
        eauto.

      (* f0 = ill *)
        contradiction.
      (* f0 = vis *)  
         eapply fsub_vis with (pf := pf1) in IN0b as FY1. 
        inversion FY1; subst. assert (IN1b' := H); clear H.
        eapply fsuper_vis with (pf1 := pf0) (pf2 := pf3) in IN1b' as HSUB.
        destruct HSUB as [_ FY3].
        inversion FY3; subst.  assert (IN3b' := H); clear H.
        assert (f3 = vis). eapply flag_of_map with (g := g3)...
        assert (f1 = vis). eapply flag_of_map with (g := g1)...
        subst.
        eapply split_cons_remove.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        right. eapply removeEntry_in...
        eapply split_iff with (pf := pf1)...
        eapply in_removeEntry_cons_iff_0...
        eauto.
        eauto.
        assert (REV: forall x : name * name * flag * piType,
                   In x ((c1, c2, fc, tc) :: removeEntry (c1, c2) g1) <->
                   In x
    ((b1, b2, f1, tb1)
     :: removeEntry (b1, b2) ((c1, c2, fc, tc) :: removeEntry (c1, c2) g1))).
        eapply in_removeEntry_cons_iff_0.
        eauto.
        right. eapply removeEntry_in...
        intros x. specialize REV with x; repeat intuition. intuition. intuition. intuition.
        (*typeCheck
    ((a1, a2, hid, Chan lin empty t)
     :: (b1, b2, f0, tb0) :: removeEntry (a1, a2) (removeEntry (b1, b2) g0)) pfk0 p2*)
        eapply IHLTS.
        eapply sl_pos_par_l...
        eauto.
        eauto.
        eauto.
        (* typeCheck
    ((a1, a2, ill, Chan lin empty t)
     :: (b1, b2, f3, tb3) :: removeEntry (a1, a2) (removeEntry (b1, b2) g3)) pfk3 p3 *)
        eapply typeCheck_impl with (pf1 := pf3).
        eauto.
        eauto.
        eauto.
        eapply in_removeEntry_cons_iff_1.
        eauto.
         assert (EX:  In (a1, a2, hid, Chan lin io t ) g0 /\
       In (a1, a2, ill, Chan lin empty t ) g3 /\
                        In (a1, a2, hid, Chan lin io t ) g1).

          assert (MIDDLE: In (a1, a2, vis, Chan lin io t) g0 /\
        In (a1, a2, vis, Chan lin empty t) g3 /\ In (a1, a2, vis, Chan lin io t) g1 \/
        In (a1, a2, hid, Chan lin io t) g0 /\
          In (a1, a2, ill, Chan lin empty t) g3 /\ In (a1, a2, hid, Chan lin io t) g1).
        eapply lts_middle...
        destruct MIDDLE as [(ABS1 &_ &_) | OK]...
        assert (vis = hid).
        eapply in_isMap with (g := g0)...
        discriminate.

        intuition.
        eauto.
        eapply tsub_io with (pf := pf1) in IN0a as K.
        inversion K; subst.
        eapply fsub_hid with (pf := pf1) in IN0a as K1.
        assert (f = hid).
        eapply flag_of_map with (g := g1)...
        subst...
        eauto. eauto. 
        
        eapply lts_finite in H14. contradiction.
        eapply lts_finite in H14. contradiction.

        (* m = un *)
        eapply lts_after_tau_unh
          with g0 p1 p2 a1 a2 t k0 nd_pf0 nd_pf0 in LTS0 as EX0.
        destruct EX0 as
          (b1 &b2 &fb0 &tb0 &ne &DIFF &IN0b & EQK0 &NEEQ).
        assert (LEM1: exists f1 tb1 f2 tb2,
                   In (b1, b2, f1, tb1) g3 /\ 
                   In (b1, b2, f2, tb2) g1).
        eapply split_sub...
        destruct LEM1 as [f3 [tb3 [f1 [tb1 [IN3b IN1b]]]]].
        inversion LTSPAR; subst.
        all: try eapply lts_finite in H14; try contradiction.
        
        assert (LTS1 := H8). clear H8.
        eapply lts_after_tau_unh with (t := t) (nd_pf1 := nd_pf1) in LTS1 as EX1. 
      
        destruct EX1 as [c1 [c2 [fc [tc [ne1 [DIFF2 [INc [EQK1 NE1EQ]]]]]]]].
        
        assert (pf' : isMap ((b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0)).
        eapply isMap_cons_2...
         assert (pf'' : isMap ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3)).
         eapply isMap_cons_2...
         assert (pf''' : isMap ((b1, b2, f1, tb1) :: removeEntry (b1, b2) g1)).
         eapply isMap_cons_2...
         assert (TS': tEnv_split ((b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0)
    ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3)
    ((b1, b2, f1, tb1) :: removeEntry (b1, b2) g1)
    pf' pf'' pf''').
         eapply split_cons_remove_3...

        
        

         case_eq ( pair_eq (b1, b2) (c1, c2)).
        (* (b1, b2) = (c1, c2) *)
         intros PEQ. rewrite <-pairEq_eq in PEQ.
          
        inversion PEQ;  subst c1 c2.
        assert (fc = f1 /\ tc = tb1).
        eapply in_isMap with (g := g1)...
        destruct H; subst tc fc.

        move EQK0 at bottom.
        move EQK1 at bottom.
        move NEEQ at bottom.
        move NE1EQ at bottom.
        destruct EQK0 as [[EQK0 NILL]| [EQK0 EQ]].
        (*subst fb0.*)
        destruct EQK1 as [[EQK1 NILL2] | [EQK1 EQ]].
        (*subst f1.*)
        destruct NE1EQ as [NE1NIL | REPL1].
        destruct NEEQ as [NENIL | REPL].
        
        assert (nd_pfk3: NoDup (domain ((b1, b2, f3, tb3) :: (removeEntry (b1, b2) g3)))).
        eapply no_dup_cons_removeEntry...
        eapply no_dup_isMap in nd_pfk3 as pfk3.

        
        (**) eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
        subst.
        eapply split_cons_remove_3...
        eauto.
        eapply typeCheck_impl with (pf1 := pf3),in_removeEntry_cons_iff_0...


        (**)
          assert (ne = ne1).
          destruct REPL as [q [REPL [INCL NEEQ]]].

                   
        assert (ne1 = newEntries g1
                                 (secLabs (dep_relabel q (domain g1) nd_pf1))
                                 (max (domain g1))).
        assert (W0:  incl (secLabs p1) (domain (hid_proj g1))).
        eapply typeCheck_hid_proj_par...
        assert (W1:  NoDup (secLabs p1)).
        eapply typeCheck_no_dup with (pf := pf0)...
        assert (W2: In (a1, a2, hid, Chan un io t) g1).
        eapply tsub_un with (pf := pf1) in IN0a as INa. inversion INa; subst; clear INa.
        eapply fsub_hid with (pf := pf1) in IN0a as INa. 
        assert (f = hid). eapply flag_of_map with (g := g1)...
        subst...
        eauto.
        eauto.
        assert (W3 :  In (b1, b2) (domain g1)). eapply in_g_in_domain...
        destruct f1; subst ne1.
        eapply lts_un_tau_action_newEntries_2h with (b1 := b1) (b2 := b2) (g1 := k1)...
        right;simpl; try rewrite pairEq_eq_true...
        contradiction.
         eapply lts_un_tau_action_newEntries_2h with (b1 := b1) (b2 := b2) (g1 := k1)...
        
        
        assert (ne = nil).
        subst; eapply newEntries_nil with (g := g1).
        eauto.
        intros. assert ( In x (domain g0) <-> In x (domain g1)).
        eapply split_domain_l...
        intuition auto.
        assert (MAX: max (domain g0) = max (domain g1)).
        eapply max_same_domain...
        erewrite identif_seclabs_of_dep_relabel;
        erewrite MAX,<-identif_seclabs_of_dep_relabel...
        subst...
        
        subst.
         assert (nd_pfk3: NoDup (domain ((b1, b2, f3, tb3) :: (removeEntry (b1, b2) g3)))).
        eapply no_dup_cons_removeEntry...
        eapply no_dup_isMap in nd_pfk3 as pfk3.
        eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
        subst.
        eapply split_cons_remove_3...
        eauto.
        eapply typeCheck_impl with (pf1 := pf3),in_removeEntry_cons_iff_0...

      
        (**)
        
        destruct NEEQ as [NENIL | REPL].
        assert (ne1 = ne).
        destruct REPL1 as [q [REPL [INCL NEEQ]]].
        assert (ne = newEntries g0
                                 (secLabs (dep_relabel q (domain g0) nd_pf0))
                                 (max (domain g0))).
         assert (W0:  incl (secLabs p1) (domain (hid_proj g0)))...
         
        assert (W1:  NoDup (secLabs p1)).
        eapply typeCheck_no_dup with (pf := pf0)...
        assert (W2: In (a1, a2, hid, Chan un io t) g1).
        eapply tsub_un with (pf := pf1) in IN0a as INa. inversion INa; subst; clear INa.
        eapply fsub_hid with (pf := pf1) in IN0a as INa. 
        assert (f = hid). eapply flag_of_map with (g := g1)...
        subst...
        eauto.
        eauto.
        assert (W3 :  In (b1, b2) (domain g0)). eapply in_g_in_domain...
        destruct fb0; subst ne.
        eapply lts_un_tau_action_newEntries_2h with (b1 := b1) (b2 := b2)...
        right;simpl; try rewrite pairEq_eq_true...
        contradiction.
         eapply lts_un_tau_action_newEntries_2h with (b1 := b1) (b2 := b2)...
        assert (f1 = fb0).
        destruct f1.
        eapply fsuper_hid with (n := (b1,b2)) in TS'
            as [(OK &_)  | (ABS &_)].
        inverts OK as OK; inverts OK as K;
          try inv K; try tauto.
        assert (~In (b1, b2, hid, t0) (removeEntry (b1, b2) g0)).
        eapply no_dup_not_in_removeEntry...
        contradiction.
        
        inverts ABS as ABS; inverts ABS as K; try inv K;
          try contradiction.
        
        assert (~In (b1, b2, ill, t0) (removeEntry (b1, b2) g0)).
        eapply no_dup_not_in_removeEntry...
        contradiction.
        eauto.
        contradiction.
        eapply fsuper_vis with (n := (b1,b2))  in TS'
            as (OK &_).
          inverts OK as OK; inverts OK as K;
          try inv K; try tauto.
          assert (~In (b1, b2, vis, t0) (removeEntry (b1, b2) g0)).
          eapply no_dup_not_in_removeEntry...
          contradiction.
         eauto.
        assert (ne1 = nil).
        subst ne1. eapply newEntries_nil with (g := g0).
        eauto.
        intros; eapply split_domain_l...
        intuition auto.
        assert (MAX: max (domain g1) = max (domain g0)).
        eapply max_same_domain...
        erewrite identif_seclabs_of_dep_relabel,MAX,<-identif_seclabs_of_dep_relabel, <-H...
        subst...

        subst.
        assert (nd_pfk3: NoDup (domain ((b1, b2, f3, tb3) :: (removeEntry (b1, b2) g3)))).
        eapply no_dup_cons_removeEntry...
        eapply no_dup_isMap in nd_pfk3 as pfk3.
        eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
        subst.
        eapply split_cons_remove_3...
        eauto.
        eapply typeCheck_impl with (pf1 := pf3),in_removeEntry_cons_iff_0...

        (* replicated case *)
        destruct REPL1 as [q1 [REPL1 [INCL1 NEEQ1]]].
        destruct REPL as [q [REPL [INCL NEEQ]]].
        assert (q = q1). eapply replication_unique...
        subst q1.

        remember (newEntries g3 (secLabs (dep_relabel q (domain g3) nd_pf3)) (max (domain g3))) as ne3.
        assert (nd_pfk3: NoDup (domain (ne3 ++ (b1, b2, f3, tb3) :: (removeEntry (b1, b2) g3)))).
        erewrite domain_distr. eapply distr_no_dup.
        subst. eapply newEntries_no_dup.
        eapply wf_rewrite,prop27,incl_incl2.
       eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
       eauto.
       eapply incl_tran with (m := secLabs p1)...
       eapply incl_iff with (m1 := (domain g0)).
       eapply typeCheck_no_dup with (pf := pf0)...
       intros; eapply split_domain_m...
       eauto.
       eapply no_dup_cons_removeEntry...
       assert (DIS : disjoint (domain g3) (domain ne3)).
       subst; eapply new_entries_disjoint.
        unfold sl_pos, pos in *; intros.
        specialize SLP with x1 x2;
          unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL; specialize INCL with (x1,x2); intuition.
         assert (MAX2: max(domain g3) >= max (secLabs q)).
        eapply incl_preserves_max, incl_tran with (m := secLabs p1)... assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        eapply incl_iff with (m1 := domain g0);
          try eassumption.
        intros; eapply split_domain_m...  
        lia.
        assert (NIN: ~In (b1, b2) (domain ne3)).
        intros ABS.
        assert (INB: In (b1, b2) (domain g3)).
        eapply in_g_in_domain...
        eapply disjoint_absurd...  
        eapply disjoint_commute, disjoint_cons_removeEntry...
        apply no_dup_isMap in nd_pfk3 as pfk3.
        eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
        subst.
        eapply split_distr.
        eapply split_newEntries...
        eapply split_cons_remove_3...
        eauto.
        
        (* typeCheck (ne3 ++ (b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) pfk3 p3 *)
        assert (nd_pfne3g3: NoDup (domain (ne3 ++ g3))).
        erewrite domain_distr. eapply distr_no_dup.
        subst; eapply newEntries_no_dup...
        eapply wf_rewrite,prop27,incl_incl2.
        eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
        eauto.
        eapply incl_tran with (m := secLabs p1)...
        assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        eapply incl_iff with (m1 := domain g0); try eassumption.
        intros; eapply split_domain_m...
        eauto.
        subst; erewrite disjoint_commute; eapply new_entries_disjoint.
        unfold sl_pos, pos in *; intros.
        specialize SLP with x1 x2;
          unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL; specialize INCL with (x1,x2); intuition.
        assert (MAX: max(domain g1) >= max (secLabs q)).
        eapply incl_preserves_max, incl_tran with (m := secLabs p1)... assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        eapply incl_iff with (m1 := domain g0)...
        erewrite split_max with (pf := pf1). lia.
        eapply split_comm...
        eapply no_dup_isMap in nd_pfne3g3 as pfne3g3.
        
        
        eapply typeCheck_impl with (pf1 := pfne3g3).
        eauto. eauto.
        eapply typeCheck_weak2.
        erewrite <-domain_distr...
        eauto.
        (* cons ne3 ?pfk *)
        assert (INVNE: forall c1 c2 ff tt,
                   In (c1, c2, ff, tt) ne3 ->
                   In (c1, c2 - max (domain g3)) (secLabs q) /\ In (c1, c2 - max (domain g3), ff, tt) g3).
        intros.
        eapply inverse_newEntries.
        eauto.
        (* sl_pos rp *)
                 eapply sl_pos_par_l in SLP;
                   unfold sl_pos in SLP;
                   unfold sl_pos.
                 eapply incl_pos with (l2 :=(secLabs p1))...
        (* incl (secLabs rp) (domain g3) *)
        eapply incl_tran with (m := secLabs p1).
        assumption.
        eapply incl_iff with (m1 := domain g0).
        eapply typeCheck_no_dup with (pf := pf0)...
        intros. eapply split_domain_m... 
        (*In (c1, c2, ff, tt)
    (newEntries g3
       (map (fun x : name * name => (fst x, snd x + max (domain g3))) (secLabs rp))
       (max (domain g3)))*)
        subst. erewrite <-identif_seclabs_of_dep_relabel...
        eapply cons_char.
        destruct ne3. left...
        right. intros.
        specialize INVNE with c1 c2 ff tt.
        apply INVNE in H; clear INVNE.
        destruct H as [INSL IN3'].
        remember (c2 - max (domain g3)) as c''.
        assert (IN2: exists t, In (c1, c'',hid, t) g0).
        eapply typeCheck_hid...
        destruct IN2 as [tt0 IN2].
        assert (ff = ill).
        assert (IN1: In (c1, c'') (secLabs p1)).
        eapply INCL...
        assert (flagOf g3 (c1, c'') ill).
        eapply finv_hid_r,split_comm...
        eapply flag_of_map with (g := g3)...
        subst ff.
        assert (F1': flagOf g1 (c1, c'')  hid).
        eapply fsub_hid... 
        inversion F1'. subst g4 n f.
        eapply typeCheck_ill with (p := p3)...

        subst ne3;
          rewrite identif_seclabs_of_dep_relabel in *;
          eapply Peirce; intros ABS;
          eapply not_disjoint in ABS as ([x1 x2] &ABS1 &ABS2);
          eapply in_bv_lt_max with (pf := pf3) in ABS1;
          eapply in_domain_in_g in ABS2 as (ff &tt &ABS2);
          eapply newEntries_gte_max in ABS2;
          try lia;
          try eassumption.
        
        eapply in_app_removeEntry_iff_0...
        

       
        (* uclose *)
        (**) subst f1.
           
        assert (fb0 = hid).
        eapply fsuper_hid with (n := (b1,b2))in TS' as [(OK &_) | (ABS &_)].
        inverts OK as OK; inv OK. try inv H;try contradiction; try tauto.
        assert (~In (b1, b2, hid, t0) (removeEntry (b1, b2) g0)).
        eapply no_dup_not_in_removeEntry...
        contradiction.
        inverts ABS as OK; inv OK. inv H; try contradiction; try tauto.
        assert (~In (b1, b2, ill, t0) (removeEntry (b1, b2) g0)).
        eapply no_dup_not_in_removeEntry...
        contradiction.
        eauto.
        subst fb0.
       
        
        destruct NE1EQ as [NE1NIL | REPL1].
        destruct NEEQ as [NENIL | REPL].
        
        
        assert (nd_pfk3: NoDup (domain ((b1, b2, f3, tb3) :: (removeEntry (b1, b2) ((b1, b2, vis, tb3) ::removeEntry (b1, b2)g3))))).
        eapply no_dup_cons_removeEntry,no_dup_cons_removeEntry...
        eapply no_dup_isMap in nd_pfk3 as pfk3.

        simpl in pfk3; rewrite pairEq_eq_true in pfk3.
        gen pfk1. rewrite EQK1,   NE1NIL; simpl;
          rewrite pairEq_eq_true; intros.
        
        eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
        subst.
        assert ( NoDup (domain (nil ++ (b1, b2, vis, tb1) :: removeEntry (b1, b2) g1))).
        eapply no_dup_cons_removeEntry...
        
       
        assert (TB3: exists tb3', typeOf  ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1, b2) tb3' /\ type_plus tb0 tb3' tb1).
        eapply split_type_plus with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
        destruct TB3 as (tb3' & TB3 & TP3).
        assert (tb3' = tb3).
        inversion TB3; inversion H0. inversion H7...
        assert (~In (b1, b2, f, tb3') (removeEntry (b1, b2) g3)). eapply no_dup_not_in_removeEntry...
        contradiction.
        subst tb3'.
         assert (FB3:  exists f3' : flag, flagOf  ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1, b2) f3' /\ flag_plus hid f3' hid).
         eapply split_flag_plus with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
         destruct FB3 as (f3' &FYP3 & FP3).
         assert (f3 = f3').
          inversion FYP3; inversion H0. inversion H7...
        assert (~In (b1, b2, f3', t0) (removeEntry (b1, b2) g3)). eapply no_dup_not_in_removeEntry...
        contradiction.
         subst f3'.
         assert (is_unrestricted tb1 -> tb0 = tb3 /\ tb3 = tb1).
         intros ISUN. destruct ISUN as (q &tt &ISUN).
         subst tb1.
         assert (EX0: exists p1 : pol, typeOf ((b1, b2, hid, tb0) :: removeEntry (b1, b2) g0) (b1, b2) (Chan un p1 tt)).
         eapply tsuper_payload with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
         assert (EX3:  exists p2 : pol, typeOf ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1, b2) (Chan un p2 tt)).
         eapply tsuper_payload_r with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
         destruct EX0 as (pp0 & TB0).
         destruct EX3 as (pp3 & TB3').
         assert (tb0 = Chan un pp0 tt).
         eapply type_of_map with (g := ((b1, b2, hid, tb0) :: removeEntry (b1, b2) g0))...
         assert (tb3 = Chan un pp3 tt).
         eapply type_of_map with (g := ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3))...
         subst tb0 tb3.
         assert (pp0 = pp3 /\ pp3 = q).
         eapply split_plus_un...
         destruct H0; subst pp0 pp3...

         simpl.
         eapply tEnv_split_add_fp... 
         eauto.
        eapply typeCheck_impl with (pf1 := pf3),in_removeEntry_cons_iff_0...

        assert (ne = ne1).
        destruct REPL as [q [REPL [INCL NEEQ]]].
        assert (ne1 = newEntries g1
                                 (secLabs (dep_relabel q (domain g1) nd_pf1))
                                 (max (domain g1))).
        assert (W0:  incl (secLabs p1) (domain (hid_proj g1))).
        eapply typeCheck_hid_proj_par...
        assert (W1:  NoDup (secLabs p1)).
        eapply typeCheck_no_dup with (pf := pf0)...
        assert (W2: In (a1, a2, hid, Chan un io t) g1).
        eapply tsub_un with (pf := pf1) in IN0a as INa. inversion INa; subst; clear INa.
        eapply fsub_hid with (pf := pf1) in IN0a as INa. 
        assert (f = hid). eapply flag_of_map with (g := g1)...
        subst...
        eauto.
        eauto.
        assert (W3 :  In (b1, b2) (domain g1)). eapply in_g_in_domain...
        eapply lts_un_tau_action_newEntries_2h with (b1 := b1) (b2 := b2)...
        assert (ne = nil).
        subst; eapply newEntries_nil with (g := g1).
        eauto.
        intros. assert ( In x (domain g0) <-> In x (domain g1)).
        eapply split_domain_l...
        intuition auto.
        assert (MAX: max (domain g0) = max (domain g1)).
        eapply max_same_domain...
        erewrite identif_seclabs_of_dep_relabel,MAX,<-identif_seclabs_of_dep_relabel...
        subst...
        
        
        subst.

        assert (nd_pfk3: NoDup (domain ((b1, b2, f3, tb3) :: (removeEntry (b1, b2) ((b1, b2, vis, tb3) ::removeEntry (b1, b2)g3))))).
        eapply no_dup_cons_removeEntry,no_dup_cons_removeEntry...
        eapply no_dup_isMap in nd_pfk3 as pfk3.

         simpl in pfk3; rewrite pairEq_eq_true in pfk3.
        gen pfk1; simpl;
          rewrite pairEq_eq_true; intros.

        eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
        simpl.
        subst.
        assert ( NoDup (domain (nil ++ (b1, b2, vis, tb1) :: removeEntry (b1, b2) g1))).
        eapply no_dup_cons_removeEntry...
        assert (TB3: exists tb3', typeOf  ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1, b2) tb3' /\ type_plus tb0 tb3' tb1).
        eapply split_type_plus with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
        destruct TB3 as (tb3' & TB3 & TP3).
        assert (tb3' = tb3).
        inversion TB3; inversion H0. inversion H7...
        assert (~In (b1, b2, f, tb3') (removeEntry (b1, b2) g3)). eapply no_dup_not_in_removeEntry...
        contradiction.
        subst tb3'.
         assert (FB3:  exists f3' : flag, flagOf  ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1, b2) f3' /\ flag_plus hid f3' hid).
         eapply split_flag_plus with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
         destruct FB3 as (f3' &FYP3 & FP3).
         assert (f3 = f3').
          inversion FYP3; inversion H0. inversion H7...
        assert (~In (b1, b2, f3', t0) (removeEntry (b1, b2) g3)). eapply no_dup_not_in_removeEntry...
        contradiction.
         subst f3'.
         assert (is_unrestricted tb1 -> tb0 = tb3 /\ tb3 = tb1).
         intros ISUN. destruct ISUN as (q &tt &ISUN).
         subst tb1.
         assert (EX0: exists p1 : pol, typeOf ((b1, b2, hid, tb0) :: removeEntry (b1, b2) g0) (b1, b2) (Chan un p1 tt)).
         eapply tsuper_payload with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
         assert (EX3:  exists p2 : pol, typeOf ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1, b2) (Chan un p2 tt)).
         eapply tsuper_payload_r with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
         destruct EX0 as (pp0 & TB0).
         destruct EX3 as (pp3 & TB3').
         assert (tb0 = Chan un pp0 tt).
         eapply type_of_map with (g := ((b1, b2, hid, tb0) :: removeEntry (b1, b2) g0))...
         assert (tb3 = Chan un pp3 tt).
         eapply type_of_map with (g := ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3))...
         subst tb0 tb3.
         assert (pp0 = pp3 /\ pp3 = q).
         eapply split_plus_un...
         destruct H0; subst pp0 pp3...

         eapply tEnv_split_add_fp... 
         eauto.
        eapply typeCheck_impl with (pf1 := pf3),in_removeEntry_cons_iff_0...

        destruct NEEQ as [NENIL | REPL].
        assert (ne1 = ne).
        destruct REPL1 as [q [REPL [INCL NEEQ]]].
        assert (ne = newEntries g0
                                 (secLabs (dep_relabel q (domain g0) nd_pf0))
                                 (max (domain g0))).
         assert (W0:  incl (secLabs p1) (domain (hid_proj g0)))... 
        (*assert (IN0: incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup...
        eapply incl_iff with (m2 := domain g) in IN0.
        unfold incl in *; intros a IN1; specialize IN0 with a;
          eapply IN0 in IN1 as K; eapply in_domain_in_g in K as (ff &tt &K). Search secLabs hid. *)
        
        assert (W1:  NoDup (secLabs p1)).
        eapply typeCheck_no_dup with (pf := pf0)...
        assert (W3 :  In (b1, b2) (domain g0)). eapply in_g_in_domain...
        subst ne.
        eapply lts_un_tau_action_newEntries_2h with (b1 := b1) (b2 := b2)...
        right;simpl; try rewrite pairEq_eq_true...
        assert (ne1 = nil).
        subst ne1; eapply newEntries_nil with (g := g0).
        eauto.
        intros; eapply split_domain_l...
        intuition auto.
        assert (MAX: max (domain g1) = max (domain g0)).
        eapply max_same_domain...
        erewrite identif_seclabs_of_dep_relabel,MAX,<-identif_seclabs_of_dep_relabel, <-H...
        subst...

        subst.
        assert (nd_pfk3: NoDup (domain ((b1, b2, f3, tb3) :: (removeEntry (b1, b2) ((b1, b2, vis, tb3) ::removeEntry (b1, b2)g3))))).
        eapply no_dup_cons_removeEntry,no_dup_cons_removeEntry...
        eapply no_dup_isMap in nd_pfk3 as pfk3.

         simpl in pfk3; rewrite pairEq_eq_true in pfk3.
        gen pfk1; simpl;
          rewrite pairEq_eq_true; intros.

        eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
        subst.
        assert ( NoDup (domain (nil ++ (b1, b2, vis, tb1) :: removeEntry (b1, b2) g1))).
        eapply no_dup_cons_removeEntry...
        assert (TB3: exists tb3', typeOf  ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1, b2) tb3' /\ type_plus tb0 tb3' tb1).
        eapply split_type_plus with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
        destruct TB3 as (tb3' & TB3 & TP3).
        assert (tb3' = tb3).
        inversion TB3; inversion H0. inversion H7...
        assert (~In (b1, b2, f, tb3') (removeEntry (b1, b2) g3)). eapply no_dup_not_in_removeEntry...
        contradiction.
        subst tb3'.
         assert (FB3:  exists f3' : flag, flagOf  ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1, b2) f3' /\ flag_plus hid f3' hid).
         eapply split_flag_plus with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
         destruct FB3 as (f3' &FYP3 & FP3).
         assert (f3 = f3').
          inversion FYP3; inversion H0. inversion H7...
        assert (~In (b1, b2, f3', t0) (removeEntry (b1, b2) g3)). eapply no_dup_not_in_removeEntry...
        contradiction.
         subst f3'.
         assert (is_unrestricted tb1 -> tb0 = tb3 /\ tb3 = tb1).
         intros ISUN. destruct ISUN as (q &tt &ISUN).
         subst tb1.
         assert (EX0: exists p1 : pol, typeOf ((b1, b2, hid, tb0) :: removeEntry (b1, b2) g0) (b1, b2) (Chan un p1 tt)).
         eapply tsuper_payload with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
         assert (EX3:  exists p2 : pol, typeOf ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1, b2) (Chan un p2 tt)).
         eapply tsuper_payload_r with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
         destruct EX0 as (pp0 & TB0).
         destruct EX3 as (pp3 & TB3').
         assert (tb0 = Chan un pp0 tt).
         eapply type_of_map with (g := ((b1, b2, hid, tb0) :: removeEntry (b1, b2) g0))...
         assert (tb3 = Chan un pp3 tt).
         eapply type_of_map with (g := ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3))...
         subst tb0 tb3.
         assert (pp0 = pp3 /\ pp3 = q).
         eapply split_plus_un...
         destruct H0; subst pp0 pp3...

         eapply tEnv_split_add_fp...

         eauto.
        eapply typeCheck_impl with (pf1 := pf3),in_removeEntry_cons_iff_0...

        (* replicated case *)
        destruct REPL1 as [q1 [REPL1 [INCL1 NEEQ1]]].
        destruct REPL as [q [REPL [INCL NEEQ]]].
        assert (q = q1). eapply replication_unique...
        subst q1.

        
        remember (newEntries g3 (secLabs (dep_relabel q (domain g3) nd_pf3)) (max (domain g3))) as ne3.
        assert (nd_pfk3': NoDup (domain (ne3 ++  ((b1, b2, vis, tb3) ::removeEntry (b1, b2)g3)))).
        erewrite domain_distr. eapply distr_no_dup.
        subst. eapply newEntries_no_dup.
        eapply wf_rewrite,prop27,incl_incl2.
       eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
       eauto.
       eapply incl_tran with (m := secLabs p1)...
       eapply incl_iff with (m1 := (domain g0)).
       eapply typeCheck_no_dup with (pf := pf0)...
       intros; eapply split_domain_m...
       eauto.
       eapply no_dup_cons_removeEntry...
       assert (DIS : disjoint (domain g3) (domain ne3)).
       subst; eapply new_entries_disjoint.
        unfold sl_pos, pos in *; intros.
        specialize SLP with x1 x2;
          unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL; specialize INCL with (x1,x2); intuition.
         assert (MAX2: max(domain g3) >= max (secLabs q)).
        eapply incl_preserves_max, incl_tran with (m := secLabs p1)... assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        eapply incl_iff with (m1 := domain g0);
          try eassumption.
        intros; eapply split_domain_m...  
        lia.
         assert (NIN: ~In (b1, b2) (domain ne3)).
        intros ABS.
        assert (INB: In (b1, b2) (domain g3)).
        eapply in_g_in_domain...
        eapply disjoint_absurd...
        eapply disjoint_commute, disjoint_cons_removeEntry...
        
        assert (nd_pfk3: NoDup (domain ((b1, b2, f3, tb3) :: (removeEntry (b1, b2) (ne3 ++  ((b1, b2, vis, tb3) ::removeEntry (b1, b2)g3)))))).
        eapply no_dup_cons_removeEntry...
        apply no_dup_isMap in nd_pfk3 as pfk3.

        
        eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
        subst.
        
        remember (newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0))) as ne0.
        assert (nd_pfk0': NoDup (domain (ne0 ++  ((b1, b2, vis, tb0) ::removeEntry (b1, b2)g0)))).
        erewrite domain_distr. eapply distr_no_dup.
        subst. eapply newEntries_no_dup.
        eapply wf_rewrite,prop27,incl_incl2.
       eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
       eauto.
       eapply incl_tran with (m := secLabs p1)...
       eapply typeCheck_no_dup with (pf := pf0)...
       eapply no_dup_split_no_dup_l with (pf1 := pf0)(pf2 := pf3) (pf := pf1)...
       eapply no_dup_cons_removeEntry...
       assert (DIS : disjoint (domain g0) (domain ne0)).
       subst; eapply new_entries_disjoint.
        unfold sl_pos, pos in *; intros.
        specialize SLP with x1 x2;
          unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL; specialize INCL with (x1,x2); intuition.
         assert (MAX2: max(domain g0) >= max (secLabs q)).
        eapply incl_preserves_max, incl_tran with (m := secLabs p1)... 
        eapply typeCheck_no_dup with (pf := pf0)...
        lia.
         assert (NIN: ~In (b1, b2) (domain ne0)).
        intros ABS.
        assert (INB: In (b1, b2) (domain g0)).
        eapply in_g_in_domain...
        eapply disjoint_absurd...
        eapply disjoint_commute, disjoint_cons_removeEntry...

        remember (newEntries g1 (secLabs (dep_relabel q (domain g1) nd_pf1)) (max (domain g1))) as ne1.
        assert (nd_pfk1': NoDup (domain (ne1 ++  ((b1, b2, vis, tb1) ::removeEntry (b1, b2)g1)))).
        erewrite domain_distr. eapply distr_no_dup.
        subst ne1; eapply newEntries_no_dup.
        eapply wf_rewrite,prop27,incl_incl2.
       eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
       eauto.
       eapply incl_tran with (m := secLabs p1)...
       eapply incl_iff with (m1 := (domain g0)).
       eapply typeCheck_no_dup with (pf := pf0)...
       intros; eapply split_domain_l...
       eauto.
       eapply no_dup_cons_removeEntry...
       assert (DIS : disjoint (domain g1) (domain ne1)).
       subst ne1; eapply new_entries_disjoint.
        unfold sl_pos, pos in *; intros.
        specialize SLP with x1 x2;
          unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL; specialize INCL with (x1,x2); intuition.
         assert (MAX2: max(domain g1) >= max (secLabs q)).
        eapply incl_preserves_max, incl_tran with (m := secLabs p1)... assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        eapply incl_iff with (m1 := domain g0)...
        lia.
         assert (NIN: ~In (b1, b2) (domain ne1)).
        intros ABS.
        assert (INB: In (b1, b2) (domain g1)).
        eapply in_g_in_domain...
        eapply disjoint_absurd...
        eapply disjoint_commute, disjoint_cons_removeEntry...
        
        assert (TB3: exists tb3', typeOf  ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1, b2) tb3' /\ type_plus tb0 tb3' tb1).
        eapply split_type_plus with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
        destruct TB3 as (tb3' & TB3 & TP3).
        assert (tb3' = tb3).
        inversion TB3. inversion H. inversion H6...
        assert (~In (b1, b2, f, tb3') (removeEntry (b1, b2) g3)). eapply no_dup_not_in_removeEntry...
        contradiction.
        subst tb3'.
         assert (FB3:  exists f3' : flag, flagOf  ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1, b2) f3' /\ flag_plus hid f3' hid).
         eapply split_flag_plus with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
         destruct FB3 as (f3' &FYP3 & FP3).
         assert (f3 = f3').
          inversion FYP3; inversion H. inversion H6...
        assert (~In (b1, b2, f3', t0) (removeEntry (b1, b2) g3)). eapply no_dup_not_in_removeEntry...
        contradiction.
         subst f3'.
         assert (is_unrestricted tb1 -> tb0 = tb3 /\ tb3 = tb1).
         intros ISUN. destruct ISUN as (q1 &tt &ISUN).
         subst tb1.
         assert (EX0: exists p1 : pol, typeOf ((b1, b2, hid, tb0) :: removeEntry (b1, b2) g0) (b1, b2) (Chan un p1 tt)).
         eapply tsuper_payload with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
         assert (EX3:  exists p2 : pol, typeOf ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1, b2) (Chan un p2 tt)).
         eapply tsuper_payload_r with (pf1 := pf') (pf2 := pf'') (pf := pf''')...
         destruct EX0 as (pp0 & TB0).
         destruct EX3 as (pp3 & TB3').
         assert (tb0 = Chan un pp0 tt).
         eapply type_of_map with (g := ((b1, b2, hid, tb0) :: removeEntry (b1, b2) g0))...
         assert (tb3 = Chan un pp3 tt).
         eapply type_of_map with (g := ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3))...
         subst tb0 tb3.
         assert (pp0 = pp3 /\ pp3 = q1).
         eapply split_plus_un...
         destruct H; subst pp0 pp3...

           assert (ND:=nd_pfk0').
         rewrite Heqne0,domain_distr,no_dup_iff in ND;
           destruct ND as (ND1 &ND2 &DIS).
         assert (nd_pfk0'': NoDup
    (domain
       ( (b1, b2, hid, tb0) ::
           removeEntry (b1, b2)(newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0)) ++
           (b1, b2, vis, tb0)::removeEntry (b1, b2) g0)))).
         erewrite removeEntry_app_shift;
           simpl; try rewrite pairEq_eq_true.
       
         econstructor; try intros ABS;
           try rewrite domain_distr in ABS;
           try eapply in_app_iff in ABS as [ABS1|ABS2].
         simpl in DIS; try eapply disjoint_absurd...
         eapply in_domain_in_g in ABS2 as (ff &tt &ABS2).
         assert (NIN: ~In(b1, b2, ff, tt) (removeEntry (b1, b2) g0)).
         eapply no_dup_not_in_removeEntry...
         contradiction.
         rewrite Heqne0 in *.
         erewrite domain_distr in nd_pfk0';
           simpl in nd_pfk0';

           eapply NoDup_remove in nd_pfk0' as [ND _];
           rewrite domain_distr...
         intros ABS.
         eapply disjoint_absurd...
         
         
         
         eapply no_dup_isMap in nd_pfk0'' as pfk0''.
        try rewrite NEEQ1; eapply split_comm,
           split_iff2 with (pf2 := pfk0'');
          try eapply split_comm, tEnv_split_add_fp;
          try eassumption.

        
        eapply split_distr.
        subst ne1; 
        eapply split_newEntries...
        eapply tEnv_split_add_vis...

        (* forall x : name * name * flag * piType,
  In x
    ((b1, b2, hid, tb0)
     :: removeEntry (b1, b2)
          (ne0 ++
           (b1, b2, vis, tb0) :: removeEntry (b1, b2) g0)) <->
  In x (ne0 ++ (b1, b2, hid, tb0) :: removeEntry (b1, b2) g0) *)
        rewrite <-Heqne0.
        specialize in_app_removeEntry_iff
          with (b1 := b1) (b2 := b2) (f := hid) (t := tb0)
               (w := ne0) (g := g0) as APPIFF.
        assert ( NoDup (domain (ne0 ++ g0))).
        subst ne0; try rewrite domain_distr;
          try eapply no_dup_iff; repeat split;
          try eapply disjoint_commute;
          try eapply new_entries_disjoint;try eapply sl_pos_repl;
          try eapply incl_preserves_max,incl_tran,typeCheck_no_dup;
          try eassumption.
        assert (   ~ In (b1, b2) (domain ne0)).
        intros ABS;
          subst ne0;
        try eapply disjoint_absurd...
        intros; split; introv IN; try rewrite <-  APPIFF;
          try assumption.
        assert (IN2 := IN).
        rewrite removeEntry_app_shift in IN;
          simpl in IN; try rewrite pairEq_eq_true in IN;
          intuition; subst...
        destruct x. destruct p .
        assert (DIFFx: p <> (b1,b2)).
        introv ABS; subst.
        eapply in_g_in_domain in H5;
          erewrite domain_distr,in_app_iff in H5;
          destruct H5 as [ABS1 |ABS2]; try contradiction.
        eapply in_domain_in_g in ABS2 as (ff&tt&ABS2).
        assert (~In (b1, b2, ff, tt) (removeEntry (b1, b2) g0)).
        eapply no_dup_not_in_removeEntry...
        contradiction.
         right. 
         eapply removeEntry_in...
         eapply in_app_iff in H5 as [APP1 | APP2];
           eapply in_app_iff...
         
       
         
         erewrite <-APPIFF in IN; try assumption.
         inv IN...
        destruct x,p.
         assert (DIFFx: p <> (b1,b2)).
         introv ABS; subst.
         assert (~In (b1, b2, f, p0)
         (removeEntry (b1, b2)
            (newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0)) ++
               g0))).
         eauto.
         contradiction.
        eapply in_removeEntry in H5 as K;
          eapply in_app_iff in K as [K1 | K2];
          right;
        eapply removeEntry_in; try assumption.
        eapply in_app_iff; left...
        eapply in_app_iff; repeat right.
        eapply removeEntry_in...

        eauto.

        (* typeCheck (ne3 ++ (b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) pfk3 p3 *)
        assert (nd_pfne3g3: NoDup (domain (ne3 ++ (b1, b2, f3, tb3) :: removeEntry (b1, b2) g3))).
        erewrite domain_distr. eapply distr_no_dup.
        subst; eapply newEntries_no_dup...
        eapply wf_rewrite,prop27,incl_incl2.
        eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
        eauto.
        eapply incl_tran with (m := secLabs p1)...
        assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        eapply incl_iff with (m1 := domain g0);
          try eassumption.
        
        intros; eapply split_domain_m...
        eauto.
        subst; erewrite disjoint_commute; eapply disjoint_iff with (l1 := domain g3). eapply new_entries_disjoint.
        unfold sl_pos, pos in *; intros.
        specialize SLP with x1 x2;
          unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL; specialize INCL with (x1,x2); intuition.
        
        assert (MAX: max(domain g1) >= max (secLabs q)).
        eapply incl_preserves_max, incl_tran with (m := secLabs p1)... assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        eapply incl_iff with (m1 := domain g0)...
        erewrite split_max with (pf := pf1). lia.
        eapply split_comm...
        eapply in_removeEntry_cons_iff,in_g_in_domain...
        eapply no_dup_isMap in nd_pfne3g3 as pfne3g3.
        
        
        eapply typeCheck_impl with (pf1 := pfne3g3).
        eauto. eauto.
        eapply typeCheck_weak2.
        erewrite <-domain_distr...
        eapply typeCheck_impl with (pf1 := pf3),in_removeEntry_cons_iff_0...
        (* cons ne3 ?pfk *)
        assert (INVNE: forall c1 c2 ff tt,
                   In (c1, c2, ff, tt) ne3 ->
                   In (c1, c2 - max (domain g3)) (secLabs q) /\ In (c1, c2 - max (domain g3), ff, tt) g3).
        intros.
        eapply inverse_newEntries.
        
        eauto.
        (* sl_pos rp *)
                 eapply sl_pos_par_l in SLP;
                   unfold sl_pos in SLP;
                   unfold sl_pos.
                 eapply incl_pos with (l2 :=(secLabs p1))...
        (* incl (secLabs rp) (domain g3) *)
        eapply incl_tran with (m := secLabs p1).
        assumption.
        eapply incl_iff with (m1 := domain g0).
        eapply typeCheck_no_dup with (pf := pf0)...
        intros. eapply split_domain_m... 
        (*In (c1, c2, ff, tt)
    (newEntries g3
       (map (fun x : name * name => (fst x, snd x + max (domain g3))) (secLabs rp))
       (max (domain g3)))*)
        subst. erewrite <-identif_seclabs_of_dep_relabel...
        eapply cons_char.
        destruct ne3. left...
        right. intros.
        specialize INVNE with c1 c2 ff tt.
        apply INVNE in H; clear INVNE.
        destruct H as [INSL IN3'].
        remember (c2 - max (domain g3)) as c''.
        assert (IN2: exists t, In (c1, c'',hid, t) g0).
        eapply typeCheck_hid...
        destruct IN2 as [tt0 IN2].
        assert (ff = ill).
        assert (IN1: In (c1, c'') (secLabs p1)).
        eapply INCL...
        assert (flagOf g3 (c1, c'') ill).
        eapply finv_hid_r,split_comm...
        eapply flag_of_map with (g := g3)...
        subst ff.
        assert (F1': flagOf g1 (c1, c'')  hid).
        eapply fsub_hid... 
        inversion F1'. subst g4 n f.
        eapply typeCheck_ill with (p := p3)...
        

        subst ne3;
          rewrite identif_seclabs_of_dep_relabel in *;
          eapply Peirce; intros ABS;
          eapply not_disjoint in ABS as ([x1 x2] &ABS1 &ABS2);
          eapply in_bv_lt_max with (pf := pf3) in ABS1;
          eapply in_domain_in_g in ABS2 as (ff &tt &ABS2);
          eapply newEntries_gte_max in ABS2;
          try lia;
          try eassumption.
        

      (*   forall x : name * name * flag * piType,
  In x (ne3 ++ (b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) <->
  In x
    ((b1, b2, f3, tb3)
       :: removeEntry (b1, b2) (ne3 ++ (b1, b2, vis, tb3) :: removeEntry (b1, b2) g3)) *)
    rewrite Heqne3.
        specialize in_app_removeEntry_iff
          with (b1 := b1) (b2 := b2) (f := f3) (t := tb3)
               (w := ne3) (g := g3) as APPIFF.
        assert (ND3: NoDup (domain (ne3 ++ g3))).
        assert (TC1 := H2).
        eapply typeCheck_no_dup in TC1 as [INCL0 ND1].
        assert (INCL1': incl (secLabs p1) (domain g3)).
        eapply incl_iff; try eassumption.
        intros; eapply split_domain_m...
         subst ne3; try rewrite domain_distr;
          try eapply no_dup_iff; repeat split;
          try eapply disjoint_commute;
           try eapply new_entries_disjoint;
           try eapply sl_pos_repl;
           try eapply incl_preserves_max,incl_tran;
           try eapply newEntries_no_dup;
           try eapply prop27;
           try eapply incl_incl2,incl_tran;
           try eapply replication_no_dup;
           try eassumption.
         assumption.
         assert (NIN3:   ~ In (b1, b2) (domain ne3)).
         rewrite domain_distr in ND3;
           eapply no_dup_iff in ND3 as (ND1 &ND3 &DIS3).
         intros ABS;
        try eapply disjoint_absurd... 
        intros; split; introv IN; try rewrite <-  APPIFF;
          try assumption.
        assert (IN2 := IN).
        rewrite removeEntry_app_shift.
        assert (EQ: removeEntry (b1, b2) ((b1, b2, vis, tb3) :: removeEntry (b1, b2) g3) = removeEntry (b1, b2) g3).
        simpl; try rewrite pairEq_eq_true...
        
        rewrite EQ.
        eapply in_app_iff in IN2 as [APP1 | APP2].
        right. eapply in_app_iff...
        inv APP2...
        repeat right; eapply in_app_iff...
        intros ABS.
        subst ne3...

        inv IN; eapply in_app_iff...
        destruct x,p.
         assert (DIFFx: p <> (b1,b2)).
         introv ABS; subst.
         assert (~In (b1, b2, f, p0)
         (removeEntry (b1, b2)
             (newEntries g3 (secLabs (dep_relabel q (domain g3) nd_pf3)) (max (domain g3)) ++
                (b1, b2, vis, tb3) :: removeEntry (b1, b2) g3))).
         eauto.
         contradiction.
        eapply in_removeEntry,in_app_iff in H
            as [APP1|APP2].
        left...
        inv APP2; try inv H; try contradiction.
        repeat right...

        (**) (*assert (IH: typeCheck k0 pfk0 p2)...*) 

           destruct EQK1 as [(EQK1 &EQ2) | (EQK1 &EQ2)].
           subst fb0.
           assert (f1 = hid).
           destruct f1; try tauto; try contradiction.
           assert (ABS2:
                    exists t2 : flag, flagOf  ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1,b2) t2 /\ flag_plus hid t2 vis).
           eapply split_flag_plus with
             (pf1 := pf') (pf2 := pf'') (pf := pf''')...
           destruct ABS2 as (ff2 &_ &FP); try inv FP...
           subst f1.

           destruct NE1EQ as [NE1NIL | REPL1].
           destruct NEEQ as [NENIL | REPL].
        
        assert (nd_pfk3: NoDup (domain ((b1, b2, f3, tb3) :: (removeEntry (b1, b2) g3)))).
        eapply no_dup_cons_removeEntry...
        eapply no_dup_isMap in nd_pfk3 as pfk3.
        
        gen pfk0. subst; simpl in *; rewrite pairEq_eq_true in *. intros.

         assert (FP:
                    exists t2 : flag, flagOf  ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1,b2) t2 /\ flag_plus hid t2 hid).
           eapply split_flag_plus with
             (pf1 := pf') (pf2 := pf'') (pf := pf''')...
           destruct FP as (ff2 &FYP &FP).
           inv FYP.
           assert (EQ: ff2 = f3 /\ t0 = tb3).
           eapply in_isMap...
           destruct EQ; subst ff2.

            assert (TP:
                     exists t2, typeOf  ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1,b2) t2 /\ type_plus tb0 t2 tb1).
             eapply split_type_plus with
             (pf1 := pf') (pf2 := pf'') (pf := pf''')...
           destruct TP as (tt2 &TYP2 &TP).
           assert (EQ: tt2 = tb3).
           eapply type_of_map with (g := (b1, b2, f3, tb3) :: removeEntry (b1, b2) g3)...
           destruct EQ; subst tt2.
           eapply TPar with (pf1 := pfk0) (pf2 := pfk3);
             try assumption.
        eapply tEnv_split_add_fp; try assumption.

        introv ISUN; destruct  ISUN as (ff &tt &ISUN); subst tb1; inv TP; try contradiction.
        assert (EQP: p0=p4 /\ p4 = (pol_cup p0 p4)).
        eapply split_plus_un with (b1 := b1) (b2 := b2)...
        destruct EQP; subst; rewrite <-H4...

        eauto.
        eapply typeCheck_impl with (pf1 := pf3),
        in_removeEntry_cons_iff_0...

        
        (* REPL CASE*)

        assert (ne = ne1).
          destruct REPL as [q [REPL [INCL NEEQ]]].

                   
        assert (ne1 = newEntries g1
                                 (secLabs (dep_relabel q (domain g1) nd_pf1))
                                 (max (domain g1))).
        assert (W0:  incl (secLabs p1) (domain (hid_proj g1))).
        eapply typeCheck_hid_proj_par...
        (*assert (IN0: incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup...
        eapply incl_iff with (m2 := domain g) in IN0.
        unfold incl in *; intros a IN1; specialize IN0 with a;
          eapply IN0 in IN1 as K; eapply in_domain_in_g in K as (ff &tt &K). Search secLabs hid. *)
        assert (W1:  NoDup (secLabs p1)).
        eapply typeCheck_no_dup with (pf := pf0)...
        assert (W2: In (a1, a2, hid, Chan un io t) g1).
        eapply tsub_un with (pf := pf1) in IN0a as INa. inversion INa; subst; clear INa.
        eapply fsub_hid with (pf := pf1) in IN0a as INa. 
        assert (f = hid). eapply flag_of_map with (g := g1)...
        subst...
        eauto.
        eauto.
        assert (W3 :  In (b1, b2) (domain g1)). eapply in_g_in_domain...
        eapply lts_un_tau_action_newEntries_2h with (b1 := b1) (b2 := b2)...
        subst; right;simpl; try rewrite pairEq_eq_true...
        
        
        assert (ne = nil).
        subst; eapply newEntries_nil with (g := g1).
        eauto.
        intros. assert ( In x (domain g0) <-> In x (domain g1)).
        eapply split_domain_l...
        intuition auto.
        assert (MAX: max (domain g0) = max (domain g1)).
        eapply max_same_domain...
        erewrite identif_seclabs_of_dep_relabel,MAX,<-identif_seclabs_of_dep_relabel...
        subst...
        
        subst.
        gen pfk0. subst; simpl in *; rewrite pairEq_eq_true in *. intros.
        
         assert (nd_pfk3: NoDup (domain ((b1, b2, f3, tb3) :: (removeEntry (b1, b2) g3)))).
        eapply no_dup_cons_removeEntry...
        eapply no_dup_isMap in nd_pfk3 as pfk3.
        eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
        subst.
        eapply split_cons_remove_3...
        eauto.
        eapply typeCheck_impl with (pf1 := pf3),in_removeEntry_cons_iff_0...

        destruct NEEQ as [NENIL | REPL].
        assert (ne1 = ne).
        destruct REPL1 as [q [REPL [INCL NEEQ]]].
        assert (ne = newEntries g0
                                 (secLabs (dep_relabel q (domain g0) nd_pf0))
                                 (max (domain g0))).
         assert (W0:  incl (secLabs p1) (domain (hid_proj g0)))...
        
        assert (W1:  NoDup (secLabs p1)).
        eapply typeCheck_no_dup with (pf := pf0)...
        assert (W2: In (a1, a2, hid, Chan un io t) g1).
        eapply tsub_un with (pf := pf1) in IN0a as INa. inversion INa; subst; clear INa.
        eapply fsub_hid with (pf := pf1) in IN0a as INa. 
        assert (f = hid). eapply flag_of_map with (g := g1)...
        subst...
        eauto.
        eauto.
        assert (W3 :  In (b1, b2) (domain g0)). eapply in_g_in_domain...
        eapply lts_un_tau_action_newEntries_2h with (b1 := b1) (b2 := b2)...

        
        assert (ne1 = nil).
        subst ne1. eapply newEntries_nil with (g := g0).
        eauto.
        intros; eapply split_domain_l...
        intuition auto.
        assert (MAX: max (domain g1) = max (domain g0)).
        eapply max_same_domain...
        erewrite identif_seclabs_of_dep_relabel,MAX,<-identif_seclabs_of_dep_relabel, <-H...
        subst...

        subst.

        gen pfk0; simpl in *;
          rewrite pairEq_eq_true in *; intros.
        assert (nd_pfk3: NoDup (domain ((b1, b2, f3, tb3) :: (removeEntry (b1, b2) g3)))).
        eapply no_dup_cons_removeEntry...
        eapply no_dup_isMap in nd_pfk3 as pfk3.
        eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
        subst.
        eapply split_cons_remove_3...
        eauto.
        eapply typeCheck_impl with (pf1 := pf3),in_removeEntry_cons_iff_0...

        (* replicated case *)
        destruct REPL1 as [q1 [REPL1 [INCL1 NEEQ1]]].
        destruct REPL as [q [REPL [INCL NEEQ]]].
        assert (q = q1). eapply replication_unique...
        subst q1.

        remember (newEntries g3 (secLabs (dep_relabel q (domain g3) nd_pf3)) (max (domain g3))) as ne3.
        assert (nd_pfk3: NoDup (domain (ne3 ++ (b1, b2, f3, tb3) :: (removeEntry (b1, b2) g3)))).
        erewrite domain_distr. eapply distr_no_dup.
        subst. eapply newEntries_no_dup.
        eapply wf_rewrite,prop27,incl_incl2.
       eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
       eauto.
       eapply incl_tran with (m := secLabs p1)...
       eapply incl_iff with (m1 := (domain g0)).
       eapply typeCheck_no_dup with (pf := pf0)...
       intros; eapply split_domain_m...
       eauto.
       eapply no_dup_cons_removeEntry...
       assert (DIS : disjoint (domain g3) (domain ne3)).
       subst; eapply new_entries_disjoint.
        unfold sl_pos, pos in *; intros.
        specialize SLP with x1 x2;
          unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL; specialize INCL with (x1,x2); intuition.
         assert (MAX2: max(domain g3) >= max (secLabs q)).
        eapply incl_preserves_max, incl_tran with (m := secLabs p1)... assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        eapply incl_iff with (m1 := domain g0);
          try eassumption.
        intros; eapply split_domain_m...  
        lia.
        assert (NIN: ~In (b1, b2) (domain ne3)).
        intros ABS.
        assert (INB: In (b1, b2) (domain g3)).
        eapply in_g_in_domain...
        eapply disjoint_absurd...  
        eapply disjoint_commute, disjoint_cons_removeEntry...
        apply no_dup_isMap in nd_pfk3 as pfk3.
        rewrite NEEQ,removeEntry_app_shift in EQK0;
          simpl in EQK0; try rewrite pairEq_eq_true in EQK0.
        
        eapply TPar with (pf1 := pfk0) (pf2 := pfk3);
          try assumption.
        subst.
        assert (nd_pfk0': NoDup (domain (newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0)) ++ (b1, b2, hid, tb0) ::  removeEntry (b1, b2) g0))).
        assert (TC1 := H2).
        eapply typeCheck_no_dup in TC1 as [INCL0 ND1];
          try eassumption.
        assert (INCL1': incl (secLabs p1) (domain g3)).
        eapply incl_iff; try eassumption.
        intros; eapply split_domain_m...
        rewrite domain_distr,no_dup_iff; repeat split;
          try eapply newEntries_no_dup;
           try eapply prop27;
           try eapply incl_incl2,incl_tran;
          try eapply replication_no_dup;
          try eapply no_dup_cons_removeEntry;
          try eassumption.
        assert (DIS2 :
                 disjoint
    (domain (newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0))))
    (domain  g0)).
        try eapply disjoint_commute,  new_entries_disjoint;
           try eapply sl_pos_repl;
          try eapply incl_preserves_max,incl_tran;
          try eassumption.
        eapply disjoint_commute,disjoint_iff; try eapply disjoint_commute... 
        
        eapply no_dup_isMap in nd_pfk0' as pfk0'.
        eapply split_comm, split_iff2 with (pf2 := pfk0');
          try assumption.
        eapply split_comm, split_distr.
        eapply split_newEntries...
        eapply split_cons_remove_3...

        (*  forall x : name * name * flag * piType,
  In x
    (newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0)) ++
     (b1, b2, hid, tb0) :: removeEntry (b1, b2) g0) <->
  In x
    ((b1, b2, hid, tb0)
     :: newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0)) ++
        removeEntry (b1, b2) g0) *)
        remember (newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0)))as ne0.
        eapply Permutation_iff,Permutation.Permutation_sym,Permutation.Permutation_middle.
        
        (* typeCheck (ne3 ++ (b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) pfk3 p3 *)
        assert (nd_pfne3g3: NoDup (domain (ne3 ++ g3))).
        erewrite domain_distr. eapply distr_no_dup.
        subst; eapply newEntries_no_dup...
        eapply wf_rewrite,prop27,incl_incl2.
        eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
        eauto.
        eapply incl_tran with (m := secLabs p1)...
        assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        eapply incl_iff with (m1 := domain g0);
          try eassumption.
        intros; eapply split_domain_m...
        eauto.
        subst; erewrite disjoint_commute; eapply new_entries_disjoint.
        unfold sl_pos, pos in *; intros.
        specialize SLP with x1 x2;
          unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL; specialize INCL with (x1,x2); intuition.
        assert (MAX: max(domain g1) >= max (secLabs q)).
        eapply incl_preserves_max, incl_tran with (m := secLabs p1)... assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        eapply incl_iff with (m1 := domain g0)...
        erewrite split_max with (pf := pf1). lia.
        eapply split_comm...
        eapply no_dup_isMap in nd_pfne3g3 as pfne3g3.
        
        
        eapply typeCheck_impl with (pf1 := pfne3g3).
        eauto. eauto.
        eapply typeCheck_weak2.
        erewrite <-domain_distr...
        eauto.
        (* cons ne3 ?pfk *)
        assert (INVNE: forall c1 c2 ff tt,
                   In (c1, c2, ff, tt) ne3 ->
                   In (c1, c2 - max (domain g3)) (secLabs q) /\ In (c1, c2 - max (domain g3), ff, tt) g3).
        intros.
        eapply inverse_newEntries.
        eauto.
        (* sl_pos rp *)
                 eapply sl_pos_par_l in SLP;
                   unfold sl_pos in SLP;
                   unfold sl_pos.
                 eapply incl_pos with (l2 :=(secLabs p1))...
        (* incl (secLabs rp) (domain g3) *)
        eapply incl_tran with (m := secLabs p1).
        assumption.
        eapply incl_iff with (m1 := domain g0).
        eapply typeCheck_no_dup with (pf := pf0)...
        intros. eapply split_domain_m... 
        (*In (c1, c2, ff, tt)
    (newEntries g3
       (map (fun x : name * name => (fst x, snd x + max (domain g3))) (secLabs rp))
       (max (domain g3)))*)
        subst. erewrite <-identif_seclabs_of_dep_relabel...
        eapply cons_char.
        destruct ne3. left...
        right. intros.
        specialize INVNE with c1 c2 ff tt.
        apply INVNE in H; clear INVNE.
        destruct H as [INSL IN3'].
        remember (c2 - max (domain g3)) as c''.
        assert (IN2: exists t, In (c1, c'',hid, t) g0).
        eapply typeCheck_hid...
        destruct IN2 as [tt0 IN2].
        assert (ff = ill).
        assert (IN1: In (c1, c'') (secLabs p1)).
        eapply INCL...
        assert (flagOf g3 (c1, c'') ill).
        eapply finv_hid_r,split_comm...
        eapply flag_of_map with (g := g3)...
        subst ff.
        assert (F1': flagOf g1 (c1, c'')  hid).
        eapply fsub_hid... 
        inversion F1'. subst g4 n f.
        eapply typeCheck_ill with (p := p3)...

        subst ne3;
          rewrite identif_seclabs_of_dep_relabel in *;
          eapply Peirce; intros ABS;
          eapply not_disjoint in ABS as ([x1 x2] &ABS1 &ABS2);
          eapply in_bv_lt_max with (pf := pf3) in ABS1;
          eapply in_domain_in_g in ABS2 as (ff &tt &ABS2);
          eapply newEntries_gte_max in ABS2;
          try lia;
          try eassumption.
        
        eapply in_app_removeEntry_iff_0...

        intros ABS.
        assert (DIS: disjoint (domain
                                 (newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0)))) (domain g0)).
        eapply disjoint_commute, new_entries_disjoint;
          try eassumption.
        eapply sl_pos_par_l in SLP;
          unfold sl_pos in SLP;
          unfold sl_pos.
        eapply incl_pos with (l2 :=(secLabs p1))...
        eapply incl_preserves_max, incl_tran with (m := secLabs p1)... assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        assumption.
        eapply disjoint_absurd...

        (* last disjunction *)
           subst fb0 f1.

           destruct NE1EQ as [NE1NIL | REPL1].
           destruct NEEQ as [NENIL | REPL].
        
        assert (nd_pfk3: NoDup (domain ((b1, b2, f3, tb3) :: (removeEntry (b1, b2) g3)))).
        eapply no_dup_cons_removeEntry...
        eapply no_dup_isMap in nd_pfk3 as pfk3.
        
        gen pfk0. gen pfk1. subst; simpl in *; rewrite pairEq_eq_true in *. intros.

         assert (FP:
                    exists t2 : flag, flagOf  ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1,b2) t2 /\ flag_plus hid t2 hid).
           eapply split_flag_plus with
             (pf1 := pf') (pf2 := pf'') (pf := pf''')...
           destruct FP as (ff2 &FYP &FP).
           inv FYP.
           assert (EQ: ff2 = f3 /\ t0 = tb3).
           eapply in_isMap...
           destruct EQ; subst ff2.

            assert (TP:
                     exists t2, typeOf  ((b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) (b1,b2) t2 /\ type_plus tb0 t2 tb1).
             eapply split_type_plus with
             (pf1 := pf') (pf2 := pf'') (pf := pf''')...
           destruct TP as (tt2 &TYP2 &TP).
           assert (EQ: tt2 = tb3).
           eapply type_of_map with (g := (b1, b2, f3, tb3) :: removeEntry (b1, b2) g3)...
           destruct EQ; subst tt2.
           eapply TPar with (pf1 := pfk0) (pf2 := pfk3);
             try assumption.
        eapply tEnv_split_add_fp; try assumption.

        introv ISUN; destruct  ISUN as (ff &tt &ISUN); subst tb1; inv TP; try contradiction.
        assert (EQP: p0=p4 /\ p4 = (pol_cup p0 p4)).
        eapply split_plus_un with (b1 := b1) (b2 := b2)...
        destruct EQP; subst; rewrite <-H4...

        eauto.
        eapply typeCheck_impl with (pf1 := pf3),
        in_removeEntry_cons_iff_0...

        
        (* REPL CASE*)

        assert (ne = ne1).
          destruct REPL as [q [REPL [INCL NEEQ]]].

                   
        assert (ne1 = newEntries g1
                                 (secLabs (dep_relabel q (domain g1) nd_pf1))
                                 (max (domain g1))).
        assert (W0:  incl (secLabs p1) (domain (hid_proj g1))).
        eapply typeCheck_hid_proj_par...
        assert (W1:  NoDup (secLabs p1)).
        eapply typeCheck_no_dup with (pf := pf0)...
        assert (W2: In (a1, a2, hid, Chan un io t) g1).
        eapply tsub_un with (pf := pf1) in IN0a as INa. inversion INa; subst; clear INa.
        eapply fsub_hid with (pf := pf1) in IN0a as INa. 
        assert (f = hid). eapply flag_of_map with (g := g1)...
        subst...
        eauto.
        eauto.
        assert (W3 :  In (b1, b2) (domain g1)). eapply in_g_in_domain...
        eapply lts_un_tau_action_newEntries_2h with (b1 := b1) (b2 := b2); try discriminate...

        
        
        assert (ne = nil).
        subst; eapply newEntries_nil with (g := g1).
        eauto.
        intros. assert ( In x (domain g0) <-> In x (domain g1)).
        eapply split_domain_l...
        intuition auto.
        assert (MAX: max (domain g0) = max (domain g1)).
        eapply max_same_domain...
        erewrite identif_seclabs_of_dep_relabel,MAX,<-identif_seclabs_of_dep_relabel...
        subst...
        
        subst.
        gen pfk0 pfk1. subst; simpl in *; rewrite pairEq_eq_true in *. intros.
        
         assert (nd_pfk3: NoDup (domain ((b1, b2, f3, tb3) :: (removeEntry (b1, b2) g3)))).
        eapply no_dup_cons_removeEntry...
        eapply no_dup_isMap in nd_pfk3 as pfk3.
        eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
        subst.
        eapply split_cons_remove_3...
        eauto.
        eapply typeCheck_impl with (pf1 := pf3),in_removeEntry_cons_iff_0...

        destruct NEEQ as [NENIL | REPL].
        assert (ne1 = ne).
        destruct REPL1 as [q [REPL [INCL NEEQ]]].
        assert (ne = newEntries g0
                                 (secLabs (dep_relabel q (domain g0) nd_pf0))
                                 (max (domain g0))).
         assert (W0:  incl (secLabs p1) (domain (hid_proj g0)))...
        
        assert (W1:  NoDup (secLabs p1)).
        eapply typeCheck_no_dup with (pf := pf0)...
        assert (W2: In (a1, a2, hid, Chan un io t) g1).
        eapply tsub_un with (pf := pf1) in IN0a as INa. inversion INa; subst; clear INa.
        eapply fsub_hid with (pf := pf1) in IN0a as INa. 
        assert (f = hid). eapply flag_of_map with (g := g1)...
        subst...
        eauto.
        eauto.
        assert (W3 :  In (b1, b2) (domain g0)). eapply in_g_in_domain...
        eapply lts_un_tau_action_newEntries_2h with (b1 := b1) (b2 := b2); try discriminate...


       
        
        assert (ne1 = nil).
        subst ne1. eapply newEntries_nil with (g := g0).
        eauto.
        intros; eapply split_domain_l...
        intuition auto.
        assert (MAX: max (domain g1) = max (domain g0)).
        eapply max_same_domain...
        erewrite identif_seclabs_of_dep_relabel,MAX,<-identif_seclabs_of_dep_relabel...
        subst...

        subst...

        subst.

        gen pfk0 pfk1; simpl in *;
          rewrite pairEq_eq_true in *; intros.
        assert (nd_pfk3: NoDup (domain ((b1, b2, f3, tb3) :: (removeEntry (b1, b2) g3)))).
        eapply no_dup_cons_removeEntry...
        eapply no_dup_isMap in nd_pfk3 as pfk3.
        eapply TPar with (pf1 := pfk0) (pf2 := pfk3).
        subst.
        eapply split_cons_remove_3...
        eauto.
        eapply typeCheck_impl with (pf1 := pf3),in_removeEntry_cons_iff_0...

        (* replicated case *)
        destruct REPL1 as [q1 [REPL1 [INCL1 NEEQ1]]].
        destruct REPL as [q [REPL [INCL NEEQ]]].
        assert (q = q1). eapply replication_unique...
        subst q1.

        remember (newEntries g3 (secLabs (dep_relabel q (domain g3) nd_pf3)) (max (domain g3))) as ne3.
        assert (nd_pfk3: NoDup (domain (ne3 ++ (b1, b2, f3, tb3) :: (removeEntry (b1, b2) g3)))).
        erewrite domain_distr. eapply distr_no_dup.
        subst. eapply newEntries_no_dup.
        eapply wf_rewrite,prop27,incl_incl2.
       eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
       eauto.
       eapply incl_tran with (m := secLabs p1)...
       eapply incl_iff with (m1 := (domain g0)).
       eapply typeCheck_no_dup with (pf := pf0)...
       intros; eapply split_domain_m...
       eauto.
       eapply no_dup_cons_removeEntry...
       assert (DIS : disjoint (domain g3) (domain ne3)).
       subst; eapply new_entries_disjoint.
        unfold sl_pos, pos in *; intros.
        specialize SLP with x1 x2;
          unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL; specialize INCL with (x1,x2); intuition.
         assert (MAX2: max(domain g3) >= max (secLabs q)).
        eapply incl_preserves_max, incl_tran with (m := secLabs p1)... assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        eapply incl_iff with (m1 := domain g0);
          try eassumption.
        intros; eapply split_domain_m...  
        lia.
        assert (NIN: ~In (b1, b2) (domain ne3)).
        intros ABS.
        assert (INB: In (b1, b2) (domain g3)).
        eapply in_g_in_domain...
        eapply disjoint_absurd...  
        eapply disjoint_commute, disjoint_cons_removeEntry...
        apply no_dup_isMap in nd_pfk3 as pfk3.
        rewrite NEEQ,removeEntry_app_shift in EQK0;
          simpl in EQK0; try rewrite pairEq_eq_true in EQK0.
        
        eapply TPar with (pf1 := pfk0) (pf2 := pfk3);
          try assumption.
        subst.
        assert (nd_pfk0': NoDup (domain (newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0)) ++ (b1, b2, hid, tb0) ::  removeEntry (b1, b2) g0))).
         assert (TC1 := H2).
        eapply typeCheck_no_dup in TC1 as [INCL0 ND1];
          try eassumption.
        assert (INCL1': incl (secLabs p1) (domain g3)).
        eapply incl_iff; try eassumption.
        intros; eapply split_domain_m...
        rewrite domain_distr,no_dup_iff; repeat split;
          try eapply newEntries_no_dup;
           try eapply prop27;
           try eapply incl_incl2,incl_tran;
          try eapply replication_no_dup;
          try eapply no_dup_cons_removeEntry;
          try eassumption.
        assert (DIS2 :
                 disjoint
    (domain (newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0))))
    (domain  g0)).
        try eapply disjoint_commute,  new_entries_disjoint;
           try eapply sl_pos_repl;
          try eapply incl_preserves_max,incl_tran;
          try eassumption.
        eapply disjoint_commute,disjoint_iff; try eapply disjoint_commute... 
        
        eapply no_dup_isMap in nd_pfk0' as pfk0'.
        assert (nd_pfk1': NoDup (domain ((newEntries g1 (secLabs (dep_relabel q (domain g1) nd_pf1)) (max (domain g1))) ++ (b1, b2, hid, tb1) ::  removeEntry (b1, b2) g1))).
         assert (TC1 := H2).
        eapply typeCheck_no_dup in TC1 as [INCL0 ND1];
          try eassumption.
        assert (INCL1': incl (secLabs p1) (domain g3)).
        eapply incl_iff; try eassumption.
        intros; eapply split_domain_m...
        rewrite domain_distr,no_dup_iff; repeat split;
          try eapply newEntries_no_dup;
           try eapply prop27;
           try eapply incl_incl2,incl_tran;
          try eapply replication_no_dup;
          try eapply no_dup_cons_removeEntry;
          try eassumption.
        eapply incl_iff; try eassumption;
          intros; try eapply split_domain_r;
          try eassumption.
        assert (DIS2 :
                 disjoint
    (domain (newEntries g1 (secLabs (dep_relabel q (domain g1) nd_pf1)) (max (domain g1))))
    (domain  g1)).
        try eapply disjoint_commute,  new_entries_disjoint;
           try eapply sl_pos_repl;
          try eapply incl_preserves_max,incl_tran;
          try eassumption;
            eapply incl_iff; try eassumption;
          intros; try eapply split_domain_r;
          try eassumption.
        eapply disjoint_commute,disjoint_iff; try eapply disjoint_commute... 
         eapply no_dup_isMap in nd_pfk1' as pfk1'.
         eapply split_comm, split_iff2 with (pf2 := pfk0');
           try assumption.
         try eapply split_iff with (pf := pfk1');
           try assumption.
        eapply split_comm, split_distr.
        eapply split_newEntries...
        eapply split_cons_remove_3...

        (*  forall x : name * name * flag * piType,
  In x (ne1 ++ (b1, b2, hid, tb1) :: removeEntry (b1, b2) g1) <->
  In x
    ((b1, b2, hid, tb1)
     :: removeEntry (b1, b2) (ne1 ++ (b1, b2, vis, tb1) :: removeEntry (b1, b2) g1)) *)
        remember (newEntries g1 (secLabs (dep_relabel q (domain g1) nd_pf1)) (max (domain g1)))as ne1.
        rewrite removeEntry_app_shift; unfold removeEntry; fold removeEntry;
          try rewrite pairEq_eq_true.
        eapply Permutation_iff,Permutation.Permutation_sym,Permutation.Permutation_middle.
        intros ABS; rewrite domain_distr in nd_pfk1';
          eapply no_dup_iff in nd_pfk1' as (ND1 &ND2&DIS);
          try eapply disjoint_absurd...
        (* forall x : name * name * flag * piType,
  In x
    (newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0)) ++
     (b1, b2, hid, tb0) :: removeEntry (b1, b2) g0) <->
  In x
    ((b1, b2, hid, tb0)
     :: newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0)) ++
        removeEntry (b1, b2) g0)*)
        remember (newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0)))as ne0.
        eapply Permutation_iff,Permutation.Permutation_sym,Permutation.Permutation_middle.
        
        (* typeCheck (ne3 ++ (b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) pfk3 p3 *)
        assert (nd_pfne3g3: NoDup (domain (ne3 ++ g3))).
        erewrite domain_distr. eapply distr_no_dup.
        subst; eapply newEntries_no_dup...
        eapply wf_rewrite,prop27,incl_incl2.
        eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
        eauto.
        eapply incl_tran with (m := secLabs p1)...
        assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        eapply incl_iff with (m1 := domain g0);
          try eassumption.
        intros; eapply split_domain_m...
        eauto.
        subst; erewrite disjoint_commute; eapply new_entries_disjoint.
        unfold sl_pos, pos in *; intros.
        specialize SLP with x1 x2;
          unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL; specialize INCL with (x1,x2); intuition.
        assert (MAX: max(domain g1) >= max (secLabs q)).
        eapply incl_preserves_max, incl_tran with (m := secLabs p1)... assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        eapply incl_iff with (m1 := domain g0)...
        erewrite split_max with (pf := pf1). lia.
        eapply split_comm...
        eapply no_dup_isMap in nd_pfne3g3 as pfne3g3.
        
        
        eapply typeCheck_impl with (pf1 := pfne3g3).
        eauto. eauto.
        eapply typeCheck_weak2.
        erewrite <-domain_distr...
        eauto.
        (* cons ne3 ?pfk *)
        assert (INVNE: forall c1 c2 ff tt,
                   In (c1, c2, ff, tt) ne3 ->
                   In (c1, c2 - max (domain g3)) (secLabs q) /\ In (c1, c2 - max (domain g3), ff, tt) g3).
        intros.
        eapply inverse_newEntries.
        eauto.
        (* sl_pos rp *)
                 eapply sl_pos_par_l in SLP;
                   unfold sl_pos in SLP;
                   unfold sl_pos.
                 eapply incl_pos with (l2 :=(secLabs p1))...
        (* incl (secLabs rp) (domain g3) *)
        eapply incl_tran with (m := secLabs p1).
        assumption.
        eapply incl_iff with (m1 := domain g0).
        eapply typeCheck_no_dup with (pf := pf0)...
        intros. eapply split_domain_m... 
        (*In (c1, c2, ff, tt)
    (newEntries g3
       (map (fun x : name * name => (fst x, snd x + max (domain g3))) (secLabs rp))
       (max (domain g3)))*)
        subst. erewrite <-identif_seclabs_of_dep_relabel...
        eapply cons_char.
        destruct ne3. left...
        right. intros.
        specialize INVNE with c1 c2 ff tt.
        apply INVNE in H; clear INVNE.
        destruct H as [INSL IN3'].
        remember (c2 - max (domain g3)) as c''.
        assert (IN2: exists t, In (c1, c'',hid, t) g0).
        eapply typeCheck_hid...
        destruct IN2 as [tt0 IN2].
        assert (ff = ill).
        assert (IN1: In (c1, c'') (secLabs p1)).
        eapply INCL...
        assert (flagOf g3 (c1, c'') ill).
        eapply finv_hid_r,split_comm...
        eapply flag_of_map with (g := g3)...
        subst ff.
        assert (F1': flagOf g1 (c1, c'')  hid).
        eapply fsub_hid... 
        inversion F1'. subst g4 n f.
        eapply typeCheck_ill with (p := p3)...

        subst ne3;
          rewrite identif_seclabs_of_dep_relabel in *;
          eapply Peirce; intros ABS;
          eapply not_disjoint in ABS as ([x1 x2] &ABS1 &ABS2);
          eapply in_bv_lt_max with (pf := pf3) in ABS1;
          eapply in_domain_in_g in ABS2 as (ff &tt &ABS2);
          eapply newEntries_gte_max in ABS2;
          try lia;
          try eassumption.
        
        eapply in_app_removeEntry_iff_0...

        intros ABS.
        assert (DIS: disjoint (domain
                                 (newEntries g0 (secLabs (dep_relabel q (domain g0) nd_pf0)) (max (domain g0)))) (domain g0)).
        eapply disjoint_commute, new_entries_disjoint;
          try eassumption.
        eapply sl_pos_par_l in SLP;
          unfold sl_pos in SLP;
          unfold sl_pos.
        eapply incl_pos with (l2 :=(secLabs p1))...
        eapply incl_preserves_max, incl_tran with (m := secLabs p1)... assert(  incl (secLabs p1) (domain g0)).
        eapply typeCheck_no_dup with (pf := pf0)...
        assumption.
        eapply disjoint_absurd...
      
        (**)
          introv PNEQ; rewrite <-pairEq_neq in PNEQ.

          
          destruct EQK1 as [(EQK1 &DIFF1)| (EQK1 &DIFF1)];
            destruct NE1EQ as [NIL1 | REPL1];subst.
          (***) eapply TPar with (g2 := g3) (pf1 := pfk0);
                try eassumption.
              destruct EQK0 as [(EQK0 &DIFF0)| (EQK0 &DIFF0)];
            destruct NEEQ as [NEEQ0 | REPL0]; subst k0.

              subst ne; simpl.
              eapply split_iff with (pf := pf1);
                try eassumption.
              eapply split_comm.
              eapply split_iff2 with (pf2 := pf0);
                try eassumption.
              eapply split_comm...
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.

              destruct REPL0 as (q &REPL0 &INCL0 &NEEQ0).

              assert (ne = nil).
              destruct ne; try tauto.
              destruct fc.
              move LTS1 at bottom.
              simpl in LTS1.
              assert (REM:
                       removeEntry (c1, c2) g1 =
                         removeEntry (c1, c2) (nil ++ (c1, c2, vis, tc):: removeEntry (c1, c2)g1)).
              simpl; rewrite pairEq_eq_true...
              gen nd_pf1; rewrite REM; intros.
              
              eapply lts_un_tau_action_newEntries_1hk in LTS1;
                try eassumption.
              assert (EQSL:  secLabs (dep_relabel q (domain g1) nd_pf1) =
                         secLabs (dep_relabel q (domain g0) nd_pf0)).
              repeat rewrite identif_seclabs_of_dep_relabel.
              erewrite max_same_domain...
              rewrite EQSL,LTS1,newEntries_nil_nil in *;
                try discriminate...
              
              assert (TC1 := H2).
              eapply typeCheck_hid_proj in TC1;
                try eapply incl_tran,split_incl_hid_proj...
              eapply typeCheck_no_dup in H2 as (_ &IH')...
              assert (TMP := IN0a);
                eapply tsub_un with (g := g1) in TMP;
                try inv TMP.
              assert (flagOf g1 (a1,a2) hid).
              eapply fsub_hid...
              inv H0.
              assert (f = hid).
              eapply flag_of_map with (g := g1)...
              subst...
              eauto.
              eauto.

              contradiction.

               eapply lts_un_tau_action_newEntries_1k in LTS1;
                try eassumption.
              assert (EQSL:  secLabs (dep_relabel q (domain g1) nd_pf1) =
                         secLabs (dep_relabel q (domain g0) nd_pf0)).
              repeat rewrite identif_seclabs_of_dep_relabel.
              erewrite max_same_domain...
              rewrite EQSL,LTS1,newEntries_nil_nil in *;
                try discriminate...

               assert (TC1 := H2).
              eapply typeCheck_hid_proj in TC1;
                try eapply incl_tran,split_incl_hid_proj...
              eapply typeCheck_no_dup in H2 as (_ &IH')...
              assert (TMP := IN0a);
                eapply tsub_un with (g := g1) in TMP;
                try inv TMP.
              assert (flagOf g1 (a1,a2) hid).
              eapply fsub_hid...
              inv H0.
              assert (f = hid).
              eapply flag_of_map with (g := g1)...
              subst...
              eauto.
              eauto.
              
              subst ne; gen pfk0; simpl; rewrite H in *; simpl; introv TC'.
              try eapply split_iff with (pf := pf1);
                try eassumption.
              eapply split_comm.
              eapply split_iff2 with (pf2 := pf0);
                try eassumption.
              eapply split_comm...
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.

              

              
              subst ne; gen pfk0; simpl; try rewrite pairEq_eq_true; introv TC'.
              eapply split_iff with (pf := pf1); try eassumption.
              eapply split_comm.
              eapply split_iff2 with (pf2 := pf0);
                try eassumption.
              eauto.
              eapply split_comm...
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.

               destruct REPL0 as (q &REPL0 &INCL0 &NEEQ0).

              assert (ne = nil).
              destruct ne; try tauto.

              destruct fc.
              move LTS1 at bottom.
              simpl in LTS1.
              assert (REM:
                       removeEntry (c1, c2) g1 =
                         removeEntry (c1, c2) (nil ++ (c1, c2, vis, tc):: removeEntry (c1, c2)g1)).
              simpl; rewrite pairEq_eq_true...

              gen nd_pf1; rewrite REM; intros.
              
              eapply lts_un_tau_action_newEntries_1hk in LTS1;
                try eassumption.

               assert (EQSL:  secLabs (dep_relabel q (domain g1) nd_pf1) =
                         secLabs (dep_relabel q (domain g0) nd_pf0)).
              repeat rewrite identif_seclabs_of_dep_relabel.
              erewrite max_same_domain...
              rewrite EQSL,LTS1,newEntries_nil_nil in *;
                try discriminate...

               assert (TC1 := H2).
              eapply typeCheck_hid_proj in TC1;
                try eapply incl_tran,split_incl_hid_proj...
              eapply typeCheck_no_dup in H2 as (_ &IH')...
              assert (TMP := IN0a);
                eapply tsub_un with (g := g1) in TMP;
                try inv TMP.
              assert (flagOf g1 (a1,a2) hid).
              eapply fsub_hid...
              inv H0.
              assert (f = hid).
              eapply flag_of_map with (g := g1)...
              subst...
              eauto.
              eauto.

              contradiction.

              
              
             
              
              eapply lts_un_tau_action_newEntries_1k in LTS1;
                try eassumption.
              assert (EQSL:  secLabs (dep_relabel q (domain g1) nd_pf1) =
                         secLabs (dep_relabel q (domain g0) nd_pf0)).
              repeat rewrite identif_seclabs_of_dep_relabel.
              erewrite max_same_domain...
              rewrite EQSL,LTS1,newEntries_nil_nil in *;
                try discriminate...

               assert (TC1 := H2).
              eapply typeCheck_hid_proj in TC1;
                try eapply incl_tran,split_incl_hid_proj...
              eapply typeCheck_no_dup in H2 as (_ &IH')...
              assert (TMP := IN0a);
                eapply tsub_un with (g := g1) in TMP;
                try inv TMP.
              assert (flagOf g1 (a1,a2) hid).
              eapply fsub_hid...
              inv H0.
              assert (f = hid).
              eapply flag_of_map with (g := g1)...
              subst...
              eauto.
              eauto.

              subst ne; gen pfk0; simpl; rewrite H in *; simpl;
                try rewrite pairEq_eq_true; introv TC'.
              try eapply split_iff with (pf := pf1);
                try eassumption.
              eapply split_comm.
              eapply split_iff2 with (pf2 := pf0);
                try eassumption.
              eauto.
              eapply split_comm...
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.

(*              eauto. *)

              
          (***)
            destruct REPL1 as (q &REPL1 &INCL1 &NEEQ1).
            remember (newEntries g3 (secLabs (dep_relabel q (domain g3) nd_pf3)) (max (domain g3))) as ne3.
            assert
              (nd_pfk2 :
                NoDup(domain (ne3 ++ g3))).
            assert (TC1 := H2).
            eapply typeCheck_no_dup in TC1 as [INCL0 ND1].
            assert (INCL1': incl (secLabs p1) (domain g3)).
            eapply incl_iff; try eassumption.
            intros; eapply split_domain_m...
            subst ne3; try rewrite domain_distr;
              try eapply no_dup_iff; repeat split;
              try eapply disjoint_commute;
              try eapply new_entries_disjoint;
              try eapply sl_pos_repl;
              try eapply incl_preserves_max,incl_tran;
              try eapply newEntries_no_dup;
              try eapply prop27;
              try eapply incl_incl2,incl_tran;
              try eapply replication_no_dup;
              try eassumption.
            assumption.
            assert (ND3 := nd_pfk2).
            assert (NIN3:   ~ In (b1, b2) (domain ne3)).
            rewrite domain_distr in ND3;
              eapply no_dup_iff in ND3 as (ND1 &ND3 &DIS3).
            intros ABS;
              try eapply disjoint_absurd...
            
            eapply no_dup_isMap in nd_pfk2 as pfk2.
            destruct NEEQ as [NIL0 | REPL0].
            eapply TPar with (pf1 := pfk0) (pf2 := pf3);
              try eassumption.

            subst ne.

            assert (ne1 = nil).
            destruct ne1; try tauto.
            destruct EQK0 as [(EQ0 &DIFF0) |(EQ0 &DIFF0)];
              subst k0.
            destruct fb0.

             move LTS0 at bottom.
              simpl in LTS0.
              assert (REM:
                       removeEntry (b1, b2) g0 =
                         removeEntry (b1, b2) (nil ++ (b1, b2, vis, tb0):: removeEntry (b1, b2)g0)).
              simpl; rewrite pairEq_eq_true...

              gen nd_pf0; rewrite REM; intros.
              
              eapply lts_un_tau_action_newEntries_1hk in LTS0;
                try eassumption.

               assert (EQSL:  secLabs (dep_relabel q (domain g1) nd_pf1) =
                         secLabs (dep_relabel q (domain g0) nd_pf0)).
              repeat rewrite identif_seclabs_of_dep_relabel.
              erewrite max_same_domain...
              rewrite EQSL,LTS0,newEntries_nil_nil in *;
                try discriminate...

               assert (TC1 := H2).
              eapply typeCheck_hid_proj in TC1...
              eapply typeCheck_no_dup in H2 as (_ &IH')...
              eauto.
              eauto.

              contradiction.

              
              eapply lts_un_tau_action_newEntries_1k in LTS0;
                try eassumption.

               assert (EQSL:  secLabs (dep_relabel q (domain g1) nd_pf1) =
                         secLabs (dep_relabel q (domain g0) nd_pf0)).
              repeat rewrite identif_seclabs_of_dep_relabel.
              erewrite max_same_domain...
              rewrite EQSL,LTS0,newEntries_nil_nil in *;
                try discriminate...

               assert (TC1 := H2).
              eapply typeCheck_hid_proj in TC1...
              eapply typeCheck_no_dup in H2 as (_ &IH')...
              eauto.
              eauto.

              subst fb0.
              move LTS0 at bottom.

            
              try eapply lts_un_tau_action_newEntries_1hk in LTS0;
              try eassumption.
            assert (EQSL:  secLabs (dep_relabel q (domain g1) nd_pf1) =
                             secLabs (dep_relabel q (domain g0) nd_pf0)).
            repeat rewrite identif_seclabs_of_dep_relabel.
            erewrite max_same_domain...
            rewrite EQSL,LTS0,newEntries_nil_nil in *;
              try discriminate...
             assert (TC1 := H2).
              eapply typeCheck_hid_proj in TC1...
              eapply typeCheck_no_dup in H2 as (_ &IH')...
              eauto.
              eauto.

              subst.

              
              
                destruct EQK0 as [(EQ0 &DIFF0) |(EQ0 &DIFF0)];
                  subst k0;gen pfk1; try rewrite H; simpl;introv.

                try eapply split_iff with (pf := pf1);
                  try eassumption.
                eauto.
              eapply split_comm.
              eapply split_iff2 with (pf2 := pf0);
                try eassumption.
              eapply split_comm...
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.

              gen pfk0; simpl; rewrite pairEq_eq_true; simpl; introv TC'.
              try eapply split_iff with (pf := pf1); try eassumption.
              eauto.
              eapply split_comm.
              eapply split_iff2 with (pf2 := pf0); try eassumption.
              eauto.
              eapply split_comm...
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.
(*              eauto. *)

               destruct REPL0 as (q' &REPL0 &INCL0 &NEEQ0).
               assert (q = q').
               eapply replication_unique...
               subst q'.
               move NEEQ0 at bottom.

        (*typeCheck (ne1 ++ (c1, c2, fc, tc) :: removeEntry (c1, c2) g1) pfk1 (dPar p2 p3)*)
               eapply TPar with (pf1 := pfk0) (pf2 := pfk2).

               (* tEnv_split k0 (ne3 ++ g3) (ne1 ++ (c1, c2, fc, tc) :: removeEntry (c1, c2) g1) pfk0 pfk2
    pfk1*)
               destruct EQK0 as
                 [(K0EQ &NILL) | (KOEQ1 &HID)];
                 subst k0.

               (*tEnv_split (ne ++ (b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0) 
    (ne3 ++ g3) (ne1 ++ (c1, c2, fc, tc) :: removeEntry (c1, c2) g1) pfk0 pfk2 pfk1*)
               
               assert (ND0: NoDup (domain (ne ++ g0))).
               rewrite domain_distr,no_dup_iff; repeat split.
               subst ne; try eapply newEntries_no_dup.
               eapply wf_rewrite,prop27,incl_incl2.
               eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
               eauto.
               eapply incl_tran with (m := secLabs p1)...
               eapply incl_iff with (m1 := (domain g0)).
               eapply typeCheck_no_dup with (pf := pf0)...
               intros; tauto. eauto. eauto.
               subst; eapply disjoint_commute, new_entries_disjoint.
               unfold sl_pos, pos in *; intros.
               specialize SLP with x1 x2;
                 unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL0; specialize INCL0 with (x1,x2); intuition.
               eapply incl_preserves_max, incl_tran with (m := secLabs p1)... 
               eapply typeCheck_no_dup with (pf := pf0)...
               
               
               assert (ND1: NoDup (domain (ne1 ++ g1))).
               rewrite domain_distr,no_dup_iff; repeat split.
               subst ne1; try eapply newEntries_no_dup.
               eapply wf_rewrite,prop27,incl_incl2.
               eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
               eauto.
               eapply incl_tran with (m := secLabs p1)...
               eapply incl_iff with (m1 := (domain g0)).
               eapply typeCheck_no_dup with (pf := pf0)...
               intros; eapply split_domain_r, split_comm...
               eauto. eauto.
               subst; eapply disjoint_commute, new_entries_disjoint.
               unfold sl_pos, pos in *; intros.
               specialize SLP with x1 x2;
                 unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL0; specialize INCL0 with (x1,x2); intuition.
               eapply incl_preserves_max, incl_tran with (m := secLabs p1)...
               assert (INCL2: incl (secLabs p1) (domain g0))...
               eapply typeCheck_no_dup with (pf := pf0)...
               eapply incl_iff...

               assert (TS1 := H1).
               assert (PF0:= ND0).
               eapply no_dup_isMap in PF0; rewrite NEEQ0 in PF0.
               assert (PF1:= ND1).
               eapply no_dup_isMap in PF1;
                 rewrite NEEQ1 in PF1.
               eapply split_newEntries
                 with (p:=q)
                      (nd_pf1 := nd_pf0)
                      (nd_pf2 := nd_pf3)
                      (nd_pf := nd_pf1)
                 in H1 as TSN; try eassumption.
               
               eapply split_comm,split_iff2 with
                 (g2 := ne ++ g0); try eassumption.

               eapply split_comm,split_iff with (g := ne1 ++ g1);
                 try eassumption.

               eapply split_distr.
               subst; eapply split_pf; try eassumption.
               eauto.

               (*forall x : name * name * flag * piType,
  In x (ne1 ++ g1) <-> In x (ne1 ++ (c1, c2, fc, tc) :: removeEntry (c1, c2) g1)*)
              
               eapply Permutation_iff,Permutation.Permutation_app_head,Permutation.NoDup_Permutation; try eapply no_dup_g; try eapply no_dup_cons_removeEntry;
                 try eassumption.
               intros; rewrite <-in_removeEntry_cons_iff_0...
               tauto.

               (* forall x : name * name * flag * piType,
  In x (ne ++ g0) <-> In x (ne ++ (b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0)*)
               
               eapply Permutation_iff,Permutation.Permutation_app_head,Permutation.NoDup_Permutation; try eapply no_dup_g; try eapply no_dup_cons_removeEntry;
                 try eassumption.
               intros; rewrite <-in_removeEntry_cons_iff_0...
               tauto.

               (* tEnv_split
    ((b1, b2, fb0, tb0)
     :: removeEntry (b1, b2) (ne ++ (b1, b2, vis, tb0) :: removeEntry (b1, b2) g0))
    (ne3 ++ g3) (ne1 ++ (c1, c2, fc, tc) :: removeEntry (c1, c2) g1) pfk0 pfk2 pfk1 *)

               
               assert (DIS: disjoint (domain g0) (domain ne) ).
               subst ne; eapply new_entries_disjoint.
                unfold sl_pos, pos in *; intros.
               specialize SLP with x1 x2;
                 unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL0; specialize INCL0 with (x1,x2); intuition.
               eapply incl_preserves_max, incl_tran with (m := secLabs p1)...
               assert (INCL2: incl (secLabs p1) (domain g0))...
               eapply typeCheck_no_dup with (pf := pf0)...

               assert (ND0: NoDup (domain (ne ++ g0))).
               rewrite domain_distr,no_dup_iff; repeat split.
               subst ne; try eapply newEntries_no_dup.
               eapply wf_rewrite,prop27,incl_incl2.
               eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
               eauto.
               eapply incl_tran with (m := secLabs p1)...
               eapply incl_iff with (m1 := (domain g0)).
               eapply typeCheck_no_dup with (pf := pf0)...
               intros; tauto.
               eauto. eauto. eapply disjoint_commute... 

               assert (NIN:
                        In (b1, b2) (domain ne) -> False).
               intros ABS.
               eapply disjoint_absurd...

               
               
               gen pfk0.
               rewrite removeEntry_app_shift;
                 try eassumption;
                 simpl;
                 try rewrite pairEq_eq_true;
                 introv.

               assert (ND0':
                        NoDup (domain (ne ++ (b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0))).
               rewrite domain_distr in *; simpl in *; rewrite no_dup_iff in *; repeat split.
               intuition.
               eapply no_dup_cons_removeEntry; intuition.
               eapply disjoint_commute,disjoint_iff with (l1 := domain g0);
                 try eapply disjoint_commute.
               intuition.
               intros. try rewrite in_removeEntry_cons_iff with (b1 := b1) (b2 := b2) (f := ill) (t := Top);
                 unfold domain; fold domain; try tauto.
               eauto.

               introv TC'.

               eapply split_comm,split_iff2
                 with (g2 :=
                         ne ++ (b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0); try eassumption.

               simpl;rewrite domain_distr; econstructor;
                 try intros ABS; try eapply in_app_iff in ABS as [ABS1 | ABS2]; try contradiction;
                 try eapply in_domain_in_g in ABS2 as
                   (ff &tt &ABS2);
                 try eapply no_dup_iff.
               assert (~ In (b1, b2, ff, tt) (removeEntry (b1, b2) g0)).
               eapply no_dup_not_in_removeEntry...
               contradiction.
               rewrite domain_distr,no_dup_iff in *; intuition; try eapply disjoint_eqd_removeEntry...

               eapply split_comm.

               (* tEnv_split (ne ++ (b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0) 
    (ne3 ++ g3) (ne1 ++ (c1, c2, fc, tc) :: removeEntry (c1, c2) g1) 
    ?pf213 pfk2 pfk1*)

                assert (ND1: NoDup (domain (ne1 ++ g1))).
               rewrite domain_distr,no_dup_iff; repeat split.
               subst ne1; try eapply newEntries_no_dup.
               eapply wf_rewrite,prop27,incl_incl2.
               eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
               eauto.
               eapply incl_tran with (m := secLabs p1)...
               eapply incl_iff with (m1 := (domain g0)).
               eapply typeCheck_no_dup with (pf := pf0)...
               intros; eapply split_domain_r, split_comm...
               eauto. eauto.
               subst; eapply disjoint_commute, new_entries_disjoint.
               unfold sl_pos, pos in *; intros.
               specialize SLP with x1 x2;
                 unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL0; specialize INCL0 with (x1,x2); intuition.
               eapply incl_preserves_max, incl_tran with (m := secLabs p1)...
               assert (INCL2: incl (secLabs p1) (domain g0))...
               eapply typeCheck_no_dup with (pf := pf0)...
               eapply incl_iff...

               assert (TS1 := H1).
               assert (PF0:= ND0).
               eapply no_dup_isMap in PF0; rewrite NEEQ0 in PF0.
               assert (PF1:= ND1).
               eapply no_dup_isMap in PF1;
                 rewrite NEEQ1 in PF1.
               eapply split_newEntries
                 with (p:=q)
                      (nd_pf1 := nd_pf0)
                      (nd_pf2 := nd_pf3)
                      (nd_pf := nd_pf1)
                 in H1 as TSN; try eassumption.
               
               eapply split_comm,split_iff2 with
                 (g2 := ne ++ g0); try eassumption.

               eapply split_comm,split_iff with (g := ne1 ++ g1);
                 try eassumption.

               eapply split_distr.
               subst; eapply split_pf; try eassumption.
               eauto.

               (*forall x : name * name * flag * piType,
  In x (ne1 ++ g1) <-> In x (ne1 ++ (c1, c2, fc, tc) :: removeEntry (c1, c2) g1)*)
               eapply Permutation_iff,Permutation.Permutation_app_head,Permutation.NoDup_Permutation; try eapply no_dup_g; try eapply no_dup_cons_removeEntry;
                 try eassumption.
               intros; rewrite <-in_removeEntry_cons_iff_0...
               tauto.

               (* forall x : name * name * flag * piType,
  In x (ne ++ g0) <-> In x (ne ++ (b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0)*)
               
               eapply Permutation_iff,Permutation.Permutation_app_head,Permutation.NoDup_Permutation; try eapply no_dup_g; try eapply no_dup_cons_removeEntry;
                 try eassumption.
               intros; rewrite <-in_removeEntry_cons_iff_0...
               tauto.

               (* forall x : name * name * flag * piType,
  In x (ne ++ g0) <-> In x (ne ++ (b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0)*)
               
               eapply Permutation_iff,
                 Permutation.Permutation_sym,
                 Permutation.Permutation_middle.

               (*  typeCheck k0 pfk0 p2 *)
               eapply IHLTS...

               (* typeCheck (ne3 ++ g3) pfk2 p3*)
               eapply typeCheck_weak2;
                 try rewrite domain_distr in *;
                 try eassumption.
               apply Peirce; intros ABS;
                 eapply gcons_abs
                 in ABS
                   as (x1 &x2 &ff &pp &tt &ABS &NEEMPTY).
               assert (INCLH:
                        incl (secLabs q) (domain (hid_proj g0))).
               eapply incl_tran...
              rewrite Heqne3, identif_seclabs_of_dep_relabel
                in ABS;
                try eapply inverse_newEntries
                in ABS
                  as [ABS1 ABS2].
                try eapply INCLH,hid_proj_flagOf in ABS1.
                inv ABS1.
                remember (max (domain g3)) as M.
                assert (FYP: flagOf g3 (x1, x2 - M) ill).
                eapply finv_hid_r;
                  try eapply split_comm;
                  try eassumption.
                inv FYP.
                assert (EQ: ff = ill /\ Chan lin pp tt = t1).
                eapply in_isMap with (g := g3)...
                destruct EQ; subst.
                eapply typeCheck_ill
                  in ABS2
                    as [ABS' | [(t' &ABS'') |
                                 (p' &t' &ABS''')]];
                  subst;
                  try inv ABS'';
                  try discriminate;
                  try contradiction.

                eauto.
                eauto.
                eauto.
                unfold sl_pos, pos in *; intros.
                specialize SLP with x0 x3;
                  unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL0; specialize INCL0 with (x0,x3); intuition.
                eapply incl_tran with (m := secLabs p1)...
                assert (INCL2: incl (secLabs p1) (domain g0))...
                eapply typeCheck_no_dup with (pf := pf0)...
                eapply incl_iff with (m1 := domain g0);
                  try eassumption.
                intros. eapply split_domain_m...

                subst ne3;
                  rewrite identif_seclabs_of_dep_relabel in *;
                  eapply Peirce; intros ABS;
                  eapply not_disjoint in ABS as ([x1 x2] &ABS1 &ABS2);
                  eapply in_bv_lt_max with (pf := pf3) in ABS1;
                  eapply in_domain_in_g in ABS2 as (ff &tt &ABS2);
                  eapply newEntries_gte_max in ABS2;
                  try lia;
                  try eassumption.

          (***) (* typeCheck
    ((c1, c2, hid, tc)
     :: removeEntry (c1, c2) (nil ++ (c1, c2, vis, tc) :: removeEntry (c1, c2) g1)) pfk1
    (dPar p2 p3)  *)
             eapply TPar with (g2 := g3) (pf1 := pfk0);
                try eassumption.
              destruct EQK0 as [(EQK0 &DIFF0)| (EQK0 &DIFF0)];
            destruct NEEQ as [NEEQ0 | REPL0]; subst k0.

              subst ne; simpl.
              eapply split_iff with (pf := pf1);
                try eassumption.
              eapply split_comm.
              eapply split_iff2 with (pf2 := pf0);
                try eassumption.
              eapply split_comm...
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.
              intros; try rewrite in_removeEntry_cons_iff_0...
              rewrite pairEq_eq_true.
              tauto.

              destruct REPL0 as (q &REPL0 &INCL0 &NEEQ0).

              assert (ne = nil).
              destruct ne; try tauto.
              
              eapply lts_un_tau_action_newEntries_1hk in LTS1;
                try eassumption.
              assert (EQSL:  secLabs (dep_relabel q (domain g1) nd_pf1) =
                         secLabs (dep_relabel q (domain g0) nd_pf0)).
              repeat rewrite identif_seclabs_of_dep_relabel.
              erewrite max_same_domain...
              rewrite EQSL,LTS1,newEntries_nil_nil in *;
                try discriminate...
              
              assert (TC1 := H2).
              eapply typeCheck_hid_proj in TC1;
                try eapply incl_tran,split_incl_hid_proj...
              eapply typeCheck_no_dup in H2 as (_ &IH')...
              assert (TMP := IN0a);
                eapply tsub_un with (g := g1) in TMP;
                try inv TMP.
              assert (flagOf g1 (a1,a2) hid).
              eapply fsub_hid...
              inv H0.
              assert (f = hid).
              eapply flag_of_map with (g := g1)...
              subst...
              eauto.
              eauto.

            
              
              subst ne; gen pfk0; simpl; rewrite H in *; simpl; introv TC'.
              try eapply split_iff with (pf := pf1);
                try eassumption.
              eapply split_comm.
              eapply split_iff2 with (pf2 := pf0);
                try eassumption.
              eapply split_comm...
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.
              intros; try rewrite in_removeEntry_cons_iff_0...
              rewrite pairEq_eq_true.
              tauto.

              

              
              subst ne; gen pfk0; simpl; try rewrite pairEq_eq_true; introv TC'.
              eapply split_iff with (pf := pf1); try eassumption.
              eapply split_comm.
              eapply split_iff2 with (pf2 := pf0);
                try eassumption.
              eauto.
              eapply split_comm...
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.
              intros; try rewrite in_removeEntry_cons_iff_0...
              try rewrite pairEq_eq_true.
              tauto.

               destruct REPL0 as (q &REPL0 &INCL0 &NEEQ0).

              assert (ne = nil).
              destruct ne; try tauto.

              
              eapply lts_un_tau_action_newEntries_1hk in LTS1;
                try eassumption.

               assert (EQSL:  secLabs (dep_relabel q (domain g1) nd_pf1) =
                         secLabs (dep_relabel q (domain g0) nd_pf0)).
              repeat rewrite identif_seclabs_of_dep_relabel.
              erewrite max_same_domain...
              rewrite EQSL,LTS1,newEntries_nil_nil in *;
                try discriminate...

               assert (TC1 := H2).
              eapply typeCheck_hid_proj in TC1;
                try eapply incl_tran,split_incl_hid_proj...
              eapply typeCheck_no_dup in H2 as (_ &IH')...
              assert (TMP := IN0a);
                eapply tsub_un with (g := g1) in TMP;
                try inv TMP.
              assert (flagOf g1 (a1,a2) hid).
              eapply fsub_hid...
              inv H0.
              assert (f = hid).
              eapply flag_of_map with (g := g1)...
              subst...
              eauto.
              eauto.

              subst ne; gen pfk0; simpl; rewrite H in *; simpl;
                try rewrite pairEq_eq_true; introv TC'.
              try eapply split_iff with (pf := pf1);
                try eassumption.
              eapply split_comm.
              eapply split_iff2 with (pf2 := pf0);
                try eassumption.
              eauto.
              eapply split_comm...
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.
              intros; try rewrite in_removeEntry_cons_iff_0...
              try rewrite pairEq_eq_true.
              tauto.

(*              eauto. *)

              
          (***)
            destruct REPL1 as (q &REPL1 &INCL1 &NEEQ1).
            remember (newEntries g3 (secLabs (dep_relabel q (domain g3) nd_pf3)) (max (domain g3))) as ne3.
            assert
              (nd_pfk2 :
                NoDup(domain (ne3 ++ g3))).
            assert (TC1 := H2).
            eapply typeCheck_no_dup in TC1 as [INCL0 ND1].
            assert (INCL1': incl (secLabs p1) (domain g3)).
            eapply incl_iff; try eassumption.
            intros; eapply split_domain_m...
            subst ne3; try rewrite domain_distr;
              try eapply no_dup_iff; repeat split;
              try eapply disjoint_commute;
              try eapply new_entries_disjoint;
              try eapply sl_pos_repl;
              try eapply incl_preserves_max,incl_tran;
              try eapply newEntries_no_dup;
              try eapply prop27;
              try eapply incl_incl2,incl_tran;
              try eapply replication_no_dup;
              try eassumption.
            assumption.
            assert (ND3 := nd_pfk2).
            assert (NIN3:   ~ In (b1, b2) (domain ne3)).
            rewrite domain_distr in ND3;
              eapply no_dup_iff in ND3 as (ND1 &ND3 &DIS3).
            intros ABS;
              try eapply disjoint_absurd...
            
            eapply no_dup_isMap in nd_pfk2 as pfk2.
            destruct NEEQ as [NIL0 | REPL0].
            eapply TPar with (pf1 := pfk0) (pf2 := pf3);
              try eassumption.

            subst ne.

            assert (ne1 = nil).
            destruct ne1; try tauto.
            destruct EQK0 as [(EQ0 &DIFF0) |(EQ0 &DIFF0)];
              subst k0.
            destruct fb0.

             move LTS0 at bottom.
              simpl in LTS0.
              assert (REM:
                       removeEntry (b1, b2) g0 =
                         removeEntry (b1, b2) (nil ++ (b1, b2, vis, tb0):: removeEntry (b1, b2)g0)).
              simpl; rewrite pairEq_eq_true...

              gen nd_pf0; rewrite REM; intros.
              
              eapply lts_un_tau_action_newEntries_1hk in LTS0;
                try eassumption.

               assert (EQSL:  secLabs (dep_relabel q (domain g1) nd_pf1) =
                         secLabs (dep_relabel q (domain g0) nd_pf0)).
              repeat rewrite identif_seclabs_of_dep_relabel.
              erewrite max_same_domain...
              rewrite EQSL,LTS0,newEntries_nil_nil in *;
                try discriminate...

               assert (TC1 := H2).
              eapply typeCheck_hid_proj in TC1...
              eapply typeCheck_no_dup in H2 as (_ &IH')...
              eauto.
              eauto.

              contradiction.

              
              eapply lts_un_tau_action_newEntries_1k in LTS0;
                try eassumption.

               assert (EQSL:  secLabs (dep_relabel q (domain g1) nd_pf1) =
                         secLabs (dep_relabel q (domain g0) nd_pf0)).
              repeat rewrite identif_seclabs_of_dep_relabel.
              erewrite max_same_domain...
              rewrite EQSL,LTS0,newEntries_nil_nil in *;
                try discriminate...

               assert (TC1 := H2).
              eapply typeCheck_hid_proj in TC1...
              eapply typeCheck_no_dup in H2 as (_ &IH')...
              eauto.
              eauto.

              subst fb0.
              move LTS0 at bottom.

            
              try eapply lts_un_tau_action_newEntries_1hk in LTS0;
              try eassumption.
            assert (EQSL:  secLabs (dep_relabel q (domain g1) nd_pf1) =
                             secLabs (dep_relabel q (domain g0) nd_pf0)).
            repeat rewrite identif_seclabs_of_dep_relabel.
            erewrite max_same_domain...
            rewrite EQSL,LTS0,newEntries_nil_nil in *;
              try discriminate...
             assert (TC1 := H2).
              eapply typeCheck_hid_proj in TC1...
              eapply typeCheck_no_dup in H2 as (_ &IH')...
              eauto.
              eauto.


              subst.

              
              
                destruct EQK0 as [(EQ0 &DIFF0) |(EQ0 &DIFF0)];
                  subst k0;gen pfk1; try rewrite H; simpl;introv.

                try eapply split_iff with (pf := pf1);
                  try eassumption.
                try rewrite pairEq_eq_true.
                eauto.
              eapply split_comm.
              eapply split_iff2 with (pf2 := pf0);
                try eassumption.
              eapply split_comm...
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.
              intros; try rewrite in_removeEntry_cons_iff_0...
              try rewrite pairEq_eq_true...
              tauto.

              gen pfk0; simpl; rewrite pairEq_eq_true; simpl; introv TC'.

              try eapply split_iff with (pf := pf1); try eassumption.
              try rewrite pairEq_eq_true... 
              eapply split_comm.
              eapply split_iff2 with (pf2 := pf0); try eassumption.
              eauto.
              eapply split_comm...
              intros; try rewrite in_removeEntry_cons_iff_0...
              tauto.
              intros; try rewrite in_removeEntry_cons_iff_0...
              try rewrite pairEq_eq_true.
              tauto.
              (*eauto.*)

               destruct REPL0 as (q' &REPL0 &INCL0 &NEEQ0).
               assert (q = q').
               eapply replication_unique...
               subst q'.
               move NEEQ0 at bottom.

        (*typeCheck (ne1 ++ (c1, c2, fc, tc) :: removeEntry (c1, c2) g1) pfk1 (dPar p2 p3)*)
               eapply TPar with (pf1 := pfk0) (pf2 := pfk2).

               (* tEnv_split k0 (ne3 ++ g3) (ne1 ++ (c1, c2, fc, tc) :: removeEntry (c1, c2) g1) pfk0 pfk2
    pfk1*)
               destruct EQK0 as
                 [(K0EQ &NILL) | (KOEQ1 &HID)];
                 subst k0.

               (*tEnv_split (ne ++ (b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0) 
    (ne3 ++ g3) (ne1 ++ (c1, c2, fc, tc) :: removeEntry (c1, c2) g1) pfk0 pfk2 pfk1*)
               
               assert (ND0: NoDup (domain (ne ++ g0))).
               rewrite domain_distr,no_dup_iff; repeat split.
               subst ne; try eapply newEntries_no_dup.
               eapply wf_rewrite,prop27,incl_incl2.
               eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
               eauto.
               eapply incl_tran with (m := secLabs p1)...
               eapply incl_iff with (m1 := (domain g0)).
               eapply typeCheck_no_dup with (pf := pf0)...
               intros; tauto. eauto. eauto.
               subst; eapply disjoint_commute, new_entries_disjoint.
               unfold sl_pos, pos in *; intros.
               specialize SLP with x1 x2;
                 unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL0; specialize INCL0 with (x1,x2); intuition.
               eapply incl_preserves_max, incl_tran with (m := secLabs p1)... 
               eapply typeCheck_no_dup with (pf := pf0)...
               
               
               assert (ND1: NoDup (domain (ne1 ++ g1))).
               rewrite domain_distr,no_dup_iff; repeat split.
               subst ne1; try eapply newEntries_no_dup.
               eapply wf_rewrite,prop27,incl_incl2.
               eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
               eauto.
               eapply incl_tran with (m := secLabs p1)...
               eapply incl_iff with (m1 := (domain g0)).
               eapply typeCheck_no_dup with (pf := pf0)...
               intros; eapply split_domain_r, split_comm...
               eauto. eauto.
               subst; eapply disjoint_commute, new_entries_disjoint.
               unfold sl_pos, pos in *; intros.
               specialize SLP with x1 x2;
                 unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL0; specialize INCL0 with (x1,x2); intuition.
               eapply incl_preserves_max, incl_tran with (m := secLabs p1)...
               assert (INCL2: incl (secLabs p1) (domain g0))...
               eapply typeCheck_no_dup with (pf := pf0)...
               eapply incl_iff...

               assert (TS1 := H1).
               assert (PF0:= ND0).
               eapply no_dup_isMap in PF0; rewrite NEEQ0 in PF0.
               assert (PF1:= ND1).
               eapply no_dup_isMap in PF1;
                 rewrite NEEQ1 in PF1.
               eapply split_newEntries
                 with (p:=q)
                      (nd_pf1 := nd_pf0)
                      (nd_pf2 := nd_pf3)
                      (nd_pf := nd_pf1)
                 in H1 as TSN; try eassumption.
               
               eapply split_comm,split_iff2 with
                 (g2 := ne ++ g0); try eassumption.

               eapply split_comm,split_iff with (g := ne1 ++ g1);
                 try eassumption.

               eapply split_distr.
               subst; eapply split_pf; try eassumption.
               eauto.

               (* forall x : name * name * flag * piType,
  In x (ne1 ++ g1) <->
  In x
    ((c1, c2, hid, tc)
     :: removeEntry (c1, c2) (ne1 ++ (c1, c2, vis, tc) :: removeEntry (c1, c2) g1))*)

               rewrite removeEntry_app_shift;
                 unfold removeEntry; fold removeEntry;
                 try rewrite pairEq_eq_true.

               assert (IFF2: forall x, In x ((c1, c2, hid, tc) :: ne1 ++ removeEntry (c1, c2) g1) <->
                                         In x ( ne1 ++ (c1, c2, hid, tc) ::removeEntry (c1, c2) g1)).
               eapply Permutation_iff,Permutation.Permutation_middle.
               intros; rewrite IFF2.
               assert (IFF3:
                        In x (ne1 ++ (c1, c2, hid, tc) :: removeEntry (c1, c2) g1) <-> In x (ne1 ++ g1)).
               rewrite in_app_iff.
               rewrite <-in_removeEntry_cons_iff_0,<-in_app_iff...
               tauto.
               rewrite <-IFF3.
               tauto.

               intros ABS.
               
               assert (DIS: disjoint (domain g1) (domain ne1)).
               subst ne1; eapply new_entries_disjoint;
                 try eapply sl_pos_repl;
                 try eapply sl_pos_par_l;
                 try eassumption.
               eapply incl_preserves_max, incl_tran;
                 try eapply secLabs_of_repl...
               eapply incl_iff with (m1 := domain g0);
                 try eapply typeCheck_no_dup...
               eapply disjoint_absurd...
               
               (* forall x : name * name * flag * piType,
  In x (ne ++ g0) <-> In x (ne ++ (b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0)*)
               
               eapply Permutation_iff,Permutation.Permutation_app_head,Permutation.NoDup_Permutation; try eapply no_dup_g; try eapply no_dup_cons_removeEntry;
                 try eassumption.
               intros; rewrite <-in_removeEntry_cons_iff_0...
               tauto.

               (* tEnv_split
    ((b1, b2, fb0, tb0)
     :: removeEntry (b1, b2) (ne ++ (b1, b2, vis, tb0) :: removeEntry (b1, b2) g0))
    (ne3 ++ g3) (ne1 ++ (c1, c2, fc, tc) :: removeEntry (c1, c2) g1) pfk0 pfk2 pfk1 *)

               
               assert (DIS: disjoint (domain g0) (domain ne) ).
               subst ne; eapply new_entries_disjoint.
                unfold sl_pos, pos in *; intros.
               specialize SLP with x1 x2;
                 unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL0; specialize INCL0 with (x1,x2); intuition.
               eapply incl_preserves_max, incl_tran with (m := secLabs p1)...
               assert (INCL2: incl (secLabs p1) (domain g0))...
               eapply typeCheck_no_dup with (pf := pf0)...

               assert (ND0: NoDup (domain (ne ++ g0))).
               rewrite domain_distr,no_dup_iff; repeat split.
               subst ne; try eapply newEntries_no_dup.
               eapply wf_rewrite,prop27,incl_incl2.
               eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
               eauto.
               eapply incl_tran with (m := secLabs p1)...
               eapply incl_iff with (m1 := (domain g0)).
               eapply typeCheck_no_dup with (pf := pf0)...
               intros; tauto.
               eauto. eauto. eapply disjoint_commute... 

               assert (NIN:
                        In (b1, b2) (domain ne) -> False).
               intros ABS.
               eapply disjoint_absurd...

               
               
               gen pfk0.
               rewrite removeEntry_app_shift;
                 try eassumption;
                 simpl;
                 try rewrite pairEq_eq_true;
                 introv TC'.

               assert (ND0':
                        NoDup (domain (ne ++ (b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0))).
               rewrite domain_distr in *; simpl in *; rewrite no_dup_iff in *; repeat split.
               intuition.
               eapply no_dup_cons_removeEntry; intuition.
               eapply disjoint_commute,disjoint_iff with (l1 := domain g0);
                 try eapply disjoint_commute.
               intuition.
               intros. try rewrite in_removeEntry_cons_iff with (b1 := b1) (b2 := b2) (f := ill) (t := Top);
                 unfold domain; fold domain; try tauto.
               eauto.

               eapply split_comm,split_iff2
                 with (g2 :=
                         ne ++ (b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0); try eassumption.

               simpl;rewrite domain_distr; econstructor;
                 try intros ABS; try eapply in_app_iff in ABS as [ABS1 | ABS2]; try contradiction;
                 try eapply in_domain_in_g in ABS2 as
                   (ff &tt &ABS2);
                 try eapply no_dup_iff.
               assert (~ In (b1, b2, ff, tt) (removeEntry (b1, b2) g0)).
               eapply no_dup_not_in_removeEntry...
               contradiction.
               rewrite domain_distr,no_dup_iff in *; intuition; try eapply disjoint_eqd_removeEntry...

               eapply split_comm.

               (* tEnv_split (ne ++ (b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0) 
    (ne3 ++ g3) (ne1 ++ (c1, c2, fc, tc) :: removeEntry (c1, c2) g1) 
    ?pf213 pfk2 pfk1*)

                assert (ND1: NoDup (domain (ne1 ++ g1))).
               rewrite domain_distr,no_dup_iff; repeat split.
               subst ne1; try eapply newEntries_no_dup.
               eapply wf_rewrite,prop27,incl_incl2.
               eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf0)...
               eauto.
               eapply incl_tran with (m := secLabs p1)...
               eapply incl_iff with (m1 := (domain g0)).
               eapply typeCheck_no_dup with (pf := pf0)...
               intros; eapply split_domain_r, split_comm...
               eauto. eauto.
               subst; eapply disjoint_commute, new_entries_disjoint.
               unfold sl_pos, pos in *; intros.
               specialize SLP with x1 x2;
                 unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL0; specialize INCL0 with (x1,x2); intuition.
               eapply incl_preserves_max, incl_tran with (m := secLabs p1)...
               assert (INCL2: incl (secLabs p1) (domain g0))...
               eapply typeCheck_no_dup with (pf := pf0)...
               eapply incl_iff...

               assert (TS1 := H1).
               assert (PF0:= ND0).
               eapply no_dup_isMap in PF0; rewrite NEEQ0 in PF0.
               assert (PF1:= ND1).
               eapply no_dup_isMap in PF1;
                 rewrite NEEQ1 in PF1.
               eapply split_newEntries
                 with (p:=q)
                      (nd_pf1 := nd_pf0)
                      (nd_pf2 := nd_pf3)
                      (nd_pf := nd_pf1)
                 in H1 as TSN; try eassumption.
               
               eapply split_comm,split_iff2 with
                 (g2 := ne ++ g0); try eassumption.

               eapply split_comm,split_iff with (g := ne1 ++ g1);
                 try eassumption.

               eapply split_distr.
               subst; eapply split_pf; try eassumption.
               eauto.

              
               (* forall x : name * name * flag * piType,
  In x (ne1 ++ g1) <->
  In x
    ((c1, c2, hid, tc)
     :: removeEntry (c1, c2) (ne1 ++ (c1, c2, vis, tc) :: removeEntry (c1, c2) g1))*)

               rewrite removeEntry_app_shift;
                 unfold removeEntry; fold removeEntry;
                 try rewrite pairEq_eq_true.

               assert (IFF2: forall x, In x ((c1, c2, hid, tc) :: ne1 ++ removeEntry (c1, c2) g1) <->
                                         In x ( ne1 ++ (c1, c2, hid, tc) ::removeEntry (c1, c2) g1)).
               eapply Permutation_iff,Permutation.Permutation_middle.
               intros; rewrite IFF2.
               assert (IFF3:
                        In x (ne1 ++ (c1, c2, hid, tc) :: removeEntry (c1, c2) g1) <-> In x (ne1 ++ g1)).
               rewrite in_app_iff.
               rewrite <-in_removeEntry_cons_iff_0,<-in_app_iff...
               tauto.
               rewrite <-IFF3.
               tauto.

               intros ABS.
               
               assert (DIS2: disjoint (domain g1) (domain ne1)).
               subst ne1; eapply new_entries_disjoint;
                 try eapply sl_pos_repl;
                 try eapply sl_pos_par_l;
                 try eassumption.
               eapply incl_preserves_max, incl_tran;
                 try eapply secLabs_of_repl...
               eapply incl_iff with (m1 := domain g0);
                 try eapply typeCheck_no_dup...
               eapply disjoint_absurd...

               (* forall x : name * name * flag * piType,
  In x (ne ++ g0) <-> In x (ne ++ (b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0)*)
               
               eapply Permutation_iff,Permutation.Permutation_app_head,Permutation.NoDup_Permutation; try eapply no_dup_g; try eapply no_dup_cons_removeEntry;
                 try eassumption.
               intros; rewrite <-in_removeEntry_cons_iff_0...
               tauto.

               (* forall x : name * name * flag * piType,
  In x (ne ++ g0) <-> In x (ne ++ (b1, b2, fb0, tb0) :: removeEntry (b1, b2) g0)*)
               
               eapply Permutation_iff,
                 Permutation.Permutation_sym,
                 Permutation.Permutation_middle.

               (*  typeCheck k0 pfk0 p2 *)
               eapply IHLTS...

               (* typeCheck (ne3 ++ g3) pfk2 p3*)
               eapply typeCheck_weak2;
                 try rewrite domain_distr in *;
                 try eassumption.
               apply Peirce; intros ABS;
                 eapply gcons_abs
                 in ABS
                   as (x1 &x2 &ff &pp &tt &ABS &NEEMPTY).
               assert (INCLH:
                        incl (secLabs q) (domain (hid_proj g0))).
               eapply incl_tran...
              rewrite Heqne3, identif_seclabs_of_dep_relabel
                in ABS;
                try eapply inverse_newEntries
                in ABS
                  as [ABS1 ABS2].
                try eapply INCLH,hid_proj_flagOf in ABS1.
                inv ABS1.
                remember (max (domain g3)) as M.
                assert (FYP: flagOf g3 (x1, x2 - M) ill).
                eapply finv_hid_r;
                  try eapply split_comm;
                  try eassumption.
                inv FYP.
                assert (EQ: ff = ill /\ Chan lin pp tt = t1).
                eapply in_isMap with (g := g3)...
                destruct EQ; subst.
                eapply typeCheck_ill
                  in ABS2
                    as [ABS' | [(t' &ABS'') |
                                 (p' &t' &ABS''')]];
                  subst;
                  try inv ABS'';
                  try discriminate;
                  try contradiction.

                eauto.
                eauto.
                eauto.
                unfold sl_pos, pos in *; intros.
                specialize SLP with x0 x3;
                  unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL0; specialize INCL0 with (x0,x3); intuition.
                eapply incl_tran with (m := secLabs p1)...
                assert (INCL2: incl (secLabs p1) (domain g0))...
                eapply typeCheck_no_dup with (pf := pf0)...
                eapply incl_iff with (m1 := domain g0);
                  try eassumption.
                intros. eapply split_domain_m...

                subst ne3;
                  rewrite identif_seclabs_of_dep_relabel in *;
                  eapply Peirce; intros ABS;
                  eapply not_disjoint in ABS as ([x1 x2] &ABS1 &ABS2);
                  eapply in_bv_lt_max with (pf := pf3) in ABS1;
                  eapply in_domain_in_g in ABS2 as (ff &tt &ABS2);
                  eapply newEntries_gte_max in ABS2;
                  try lia;
                  try eassumption.

                eauto.
                assert (INCLH: incl (secLabs (dPar p1 p3)) (domain (hid_proj g1))).
                eapply typeCheck_hid_proj...
                simpl in INCLH. eapply incl_app_inv...
                eapply typeCheck_no_dup with (pf := pf0)...
                assert (IN := IN0a).
                eapply tsub_un with (g := g1) in IN0a; try inv IN0a;
                  try eassumption.
                eapply fsub_hid with (g := g1) in IN;
                   try inv IN;
                  try eassumption.
                assert (f = hid).
                eapply flag_of_map with (g := g1)...
                subst...
                eauto.
                eapply typeCheck_hid_proj...
                eapply typeCheck_no_dup with (pf := pf0)...
                assumption.

        (*        
        (**) eapply sl_pos_par_l in SLP...
        (**) (* incl (secLabs p1) (domain (hid_proj g1))*)
        eapply typeCheck_hid_proj_par...
        (**) eapply typeCheck_no_dup with (g := g0)...
        (**) eapply tsub_un with (pf := pf1) in IN0a as INa. inversion INa; subst; clear INa.
        eapply fsub_vis with (pf := pf1) in IN0a as INa. 
        assert (f = vis). eapply flag_of_map with (g := g1)...
        subst...
        eauto.
        eauto.

        (**) eapply sl_pos_par_l in SLP...
        (* incl (secLabs p1) (domain (hid_proj g1))*)
        (**) eapply typeCheck_hid_proj...
        (**) eapply typeCheck_no_dup with (g := g0)...
        (**) eauto.
         *)












                

           Unshelve.
           
           all:
             subst;
             try match goal with
               | [ H : isMap (?l ++ _) |- isMap (?l) ] =>
                   try eapply isMap_distr  in H as [K _];
                   try eassumption
               | [ H : NoDup (domain (?l ++ _)) |- isMap (?l) ] =>
                   try rewrite domain_distr,no_dup_iff in H;
                   try eapply no_dup_isMap;
                   intuition
               | [ _ : _  |- isMap (newEntries _ _ _) ] =>
                   try eapply no_dup_isMap,newEntries_no_dup;
                   try eapply prop27, incl_incl2;
                   try eapply replication_no_dup;
                   try eapply incl_tran;
                   try eassumption
               | [ _ : _ |- isMap (_ :: removeEntry _ _)] =>
                   eapply  no_dup_isMap,no_dup_cons_removeEntry;
                   try eassumption
               | [ _ : _ |- isMap (removeEntry _ _)] =>
                   eapply  no_dup_isMap,no_dup_removeEntry_no_dup;
                   try eassumption
               | [ _ : _  |- isMap (_ ++ _ :: _) ] =>
                  (* try eapply isMap_change_flag;*)
                   try eauto
               end
           ;
             try match goal with
                  | [ _ : _ |- NoDup (secLabs _)] =>
                      try eapply typeCheck_no_dup with (pf := pf0);
                      eauto
               | [ _ : _ |- incl (secLabs _) _ ] =>
                     try eapply incl_iff with (m1 := domain g0); try eapply typeCheck_no_dup with (pf := pf0);
                 intros;
                 try eapply split_domain_m;
                 try eassumption
               end
           ;
             try eassumption.

           

           eauto.
           
           (*NoDup (domain (ne ++ (b1, b2, vis, tb0) :: removeEntry (b1, b2) g0))
            *)
           move nd_pfk0 at bottom;
             simpl in nd_pfk0; rewrite domain_distr; simpl.
           assert (~In (b1, b2) (domain ne)).
           intros ABS.
           rewrite removeEntry_app_shift2 in   nd_pfk0;
             simpl in nd_pfk0; eapply NoDup_cons_iff in nd_pfk0 as [K1 K2].
           assert (
               In (b1, b2)
                 (domain (removeEntry (b1, b2) ne ++ (b1, b2, vis, tb0) :: removeEntry (b1, b2) g0))).
           rewrite domain_distr,in_app_iff; right.
           unfold domain; fold domain...
           contradiction.
           assumption.
           rewrite removeEntry_app_shift in   nd_pfk0;
             unfold removeEntry in nd_pfk0;
             fold removeEntry in *;
             try rewrite pairEq_eq_true in nd_pfk0;
             try rewrite domain_distr in nd_pfk0.
           eapply Permutation.Permutation_NoDup;
             try eapply Permutation.Permutation_middle;
             try eassumption.
           assumption.
            (*NoDup (domain (ne ++ (b1, b2, vis, tb0) :: removeEntry (b1, b2) g0))
            *)
           move nd_pfk0 at bottom;
             simpl in nd_pfk0; rewrite domain_distr; simpl.
           assert (~In (b1, b2) (domain ne)).
           intros ABS.
           rewrite removeEntry_app_shift2 in   nd_pfk0;
             simpl in nd_pfk0; eapply NoDup_cons_iff in nd_pfk0 as [K1 K2].
           assert (
               In (b1, b2)
                 (domain (removeEntry (b1, b2) ne ++ (b1, b2, vis, tb0) :: removeEntry (b1, b2) g0))).
           rewrite domain_distr,in_app_iff; right.
           unfold domain; fold domain...
           contradiction.
           assumption.
           rewrite removeEntry_app_shift in   nd_pfk0;
             unfold removeEntry in nd_pfk0;
             fold removeEntry in *;
             try rewrite pairEq_eq_true in nd_pfk0;
             try rewrite domain_distr in nd_pfk0.
           eapply Permutation.Permutation_NoDup;
             try eapply Permutation.Permutation_middle;
             try eassumption.
           assumption.
            (*NoDup (domain (ne ++ (b1, b2, vis, tb0) :: removeEntry (b1, b2) g0))
            *)
           move nd_pfk0 at bottom;
             simpl in nd_pfk0; rewrite domain_distr; simpl.
           assert (~In (b1, b2) (domain ne)).
           intros ABS.
           rewrite removeEntry_app_shift2 in   nd_pfk0;
             simpl in nd_pfk0; eapply NoDup_cons_iff in nd_pfk0 as [K1 K2].
           assert (
               In (b1, b2)
                 (domain (removeEntry (b1, b2) ne ++ (b1, b2, vis, tb0) :: removeEntry (b1, b2) g0))).
           rewrite domain_distr,in_app_iff; right.
           unfold domain; fold domain...
           contradiction.
           assumption.
           rewrite removeEntry_app_shift in   nd_pfk0;
             unfold removeEntry in nd_pfk0;
             fold removeEntry in *;
             try rewrite pairEq_eq_true in nd_pfk0;
             try rewrite domain_distr in nd_pfk0.
           eapply Permutation.Permutation_NoDup;
             try eapply Permutation.Permutation_middle;
             try eassumption.
           assumption.

          
           try rewrite domain_distr in *;
             try rewrite no_dup_iff in *;
             try eapply no_dup_isMap;
             intuition.

           try rewrite domain_distr in *;
             try rewrite no_dup_iff in *;
             try eapply no_dup_isMap;
             intuition.
           
           eauto.

           all:try rewrite domain_distr in *;
             try rewrite no_dup_iff in *;
             try eapply no_dup_isMap;
             intuition.









           
        
           
      + assert (incl (secLabs p1) (domain g0) /\
                NoDup (secLabs p1)).
        eapply typeCheck_no_dup...
        intuition.
        apply incl_incl2;
        try eapply typeCheck_no_dup with (pf := pf1)...
      + assert (incl (secLabs p1) (domain g0) /\
                NoDup (secLabs p1)).
        eapply typeCheck_no_dup...
        intuition.
        try eapply typeCheck_no_dup with (pf := pf1)...
      + assert (incl (secLabs (dPar p1 p3)) (domain  g1)).
        eapply typeCheck_no_dup...
        eapply incl_preserves_max...
      + assert (incl (secLabs p1) (domain g0) /\
                NoDup (secLabs p1)).
        eapply typeCheck_no_dup...
        intuition.
        eapply incl_incl2...
      + eapply typeCheck_no_dup with (pf := pf0)...
      + assert (max (domain g0) >= max (secLabs p1)).
        eapply incl_preserves_max...
        eapply typeCheck_no_dup...
        lia.
      + inversion LTSPAR. assumption.
        apply lts_finite in H13.
        contradiction.
        apply lts_finite in H12.
        contradiction.
        
    - Case lOut. 
       intros. inversion TYP. subst.
      destruct u as [a1 a2];
        destruct v as [b1 b2];
        simpl in AFT, H0, H1, SLP, TYP.
      eapply tsuper_payload with (pf1 := pf1) in H0 as K0.
      destruct K0 as [pp1 TYP1].
      inversion TYP1; subst.
      assert (vis = f /\ Chan lin p0 t0 =  Chan lin pp1 t).
      eapply in_isMap... intuition. inversion H5; subst.
      assert (k1 = ((a1, a2, vis, Chan lin empty t)
                      :: (b1, b2, vis, t4) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1))).
      eapply lts_lin_output_action.
      eauto. 
      apply T_Entry with (f := vis).
      instantiate (1 := pp1)...
      eauto. eauto.
      erewrite removeEntry_swap in H3.
      assert (TEQ: t3 =  Chan lin empty t).
      inversion H7. destruct H6. inversion H6. inversion H16.
      subst... subst. eapply tsub_io with (g := g) in H2.
      inversion H2. subst.
      assert (vis = f /\ Chan lin out t = Chan lin io t).
      apply in_isMap with (x := (a1, a2)) (g := g)...
      intuition. inversion H15.
      eauto. subst t3.
      revert dependent pf3.
      rewrite <-H3. intuition.
      eapply typeCheck_rewrite_pf...
      eapply nonRecActions2...
      eauto.

      eapply tsuper_payload with (pf1 := pf1) in H0 as K0.
      destruct K0 as [pp1 TYP1].
      inversion TYP1; subst.
      assert (vis = f /\ Chan un p0 t0 =  Chan lin pp1 t).
      destruct u; eapply in_isMap...
      inversion H2.  inversion H4.
      eauto.
      
    - Case uOut.
      intros.
      inversion TYP. subst.

      eapply tsuper_payload with (pf1 := pf1) in H1 as K0.
      destruct K0 as [pp1 TYP1].
      inversion TYP1; subst.
      assert (vis = f /\ Chan lin p0 t0 =  Chan un pp1 t).
      destruct u; eapply in_isMap...
      inversion H4.  inversion H6.
      eauto.
      
      simpl in AFT, H0, H1, SLP, TYP.
      eapply tsuper_payload with (pf1 := pf1) in H1 as K0.
      destruct K0 as [pp1 TYP1].
      inversion TYP1; subst.
      assert (vis = f /\ Chan un p0 t0 =  Chan un pp1 t).
      destruct u; eapply in_isMap...   inversion H3. inversion H5. subst.
      assert (k1 = ((v, vis, t3) :: (removeEntry v g1))).
      destruct v; eapply lts_un_output_action.
      all:eauto.
      revert dependent pf3.
      rewrite <-H4. intuition.
      all:eapply typeCheck_rewrite_pf...
      
    - Case lIn.
      intros.
      assert (DIFF : (a1, a2) <> (b1, b2)).
      eapply nonRecActions1...
      assert (DIFF3 : (x1, x2) <> (b1, b2)).
      eapply in_g_in_domain in H2. erewrite <-split_domain_l_2 with (pf1 := pf1) in H2. eapply in_domain_in_g in H2 as (ff &tf &IN).
      eapply in_diff_not_in with (g := g1).
      inversion TYP; subst; rewrite <-surjective_pairing...
      eauto. eauto.
      
      inversion TYP. subst.
      destruct u as [a1 a2];
        destruct x as [x1 x2];
        simpl in *.
       assert (DIFF2 : (x1, x2) <> (a1, a2)).
       eapply in_diff_not_in...
       eapply tsuper_payload with (pf1 := pf1) in H1 as K0.
      destruct K0 as [pp1 TYP1].
      inversion TYP1; subst. simpl.
      inversion AFT; subst.
      assert (f0 = vis /\ Chan lin pp1 t =  Chan lin inp t4).
      eapply in_isMap... inversion H4. inversion H6. subst f0 t4 pp1.
      assert (vis = vis /\ Chan lin p0 t0 =  Chan lin inp t).
      eapply in_isMap... inversion H5. inversion H13. subst p0 t0.
      assert (EQ: t3 = Chan lin empty t).
      inversion H8. inversion H15. inversion H16. inversion H25. 
      subst...
      subst t3.
      assert (TC := H11).
      revert dependent pfk1. rewrite removeEntry_swap with (a := (a1, a2)) (b := (b1, b2)). intros.
      
      (* substitution lemma *)
      assert (nd_pfk' :
                NoDup (domain
                       ((b1, b2, vis, t6)
                     :: removeEntry (b1, b2)
                     (removeEntry (x1, x2)
                     (((a1, a2, vis, Chan lin empty t) :: (x1, x2, vis, t) :: removeEntry (a1, a2) g1)))))).
      erewrite removeEntry_shift
        with (b1 := x1),
             <-removeEntry_shift with (b1 := a1), removeEntry_swap,<-removeEntry_shift with (b1 := a1). 
      eapply no_dup_cons_removeEntry_app.
      unfold removeEntry; fold removeEntry.
      rewrite pairEq_eq_true...
      eauto. eauto. eauto. eauto. intuition.
      apply no_dup_isMap in nd_pfk' as pfk'.
      assert
        (TCS: typeCheck
                ((b1, b2, vis, t6)
                     :: removeEntry (b1, b2)
                     (removeEntry (x1, x2)
                                  (((a1, a2, vis, Chan lin empty t) :: (x1, x2, vis, t) :: removeEntry (a1, a2) g1))))
                pfk'  (pmap p x1 x2 b1 b2)).
      eapply typeCheck_substitution.
      rewrite removeEntry_shift.
      eapply no_dup_cons_removeEntry.
      unfold domain; fold domain...
      intuition.
      right; right; eapply removeEntry_in...
      right...
      eauto.
      erewrite max_same_domain with
          (l := domain ((a1, a2, vis, Chan lin empty t) :: removeEntry (a1, a2)  ((x1, x2, vis, t) :: g1))), <-max_removeEntry_cons. simpl. erewrite <-Nat.ltb_lt in TC; erewrite TC...
      simpl...
      simpl.  right...
      rewrite <-removeEntry_shift; intuition.
      eauto. 
      eauto.
      eauto.

      (*typeCheck
    ((a1, a2, vis, Chan lin empty t)
     :: (b1, b2, vis, t6) :: removeEntry (b1, b2) (removeEntry (a1, a2) g1)) pfk1
    (pmap p x1 x2 b1 b2)*)
      assert (EQ:
                ((b1, b2, vis, t6)
           :: removeEntry (b1, b2)
                (removeEntry (x1, x2)
                   ((a1, a2, vis, Chan lin empty t)
                      :: (x1, x2, vis, t) :: removeEntry (a1, a2) g1))) =
                (b1, b2, vis, t6)
                 ::   ((a1, a2, vis, Chan lin empty t)
                      :: 
           removeEntry (b1, b2)
           (removeEntry (a1, a2) g1))).
      erewrite <-removeEntry_shift with (b1 := a1).
      unfold removeEntry at 2; fold removeEntry; rewrite pairEq_eq_true.
      erewrite <-removeEntry_shift with (b1 := a1)...
      eauto.
      revert dependent pfk'. rewrite EQ.
      intros. 
      eapply typeCheck_impl with (pf1 := pfk').
      eapply no_dup_cons_removeEntry_app...
      erewrite removeEntry_swap. eapply no_dup_cons_removeEntry_app...
      eauto.
      eauto.
      (*forall x : name * name * flag * piType,
  In x
    ((b1, b2, vis, t6)
     :: removeEntry (b1, b2)
          (removeEntry (x1, x2)
             ((a1, a2, vis, Chan lin empty t) :: (x1, x2, vis, t) :: removeEntry (a1, a2) g1))) <->
  In x
    ((a1, a2, vis, Chan lin empty t)
     :: (b1, b2, vis, t6) :: removeEntry (b1, b2) (removeEntry (a1, a2) g1))*)
      eapply cons_cons_iff.
      eauto.
      

      eapply tsuper_payload with (pf1 := pf1) in H1 as K0.
      destruct K0 as [pq1 TYPP1].
      inversion TYPP1; subst.
      assert (vis = f2 /\ Chan un pol t4 =  Chan lin pq1 t).
      eapply in_isMap...
      inversion H5.  inversion H7.
      eauto. eauto.

      eapply tsuper_payload with (pf1 := pf1) in H1 as K0.
      destruct K0 as [pq1 TYPP1].
      inversion TYPP1; subst.
      assert (vis = f0 /\ Chan un p0 t0 =  Chan lin pq1 t).
      destruct u; eapply in_isMap...
      inversion H3.  inversion H5.
      all:eauto.
                               
    - Case uIn.
      intros.
      inversion TYP. subst.
      assert (DIFF : u <> (b1, b2)).
      destruct u. eapply nonRecActions1...
      assert (DIFF2 : x <> u).
      destruct u, x; eapply in_diff_not_in...
      assert (DIFF3 : x <> (b1, b2)).
      eapply in_g_in_domain in H3. erewrite <-split_domain_l_2 with (pf1 := pf1) in H3. eapply in_domain_in_g in H3 as (ff &tf &IN).
      destruct x. eapply in_diff_not_in with (g := g1).
      inversion TYP; subst; rewrite <-surjective_pairing...
      eauto. eauto.

      
      eapply tsuper_payload with (pf1 := pf1) in H2 as K0.
      destruct K0 as [pq1 TYPP1].
      inversion TYPP1; subst. destruct u; simpl in *.
      assert (vis = f0 /\ Chan lin p0 t0 =  Chan un pq1 t).
      eapply in_isMap...
      inversion H5.  inversion H7.
      all:eauto.

      inversion H7.

       rewrite surjective_pairing with (p := u ), H4, H5  in H10.
      revert dependent pf3.
       rewrite surjective_pairing with (p := x ), H6, H7; intros. 
      eapply tsub_un in H10 as K13... inversion K13.
      assert (Chan un pol t = Chan un p0 t0).
      eapply type_of_map with (x := (a1, a2)) (g := g)...
      inversion H19; subst p0 t0. subst.
      inversion AFT; subst.
      assert (vis = vis /\ Chan un pol t =  Chan lin inp t0).
      eapply in_isMap... inversion H4. inversion H6.
      assert (vis = vis /\ Chan un pol t =  Chan un pol0 t0).
      eapply in_isMap... inversion H4. inversion H6. subst pol0 t0.
      
      assert (TC := H12). 
      (* substitution lemma *)
      destruct x as [x1 x2]; simpl in *.
      assert (nd_pfk' :
                NoDup (domain
                       ((b1, b2, vis, t4)
                     :: removeEntry (b1, b2)
                     (removeEntry (x1, x2)
                     ((x1, x2, vis, t) :: g1))))).
      unfold removeEntry; fold removeEntry; rewrite pairEq_eq_true. eapply no_dup_cons_removeEntry...
      apply no_dup_isMap in nd_pfk' as pfk'.
      assert (DIFF3 : (x1, x2) <> (b1, b2)).
      eapply in_g_in_domain in H3. erewrite <-split_domain_l_2 with (pf1 := pf1) in H3. eapply in_domain_in_g in H3 as (ff &tf &IN). eapply in_diff_not_in with (g := g1)...
      eauto.

      (* 19-7*)
      inversion TYP.  destruct u, u0; subst; simpl in *; subst.
      assert (ABS: Chan lin p0 t0 = Chan un pol t).
      eapply type_of_map with (x := (n,n0)) (g := g1)...
      inversion ABS.

      assert
        (TCS: typeCheck
                ((b1, b2, vis, t4)
                     :: removeEntry (b1, b2)
                     (removeEntry (x1, x2)
                     ((x1, x2, vis, t) :: g1)))
                pfk'  (pmap p x1 x2 b1 b2)).
      eapply typeCheck_substitution.
      eapply NoDup_cons_iff...
      right...
      eauto.
      eauto.
      simpl. erewrite <-Nat.ltb_lt in TC; erewrite TC...
      
      eauto.
      eauto.
      eauto.

      destruct x ; subst; simpl in *.
      eapply typeCheck_impl with (pf1 := pfk')...
      assert (EQx : pair_eq (n, n0) (n, n0) = true). eauto.
      rewrite EQx. intuition.

      
    - Case uRin.
      intros. 
      inversion TYP. subst.
      assert (DIFF : u <> (b1, b2)).
      destruct u. eapply nonRecActions1...
      assert (DIFF2 : x <> u).
      destruct u, x; eapply in_diff_not_in...
       assert (DIFF4 : x <> (b1, b2)).
      eapply in_g_in_domain in H3. erewrite <-split_domain_l_2 with (pf1 := pf1) in H3. eapply in_domain_in_g in H3 as (ff &tf &IN).
      destruct x. eapply in_diff_not_in with (g := g1).
      inversion TYP; subst; rewrite <-surjective_pairing...
      eauto. eauto.

      
      destruct u as [u1 u2]; destruct x as [x1 x2]; simpl in *.
      eapply tsub_un in H10 as K13... inversion K13.
      assert (Chan un pol t = Chan un p0 t0).
      eapply type_of_map with (x := (u1, u2)) (g := g)...
      inversion H8; subst p0 t0. subst. clear f0 H4 H9.
      inversion AFT; subst.
      assert (vis = vis /\ Chan un pol t =  Chan un pol0 t0).
      eapply in_isMap... inversion H4. inversion H6.
      subst pol0 t0 q0 q1. clear H4 H5 H6 H8.

      remember t3 as s3.
      assert (DIFF3 := H22).
      
      destruct s3. destruct m.
      (*destruct f0.
      intuition.*)
      (* m = lin *) 
      (* f0 = ill *) 
      + 
      remember ((b1, b2, vis, t3) :: removeEntry (b1, b2) g1) as gg1.
      remember ((x1, x2, vis, t) :: g1) as k.
      assert (nd_pfk: NoDup (domain k)).
      subst k. unfold domain; fold domain; eapply NoDup_cons...
      assert (pff1: isMap gg1).
      subst; eapply no_dup_split_no_dup.cons_removeEntry,no_dup_domain_cons...
      assert (pff3: isMap ((x1, x2, vis, t) :: gg1)).
      subst.
      apply isMap_not_in ; try assumption.
      intros ABS; inversion ABS. inversion H4; subst.
      eapply in_g_in_domain in H24; contradiction.
      eapply in_domain_in_g in H4; destruct H4 as [ff [tt ABS2]]; eapply in_removeEntry in ABS2; eapply in_g_in_domain in ABS2; contradiction.
      assert(nd_pff:  NoDup (domain ((b1, b2, vis, t3) :: removeEntry (b1, b2) k))).
      subst. eapply no_dup_cons_removeEntry;unfold domain; fold domain; eapply NoDup_cons...
       apply no_dup_isMap in nd_pff as pff. 
      
      assert (TC: typeCheck ((x1, x2, vis, t) :: gg1) pff3 p).
      assert (TC0 := H14).
      destruct f0. contradiction.
      eapply typeCheck_impl.
      instantiate (1 := (b1, b2, vis, t3)
                          :: removeEntry (b1, b2) k)...
     
      subst; unfold domain; fold domain; eapply NoDup_cons,  no_dup_cons_removeEntry.
      intros ABS; inversion ABS. inversion H4; subst.
      eapply in_g_in_domain in H24; contradiction.
      eapply in_domain_in_g in H4; destruct H4 as [ff [tt ABS2]]; eapply in_removeEntry in ABS2; eapply in_g_in_domain in ABS2; contradiction.
      eauto.

      
      eapply typeCheck_ill_vis. eauto. subst k t3...
      subst; right...
      (* forall x : name * name * flag * piType,
  In x ((b1, b2, vis, t3) :: removeEntry (b1, b2) ((x1, x2, vis, t) :: g1)) <->
  In x ((x1, x2, vis, t) :: (b1, b2, vis, t3) :: removeEntry (b1, b2) g1) *)
      subst.
      rewrite <-removeEntry_shift with (b1 := x1).
      eapply cons_cons_iff.
       intros ABS; inversion ABS. subst.
       eapply in_g_in_domain in H24; contradiction.

       eapply typeCheck_impl.
      instantiate (1 := (b1, b2, vis, t3)
                          :: removeEntry (b1, b2) k)...
     
      subst; unfold domain; fold domain; eapply NoDup_cons,  no_dup_cons_removeEntry.
      intros ABS; inversion ABS. inversion H4; subst.
      eapply in_g_in_domain in H24; contradiction.
      eapply in_domain_in_g in H4; destruct H4 as [ff [tt ABS2]]; eapply in_removeEntry in ABS2; eapply in_g_in_domain in ABS2; contradiction.
      eauto.
      eapply typeCheck_impl with (pf1 := pf3).
      eauto. eauto. eauto. eapply in_removeEntry_cons_iff_0. eauto. subst. right...
         subst.
      rewrite <-removeEntry_shift with (b1 := x1).
      eapply cons_cons_iff.
       intros ABS; inversion ABS. subst.
       eapply in_g_in_domain in H24; contradiction.
      
   
      
      assert (nd_pf' :
                NoDup (domain 
      ((newEntries
          k
          (secLabs (dep_relabel p (domain k) nd_pfk))
          (max (domain k)))
         ++
         illECast k))).
      eapply no_dup_ne_ic...
      apply no_dup_isMap in nd_pf' as pf'.

      
      assert
        (TC':
           typeCheck 
             ((newEntries
                 k
                 (secLabs (dep_relabel p (domain k) nd_pfk))
                 (max (domain k)))
                ++
                illECast k) pf'
             (dep_relabel p (domain k) nd_pfk)).
      eapply typeCheck_dep_relabel2...

      assert (MAX : max (domain k) = max (domain g1)). subst k; unfold domain; fold domain; unfold max; fold max. eapply Nat.ltb_lt in H12; erewrite H12...

      
     assert (nd_pf'' :
                NoDup
                  (domain
                     (((x1, x2, vis, t)
                         :: (newEntries g1 (secLabs (dep_relabel p (domain k) nd_pfk)) (max (domain k)) ++ illECast g1))))).
      unfold domain; fold domain; eapply NoDup_cons.
      intros ABS.
      eapply in_domain_in_g in ABS.
      destruct ABS as [ff [tt ABS]].
      eapply in_app_iff in ABS as [ABS | ABS].
      erewrite identif_seclabs_of_dep_relabel in ABS;
        eapply newEntries_gte_max in ABS.
      subst. unfold domain,max; fold domain; intuition.
      eapply in_g_in_domain in ABS; erewrite illEC_eq_domain in ABS; contradiction.
      subst k.

      erewrite newEntries_remove0
        with (p := p) (f := vis) in nd_pf';
        try assumption.
      unfold  illECast in nd_pf'.
      rewrite map_cons in nd_pf'. unfold cast at 1 in nd_pf'.
      repeat rewrite domain_distr in nd_pf';
        unfold domain in nd_pf'; fold domain in nd_pf'.
      repeat rewrite domain_distr.
      eapply NoDup_remove_1...

      (* new version of newEntries_remove *)
      erewrite max_dep_relabel...
      simpl; case_eq (x2 <? max (domain g1)); intros; try lia...
      intros ABS;
        eapply typeCheck_no_dup in TYP as [INCL _];
        try simpl in INCL;
        try unfold incl in INCL;
        try specialize INCL with (x1, x2); intuition.
      
      (*erewrite identif_seclabs_of_dep_relabel; intros x IN;
        eapply in_map_iff in IN as (y &EQ &IN); subst x;
          eapply in_map_iff in IN as ([z1 z2] &EQ &IN); subst y;
            unfold fst, snd.
      assert (EQ: z2 + max (domain ((x1, x2, vis, t) :: g1)) - max (domain ((x1, x2, vis, t) :: g1)) = z2)by lia.
      rewrite EQ. eapply typeCheck_no_dup...
      intros ABS.
      erewrite identif_seclabs_of_dep_relabel,MAX,in_map_iff in ABS;
        destruct ABS as (e &ABS &_); inversion ABS; subst x2; lia. *)  
     
      eapply no_dup_isMap in nd_pf'' as pf''.
       
      assert (TC'':
                typeCheck
                  (cast (x1, x2, vis, t) :: (newEntries g1 (secLabs (dep_relabel p (domain k) nd_pfk)) (max (domain k)) ++
                                                        illECast g1)) pf'' (dep_relabel p (domain k) nd_pfk)).
      assert (NIN: ~ In (x1, x2) (secLabs (dep_relabel p (domain k) nd_pfk))).
      erewrite identif_seclabs_of_dep_relabel, MAX; intro ABS; erewrite in_map_iff in ABS; destruct ABS as [y [ABS _]]; inversion ABS; lia.
      eapply typeCheck_impl with (pf1 := pf'),ne_illEC_var...
      intros z INSL; rewrite identif_seclabs_of_dep_relabel in INSL. eapply in_map_iff in INSL as ((z1 & z2) & EQ & INSL). subst z. simpl.
      assert (INDOM: incl (secLabs (dBang u1 u2 x1 x2 p)) (domain g1)). eapply typeCheck_no_dup...
      simpl in INDOM. assert (MAXEQ: z2 + max (domain k) - max (domain k) = z2) by lia. rewrite MAXEQ; simpl; apply INDOM...
      

         assert (NIND:  ~
  In (x1, x2)
    (domain
       (newEntries g1 (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1)) ++
                   illECast g1))).
    rewrite domain_distr, illEC_eq_domain;
        intro IN; eapply in_app_iff in IN; inversion IN as [ABS | ABS]. erewrite identif_seclabs_of_dep_relabel in ABS; eapply incl_newEntries_domain in ABS;erewrite in_map_iff in ABS; destruct ABS as [y [ABS _]]; inversion ABS; lia. intuition auto.

      revert dependent pf''.
      erewrite MAX, max_dep_relabel with (nd_pf1 := nd_pf1); unfold cast,castF,flag_eq;simpl;
      intros...

      assert (nd_pf2 :
                NoDup
                  (domain
                     (newEntries g1 (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1)) ++
                                 illECast g1))).
      eapply no_dup_domain_cons in nd_pf'';
        erewrite identif_seclabs_of_dep_relabel,<-MAX,<-identif_seclabs_of_dep_relabel...
      eapply no_dup_isMap in nd_pf2 as pf2'.
      assert (nd_pf1' :
                 NoDup
                  (domain
                     ((x1, x2, vis, t):: ((newEntries
                 g1
                 (secLabs (dep_relabel p (domain g1) nd_pf1))
                 (max (domain g1)))
                ++
                illECast  g1)))).
      unfold domain; fold domain; eapply NoDup_cons...
      eapply no_dup_isMap in nd_pf1' as pf1'.
      assert (nd_pf_prem :
                NoDup
                  (domain
                     ((vis_proj
       (newEntries g1 (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1)) ++
        illECast g1) ++
     ill_proj
       (newEntries g1 (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1)) ++
                   illECast g1))))).
      erewrite domain_distr.
      eapply distr_no_dup.
      eapply no_dup_vis_proj...
      eapply no_dup_ill_proj...
      eapply disjoint_projections...
      eapply no_dup_isMap in nd_pf_prem as pf_prem.

      assert (TC2:
                typeCheck 
             ((newEntries
                 g1
                 (secLabs (dep_relabel p (domain g1) nd_pf1))
                 (max (domain g1)))
                ++
                illECast  g1) pf2'
             (dBang u1 u2 x1 x2 (dep_relabel p (domain k) nd_pfk))).
      eapply TInU with
          (u := (u1, u2)) (x := (x1, x2)) (p := pol)
          (pf1 := pf1') (pf2 := pf_prem).
      intuition. eapply in_app_iff; right.
      
      eapply in2_false_illECast...  eauto. eauto. 

      simpl; erewrite domain_distr; eapply max_distr;erewrite illEC_eq_domain...
      
      (*cons
    (vis_proj
       (newEntries g1 (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1)) ++
        illECast g1) ++
     ill_proj
       (newEntries g1 (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1)) ++
        illECast g1)) pf_prem*)
      assert (LEM1 := proj_distr).
      assert (LEM2 := proj_newEntries_nil).
      assert (LEM3 := proj_illECast_gcons).
      assert (LEM4 := gcons_distr). 
      assert (PF := pf4). assert (CON:= H13).
      revert dependent pf_prem;
        erewrite LEM1, identif_seclabs_of_dep_relabel, LEM2, app_nil_l.
      erewrite LEM1, LEM2, app_nil_l. intros.
      erewrite LEM4; split.
      eapply LEM3. eauto. left... eapply LEM4 in CON as [CON _]...
       eapply LEM3. eauto. right... eapply LEM4 in CON as [_ CON]...

      eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.

      move MAX at bottom.
      assert (DEP: forall nd_pfk, dep_relabel p (domain k) nd_pfk =
                   dep_relabel p (domain g1) nd_pf1).
      erewrite max_dep_relabel...
      erewrite DEP...

      assert (DEP: forall nd_pfk, dep_relabel p (domain k) nd_pfk =
                   dep_relabel p (domain g1) nd_pf1).
      erewrite max_dep_relabel...
      erewrite DEP in TC2.
      
      
      (* substitution lemma *)
      assert (nd_pfk' :
                NoDup (domain
                       ((b1, b2, vis, t4)
                     :: removeEntry (b1, b2)
                     (removeEntry (x1, x2)
                                  ((x1, x2, vis, t) :: g1))))).
      unfold removeEntry.
      assert (EQx : pair_eq (x1, x2) (x1, x2)= true).
      eauto. rewrite EQx. fold removeEntry.
      eapply no_dup_cons_removeEntry...
      apply no_dup_isMap in nd_pfk' as pfk'.
      assert
        (TC1: typeCheck
                ((b1, b2, vis, t4)
                     :: removeEntry (b1, b2)
                     (removeEntry (x1, x2)
                     ((x1, x2, vis, t) :: g1)))
                pfk'  (pmap p x1 x2 b1 b2)).
      assert (pf_restore_illegal_app: isMap ((x1, x2, vis, t) :: g1)).
      apply isMap_not_in; try assumption.
      eapply typeCheck_substitution with (pf := pf_restore_illegal_app).
      eapply NoDup_cons_iff...
      right...
      eauto.
      eauto.
      simpl. assert (LT := H12);
               rewrite <-Nat.ltb_lt in LT; rewrite LT...
      eauto.
      subst k...
      inversion TYP; subst...
      move TC2 at bottom.

      remember (newEntries g1 (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1))) as w.
      assert (nd_pfw : NoDup (domain w)).
      subst w; eapply newEntries_no_dup; eapply typeCheck_no_dup in TC''; intuition auto...
      apply no_dup_isMap in nd_pfw as pfw.
      
      assert (NEU: exists (neutral : typeEnv) (pfn : isMap neutral) (nd_pfn : NoDup (domain neutral)),
         tEnv_split w neutral w pfw pfn pfw).
      eapply split_exists_neutral;eauto...
      destruct NEU as [neutral [pfn [nd_pfn TS2]]];
        eapply split_comm in TS2.

      assert (nd_pfk'' :
                NoDup
                  (domain
                  (neutral ++  ((b1, b2, vis, t4)
                                  :: removeEntry (b1, b2) (removeEntry (x1, x2) ((x1, x2, vis, t) :: g1)))))).
      erewrite domain_distr.
      eapply distr_no_dup.
      eauto.
      eauto.
      eapply disjoint_iff...
      erewrite disjoint_commute.
      eapply disjoint_iff with (l1 := (domain g1)).
      subst w. eapply new_entries_disjoint...
      assert (INK: incl (secLabs p) (domain k)).
      eapply typeCheck_no_dup...
      subst k. unfold domain in INK; fold domain in INK.
      eapply incl_preserves_max.
      unfold incl; intros x IN.
      unfold incl in INK; specialize INK with x.
      apply INK in IN as ABS.
      inversion ABS; subst.
      assert (ABS2: incl (secLabs (dBang u1 u2 x1 x2 p)) (domain g1)).
      eapply typeCheck_no_dup...
      unfold secLabs in ABS2; fold secLabs in ABS2.
      assert (ABS3: In (x1, x2) (domain g1)).
      eapply incl_tran in ABS2...
      eauto. eauto.
      unfold removeEntry. fold removeEntry.
      rewrite pairEq_eq_true.
      eapply in_removeEntry_cons_iff.
      eauto. eapply in_g_in_domain...
      eapply no_dup_isMap in nd_pfk'' as pfk''.
      eapply typeCheck_weak2 with (pf1 := pfk'') in TC1.

      destruct f0.
      contradiction.
      
      (* f0 = ill *)
      assert (nd_pf2'':
                NoDup(domain(
                          w ++ ((b1, b2, vis, t3) :: removeEntry (b1, b2) (illECast g1))))).
      erewrite domain_distr. eapply distr_no_dup.
      eauto.
      eapply no_dup_cons_removeEntry.
      assert (K := nd_pf2). erewrite domain_distr, no_dup_iff  in K; intuition.
      subst w.
      assert (DIS: disjoint (domain g1)
    (domain (newEntries g1 (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1))))).
      eapply  new_entries_disjoint...
      eapply typeCheck_no_dup in TYP as [INCL _].
      unfold secLabs in INCL; fold secLabs in INCL.
      eapply incl_preserves_max...
      eauto.
      assert (DIS2: disjoint ( (domain ((b1, b2, vis, t3) :: removeEntry (b1, b2) (illECast g1))))
                             (domain (newEntries g1 (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1))))).
       assert (NIN: ~In (b1, b2) (domain (newEntries g1 (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1))))).
        intros ABS.
        assert (INB: In (b1, b2) (domain g1)).
        eapply in_g_in_domain...
        eapply disjoint_absurd...
      eapply disjoint_cons_removeEntry.
       assert (K := nd_pf2); erewrite domain_distr, no_dup_iff  in K; intuition.
       erewrite illEC_eq_domain... assumption.
       eapply disjoint_commute...

       eapply no_dup_isMap in nd_pf2'' as pf2''.
       eapply TPar with (pf1 := pfk'') (pf2 := pf2'').
      revert dependent pfk''; unfold removeEntry; fold removeEntry; erewrite pairEq_eq_true; intros.

      assert (pfp1 := pfk').
      unfold removeEntry in pfp1; fold removeEntry in pfp1; rewrite pairEq_eq_true in pfp1.
      assert (nd_pfp'': NoDup (domain ((((b1, b2, vis, t3) :: removeEntry (b1, b2) (illECast g1)))))).
      eapply no_dup_cons_removeEntry.
      erewrite illEC_eq_domain...
      eapply no_dup_isMap in nd_pfp'' as pfp''.

      assert (TSAV:
                tEnv_split ((b1, b2, vis, t4) :: removeEntry (b1, b2) g1) ((b1, b2, vis, t3) :: removeEntry (b1, b2) (illECast g1))
                           ((b1, b2, vis, t4) :: removeEntry (b1, b2) g1) pfp1 pfp'' pfp1).
      eapply tEnv_split_add_vis.
      eauto.
      (* type_plus t4 t3 t4 *)
      assert (PEQ: p0 = empty).
      eapply gcons_distr in H13;  destruct H13 as [CONS].
      eapply cons_lin with (a1 := b1) (a2 := b2) (f := ill) (g := ill_proj g1).
      eauto.
      eapply in_ill_proj...
      subst p0.
      
      assert (TP := H21); move TP at bottom;
        subst t3; inversion H21; subst; inversion H8; subst; econstructor;eapply Pp_emptyR.
      unfold is_unrestricted; intros ABS. destruct ABS as [pp [ss EQ]]; subst; inversion H21; intuition auto.
      eapply split_illECast_cons...

      eapply split_distr.
      eauto.
      eauto.
      eauto.
     
      (* typeCheck (w ++ (b1, b2, vis, t3) :: removeEntry (b1, b2) (illECast g1)) pf2''
    (dBang u1 u2 x1 x2 (dep_relabel p (domain g1) nd_pf1))*)
      move TC2 at bottom.
      assert (nd_pf2''':
                NoDup (domain (
                           (b1, b2, vis, t3) :: removeEntry (b1, b2)((w ++ illECast g1))))).
      eapply no_dup_cons_removeEntry...
      eapply no_dup_isMap in nd_pf2''' as pf2'''.
      eapply typeCheck_impl with (pf1 := pf2''').
      eauto.
      eauto. 
      eapply typeCheck_ill_vis.
      eauto.
      eauto.
      eapply in_app_iff. right.
      eapply in_illECast.
      subst...
      assert (p0 = empty). eapply cons_lin with (g := vis_proj g1 ++ ill_proj g1),in_vis_ill_proj...
      subst; right; split; try discriminate;
        left; try exists empty...
      (*In x ((b1, b2, vis, t3) :: removeEntry (b1, b2) (w ++ illECast g1)) <->
  In x (w ++ (b1, b2, vis, t3) :: removeEntry (b1, b2) (illECast g1))*)
      intros.
      eapply in_app_removeEntry_iff.
      eauto.
      intros ABS. subst w.
      assert (ABS2: In (b1, b2) (secLabs (dep_relabel p (domain g1) nd_pf1))).
      eapply incl_newEntries_domain...
      erewrite identif_seclabs_of_dep_relabel,in_map_iff in ABS2; destruct ABS2 as [[b1' b2'] [ABS2 ABS3]]. simpl in ABS2, ABS3. inversion ABS2.
      assert (b2 <= max (domain g1)).
      eapply in_preserves_max, in_g_in_domain...
      assert (b2' = 0). lia.
      eapply sl_pos_bang in SLP.
      unfold sl_pos, pos in SLP; specialize SLP with b1' b2'; intuition.
      
      (* f0 = vis *)
      eapply TPar with (pf1 := pfk'') (pf2 := pf2').
      revert dependent pfk''; unfold removeEntry; fold removeEntry; erewrite pairEq_eq_true; intros.

      assert (pfp1 := pfk').
      unfold removeEntry in pfp1; fold removeEntry in pfp1; rewrite pairEq_eq_true in pfp1.
      assert (nd_pfp'': NoDup (domain ((((b1, b2, vis, t3) :: removeEntry (b1, b2) (illECast g1)))))).
      eapply no_dup_cons_removeEntry.
      erewrite illEC_eq_domain...
      eapply no_dup_isMap in nd_pfp'' as pfp''.

      assert (TSAV:
                tEnv_split ((b1, b2, vis, t4) :: removeEntry (b1, b2) g1) ((b1, b2, vis, t3) :: removeEntry (b1, b2) (illECast g1))
                           ((b1, b2, vis, t4) :: removeEntry (b1, b2) g1) pfp1 pfp'' pfp1).
      eapply tEnv_split_add_vis.
      eauto.
      (* type_plus t4 t3 t4 *)
      assert (PEQ: p0 = empty).
      eapply gcons_distr in H13;  destruct H13 as [CONS].
      eapply cons_lin with (a1 := b1) (a2 := b2) (f := vis) (g := vis_proj g1).
      eauto.
      eapply in_vis_proj...
      subst p0.
      
      
      assert (TP := H21); move TP at bottom;
        subst t3; inversion H21; subst; inversion H8; subst; econstructor;eapply Pp_emptyR.
      unfold is_unrestricted; intros ABS. destruct ABS as [pp [ss EQ]]; subst; inversion H21; intuition auto.
      eapply split_illECast_cons...

      eapply split_distr.
      eauto.
      eapply split_iff2 with (g2 :=  ((b1, b2, vis, t3) :: removeEntry (b1, b2) (illECast g1))).
eapply no_dup_cons_removeEntry.
(*      eapply no_dup_split_no_dup_r with (g := g)...*)
       erewrite domain_distr in nd_pf2;
         eapply no_dup_distr in nd_pf2; intuition.
        erewrite domain_distr in nd_pf2;
        eapply no_dup_distr in nd_pf2; intuition.
       eauto.
      (*forall x : name * name * flag * piType,
  In x ((b1, b2, vis, t3) :: removeEntry (b1, b2) (illECast g1)) <-> In x (illECast g1)*)
      assert (REV: forall x, In x (illECast g1) <-> In x ((b1, b2, vis, t3) :: removeEntry (b1, b2) (illECast g1))).
      eapply in_removeEntry_cons_iff_0.
      erewrite illEC_eq_domain...
      eapply in_illECast. subst... left...
      eauto.
      assumption.
      assumption.
      erewrite <-domain_distr...
      (* cons neutral ?pfk *)
      eapply neutral_is_gcons...

      rewrite bv_pmap.
      assert (DIS:disjoint (bv p) (domain w)).
      subst w;
          rewrite identif_seclabs_of_dep_relabel in *;
          eapply Peirce; intros ABS;
          eapply not_disjoint in ABS as ([y1 y2] &ABS1 &ABS2);
          eapply in_bv_lt_max with (pf := pf3) in ABS1;
          eapply in_domain_in_g in ABS2 as (ff &tt &ABS2);
          eapply newEntries_gte_max in ABS2;
          try lia;
        try eassumption.
      eapply disjoint_commute,disjoint_iff; try eapply disjoint_commute; try eassumption.
      eauto.
      
      + (* m = un *)
        assert (TP := H21); move TP at bottom; inversion H21; subst.
        remember ( Chan un p2 s3) as t.

        assert (DIFF1: (x1, x2) <> (b1, b2)). intros ABS; inversion ABS; subst; eapply in_g_in_domain,split_domain_l_2 with (g1 := g1) in H3. contradiction. eauto.

        assert (nd_pf_tmp: NoDup (domain ((b1, b2, f0, Chan un (pol_cup p0 p2) s3)
                                            :: removeEntry (b1, b2) ((x1, x2, vis, t) :: g1)))).
        erewrite <-removeEntry_shift. eapply no_dup_cons_removeEntry_app_1... intuition.
        apply no_dup_isMap in nd_pf_tmp as pf_tmp.
        eapply typeCheck_weak_is_un with (a1 := b1) (a2 := b2) (f := f0) (pol1 := p0) (pol2 := p2) (t := s3) (pf2 := pf_tmp) in H14; assert (TC1 := H14); clear H14.
         assert (nd_pf_tmp0_2: NoDup (domain ((b1, b2, vis, Chan un (pol_cup p0 p2) s3)
                                            :: removeEntry (b1, b2) ((b1, b2, f0, Chan un (pol_cup p0 p2) s3)
           :: removeEntry (b1, b2) ((x1, x2, vis, t) :: g1))))).
         unfold removeEntry at 1; fold removeEntry.
         rewrite pairEq_eq_true. erewrite <-removeEntry_shift. eapply no_dup_cons_removeEntry_app_1; intuition.
         eauto.
        apply no_dup_isMap in nd_pf_tmp0_2 as pf_tmp0_2.

       
        assert (TC1_0' : typeCheck
                        ((b1, b2, vis, Chan un (pol_cup p0 p2) s3)
               :: removeEntry (b1, b2)
                    ((b1, b2, f0, Chan un (pol_cup p0 p2) s3)
                       :: removeEntry (b1, b2) ((x1, x2, vis, t) :: g1))) pf_tmp0_2 p).
        eapply typeCheck_strength_vis...
        revert dependent pf_tmp0_2.
        unfold removeEntry; fold removeEntry.
        rewrite pairEq_eq_true.
        assert (EQn: pair_eq (x1, x2) (b1, b2) = false).
        eapply pairEq_neq... rewrite EQn. intros.
        assert (nd_pf_tmp2: NoDup (domain (((x1, x2, vis, t) :: (b1, b2, vis, Chan un (pol_cup p0 p2) s3)
                                                             ::  removeEntry (b1, b2) g1)))).
        unfold domain; fold domain; subst; unfold domain; fold domain; eapply NoDup_cons,  no_dup_cons_removeEntry.
      intros ABS; inversion ABS. inversion H4; subst.
      eapply in_g_in_domain in H24; contradiction.
      eapply in_domain_in_g in H4; destruct H4 as [ff [tt ABS2]]; eapply in_removeEntry in ABS2; eapply in_g_in_domain in ABS2; contradiction.
      eauto.
      
      apply no_dup_isMap in nd_pf_tmp2 as pf_tmp2.
      assert (TC1' : typeCheck
                       ((x1, x2, vis, t) :: (b1, b2, vis, Chan un (pol_cup p0 p2) s3) :: removeEntry (b1, b2) g1) pf_tmp2 p).
      eapply typeCheck_impl with (pf1 := pf_tmp0_2).
      unfold removeEntry in nd_pf_tmp0_2;
        fold removeEntry in nd_pf_tmp0_2.
      rewrite pairEq_eq_true,EQn in nd_pf_tmp0_2...
      eauto. eauto. eapply cons_cons_iff...

      
      remember ((x1, x2, vis, t) ::  (b1, b2, vis, Chan un (pol_cup p0 p2) s3) :: removeEntry (b1, b2) g1) as k.
        
      assert (nd_pfk: NoDup (domain k)).
      subst k; unfold domain; fold domain; eapply NoDup_cons_iff; eauto.
      split. intros ABS;inversion ABS. inversion H4; subst; eapply in_g_in_domain in H24; intuition auto.
      eapply in_domain_in_g in H4; destruct H4 as [ff [tt ABS2]]. eapply in_removeEntry,in_g_in_domain in ABS2; intuition auto.
      eapply no_dup_cons_removeEntry...
      
      
      assert (nd_pf' :
                NoDup (domain 
      ((newEntries
          k
          (secLabs (dep_relabel p (domain k) nd_pfk))
          (max (domain k)))
         ++
         illECast k))).
      eapply no_dup_ne_ic...
      apply no_dup_isMap in nd_pf' as pf'.

      
      assert
        (TC':
           typeCheck 
             ((newEntries
                 k
                 (secLabs (dep_relabel p (domain k) nd_pfk))
                 (max (domain k)))
                ++
                illECast k) pf'
             (dep_relabel p (domain k) nd_pfk)).
      eapply typeCheck_dep_relabel2...

     (* rewrite Heqk.  eapply typeCheck_impl with (g1 :=  ((b1, b2, vis, Chan un (pol_cup p0 p2) s3)
                                                           :: removeEntry (b1, b2) ((x1, x2, vis, t) :: g1))).
      eauto.
      (* NoDup
    NoDup
    (domain
       ((x1, x2, vis, t)
        :: (b1, b2, vis, Chan un (pol_cup p0 p2) s3) :: removeEntry (b1, b2) g1))*)
      unfold domain; fold domain; eapply NoDup_cons.
      intros ABS; inversion ABS. inversion H4; subst.
      eapply in_g_in_domain in H24; contradiction.
      eapply in_domain_in_g in H4; destruct H4 as [ff [tt ABS2]]; eapply in_removeEntry in ABS2; eapply in_g_in_domain in ABS2; contradiction.
      eapply no_dup_cons_removeEntry...
      eauto.
      (*forall x : name * name * flag * piType,
  In x
    ((b1, b2, vis, Chan un (pol_cup p0 p2) s3)
     :: removeEntry (b1, b2) ((x1, x2, vis, t) :: g1)) <->
  In x
    ((x1, x2, vis, t)
     :: (b1, b2, vis, Chan un (pol_cup p0 p2) s3) :: removeEntry (b1, b2) g1)*)
      erewrite <-removeEntry_shift with (b1 := x1).
      eapply cons_cons_iff...
      eauto.*)

      (*typeCheck
    (newEntries g1 (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1)) ++
     (b1, b2, vis, Chan un (pol_cup p0 p2) s3) :: removeEntry (b1, b2) g1) pfk1
    (dPar (pmap p x1 x2 b1 b2) (dBang u1 u2 x1 x2 (dep_relabel p (domain g1) nd_pf1)))*)
      assert (MAX : max (domain k) = max (domain g1)). rewrite Heqk.
      assert (MAX2: max (domain g1) = max ( domain ((b1, b2, vis, Chan un (pol_cup p0 p2) s3):: removeEntry (b1, b2) g1))). eapply max_same_domain, in_removeEntry_cons_iff,in_g_in_domain...
      erewrite <-rewrite_max_var...
      erewrite <-MAX2; simpl...


      remember  ((b1, b2, vis, Chan un (pol_cup p0 p2) s3) :: removeEntry (b1, b2) g1) as g'.
      assert (SD: forall x : name * name, In x (domain g') <-> In x (domain g1)).
      subst g'.
      assert (EQ: forall x : name * name,
   In x (domain g1)  <-> In x
    (domain ((b1, b2, vis, Chan un (pol_cup p0 p2) s3) :: removeEntry (b1, b2) g1))).
      eapply in_removeEntry_cons_iff, in_g_in_domain...
      intros x; specialize EQ with x; intuition auto.

      assert (NIN: ~ In (x1, x2) (secLabs (dep_relabel p (domain k) nd_pfk))).
      erewrite identif_seclabs_of_dep_relabel, MAX; intro ABS; erewrite in_map_iff in ABS; destruct ABS as [y [ABS _]]; inversion ABS; lia.

       assert (NIND:  ~
  In (x1, x2)
    (domain
       (newEntries g' (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1)) ++
                   illECast g'))).
    rewrite domain_distr, illEC_eq_domain;
      intro IN; eapply in_app_iff in IN; inversion IN as [ABS | ABS]. erewrite identif_seclabs_of_dep_relabel in ABS; eapply incl_newEntries_domain in ABS;erewrite in_map_iff in ABS; destruct ABS as [y [ABS _]]; inversion ABS; lia. rewrite Heqg' in ABS; unfold domain in ABS; fold domain in ABS; inversion ABS. inversion H4; subst b1 b2; eapply in_g_in_domain in H24; intuition auto.
    eapply in_domain_in_g in H4; destruct H4 as [ss [tt ABS2]]; eapply in_removeEntry,in_g_in_domain in ABS2; intuition auto.

      
      assert (nd_pf'' :
                NoDup
                  (domain
                     (((x1, x2, vis, t)
                         :: (newEntries g' (secLabs (dep_relabel p (domain k) nd_pfk)) (max (domain k)) ++ illECast g'))))).
       unfold domain; fold domain; eapply NoDup_cons.
      intros ABS.
      eapply in_domain_in_g in ABS.
      destruct ABS as [ff [tt ABS]].
      eapply in_app_iff in ABS as [ABS | ABS].
      erewrite identif_seclabs_of_dep_relabel in ABS;
        eapply newEntries_gte_max in ABS.
      subst. unfold domain,max; fold domain; intuition.
      eapply in_g_in_domain in ABS; erewrite illEC_eq_domain in ABS; subst g'; repeat simpl in ABS; inverts ABS as EQb; try inversion EQb;
        subst; try contradiction;
          try eapply in_domain_in_g in EQb as (ff1 &tt1 &ABS);
          try eapply in_removeEntry,in_g_in_domain in ABS;
          try contradiction.
      subst k.

      assert (MAX2:
                max (domain ((x1, x2, vis, t) :: g')) = max (domain g')).
      subst g'; try rewrite MAX, <-max_removeEntry_cons; try tauto;
        try eapply in_g_in_domain...
      erewrite newEntries_remove0
        with (p := p) (f := vis) in nd_pf';
        try assumption. unfold  illECast in nd_pf'.
      rewrite map_cons in nd_pf'. unfold cast at 1 in nd_pf'.
      repeat rewrite domain_distr in nd_pf';
        unfold domain in nd_pf'; fold domain in nd_pf'.
      repeat rewrite domain_distr.
      eapply NoDup_remove_1...

       (* new version of newEntries_remove *)
      erewrite max_dep_relabel...
      rewrite MAX2; try lia...
      intros ABS;
        eapply typeCheck_no_dup in TYP as [INCL _];
        try simpl in INCL;
        try unfold incl in INCL;
        try specialize INCL with (x1, x2); intuition.
      
      eapply no_dup_isMap in nd_pf'' as pf''.
      
      assert (TC'':
                typeCheck
                  (cast (x1, x2, vis, t) :: (newEntries g' (secLabs (dep_relabel p (domain k) nd_pfk)) (max (domain k)) ++
                                                        illECast g')) pf'' (dep_relabel p (domain k) nd_pfk)).
      (*assert (NIN: ~ In (x1, x2) (secLabs (dep_relabel p (domain k) nd_pfk))).
      erewrite identif_seclabs_of_dep_relabel, MAX; intro ABS; erewrite in_map_iff in ABS; destruct ABS as [y [ABS _]]; inversion ABS; lia.*)
      eapply typeCheck_impl with (pf1 := pf'),ne_illEC_var...
      intros z INSL; rewrite identif_seclabs_of_dep_relabel in INSL. eapply in_map_iff in INSL as ((z1 & z2) & EQ & INSL). subst z. simpl.
      assert (INDOM: incl (secLabs (dBang u1 u2 x1 x2 p)) (domain g1)). eapply typeCheck_no_dup...
      eapply incl_iff in INDOM.
       simpl in INDOM. assert (MAXEQ: z2 + max (domain k) - max (domain k) = z2) by lia. rewrite MAXEQ; simpl; eapply INDOM... eauto.

      

      revert dependent pf''.
      erewrite MAX, max_dep_relabel with (nd_pf1 := nd_pf1); unfold cast,castF,flag_eq;simpl;
      intros.

      assert (nd_pf2 :
                NoDup
                  (domain
                     (newEntries g' (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1)) ++
                                 illECast g'))).
      eapply no_dup_domain_cons in nd_pf''.
      erewrite <-MAX, max_dep_relabel...
      eapply no_dup_isMap in nd_pf2 as pf2'.
      assert (nd_pf1' :
                 NoDup
                  (domain
                     ((x1, x2, vis, t):: ((newEntries
                 g'
                 (secLabs (dep_relabel p (domain g1) nd_pf1))
                 (max (domain g1)))
                ++
                illECast  g')))).
      unfold domain; fold domain; eapply NoDup_cons...
      eapply no_dup_isMap in nd_pf1' as pf1'.
      assert (nd_pf_prem :
                NoDup
                  (domain
                     ((vis_proj
       (newEntries g' (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1)) ++
        illECast g') ++
     ill_proj
       (newEntries g' (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1)) ++
                   illECast g'))))).
      rewrite domain_distr, no_dup_iff.
      split.
      eapply no_dup_vis_proj...
      split. eapply no_dup_ill_proj...
      eapply disjoint_projections...
      eapply no_dup_isMap in nd_pf_prem as pf_prem.

      assert (TC2:
                typeCheck 
             ((newEntries
                 g'
                 (secLabs (dep_relabel p (domain g1) nd_pf1))
                 (max (domain g1)))
                ++
                illECast  g') pf2'
             (dBang u1 u2 x1 x2 (dep_relabel p (domain k) nd_pfk))).
      eapply TInU with
          (u := (u1, u2)) (x := (x1, x2)) (p := pol)
          (pf1 := pf1') (pf2 := pf_prem).
      intuition. eapply in_app_iff; right.
      
      eapply in2_false_illECast.  tauto.  rewrite Heqg'; right; eapply removeEntry_in.
      eauto.
      eauto.
      eauto.

      simpl; erewrite domain_distr; eapply max_distr;erewrite illEC_eq_domain,max_same_domain. instantiate (1 := (domain g1))...
      eauto.
      
      
      (*cons
    (vis_proj
       (newEntries g' (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1)) ++
        illECast g') ++
     ill_proj
       (newEntries g' (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1)) ++
        illECast g')) pf_prem*)
     assert (LEM1 := proj_distr). 
     assert (LEM2 := proj_newEntries_nil).
     assert (LEM3 := proj_illECast_gcons).
     assert (LEM4 :=  gcons_distr).
     assert (LEM5 := gcons_vis_proj_add).
      assert (LEM6 :  forall pf2,
                 cons (ill_proj ((b1, b2, vis, Chan un (pol_cup p0 p2) s3) :: removeEntry (b1, b2) g1)) pf2).
      unfold ill_proj; fold ill_proj; intros; revert dependent pf5; arewrite ill_proj_removeEntry; intros; eapply cons_removeEntry; assert (CON:= H13); eapply LEM4 in CON; destruct CON...
      
      assert (PF := pf4). assert (CON:= H13).
      revert dependent pf_prem;
        erewrite  LEM1,  Heqg', <-newEntries_removeEntry, identif_seclabs_of_dep_relabel,LEM2, app_nil_l.  
      erewrite LEM1, LEM2, app_nil_l. intros.
      eapply LEM4 in CON; destruct CON as [CON1 CON2].
      subst g'. erewrite LEM4. split. eapply LEM3. eauto. intuition.
      eapply LEM5...
      eapply LEM3...
      eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.  
      (*  ~ In (b1, b2) (secLabs p) *)
      intros ABS. assert (ABS2:  exists t : piType, In (b1,b2, hid, t) k). eapply typeCheck_hid... destruct ABS2 as (tt&ABS2); subst k g'. inversion ABS2. inversion H4.
      inversion H4. inversion H5.
      assert (~In (b1, b2, hid, tt) (removeEntry (b1, b2) g1)).
      eapply no_dup_not_in_removeEntry...
      contradiction.
      eauto.
      
      
      assert (DEP: forall nd_pfk, dep_relabel p (domain k) nd_pfk =
                   dep_relabel p (domain g1) nd_pf1).
      erewrite max_dep_relabel...
      erewrite DEP...

      assert (DEP: forall nd_pfk, dep_relabel p (domain k) nd_pfk =
                   dep_relabel p (domain g1) nd_pf1).
      erewrite max_dep_relabel...
      erewrite DEP in TC2.
      
      
      
      
      (* substitution lemma *)
      assert (nd_pfk' :
                NoDup (domain
                       ((b1, b2, vis, Chan un (pol_cup p0 p2) s3)
                     :: removeEntry (b1, b2)
                     (removeEntry (x1, x2)
                                  ((b1, b2, f0, Chan un (pol_cup p0 p2) s3)
            :: (x1, x2, vis, t) :: removeEntry (b1, b2) g1))))).
      unfold removeEntry.
      assert (EQx : pair_eq (x1, x2) (x1, x2)= true).
      eauto. rewrite EQx. fold removeEntry.
      assert (DIFF'' := DIFF2). clear DIFF2.
       assert (DIFF2: pair_eq (b1, b2) (x1, x2) = false).
       eapply pairEq_neq...
       rewrite DIFF2.
       unfold removeEntry; fold removeEntry;
      assert (EQb : pair_eq (b1, b2) (b1, b2)= true).
       eauto. rewrite EQb.
       eapply no_dup_cons_removeEntry...
      apply no_dup_isMap in nd_pfk' as pfk'.
      move TC1 at bottom.
      assert (TC01 := TC1). clear TC1.
      assert (RS:
                removeEntry (b1, b2) ((x1, x2, vis, t) :: g1) =
                (x1, x2, vis, t) :: removeEntry (b1, b2) g1 ).                   
      erewrite <-removeEntry_shift. eauto. eauto.
      revert dependent pf_tmp.
      erewrite RS.
      intros. 
      
      assert
        (TC1: typeCheck
                ((b1, b2, vis, Chan un (pol_cup p0 p2) s3)
                     :: removeEntry (b1, b2)
                     (removeEntry (x1, x2)
                     (((b1, b2, f0, Chan un (pol_cup p0 p2) s3)
            :: (x1, x2, vis, t) :: removeEntry (b1, b2) g1))))
                pfk'  (pmap p x1 x2 b1 b2)).
      eapply typeCheck_substitution.
      eapply no_dup_cons_removeEntry_app_1...
      eauto. eauto. eauto.
      erewrite max_same_domain with (l := domain
       ((b1, b2, f0, Chan un (pol_cup p0 p2) s3)
          :: removeEntry (b1, b2) ((x1, x2, vis, t) :: g1))),<-max_removeEntry_cons.
      assert (LT := H12); rewrite <-Nat.ltb_lt in H12;
        simpl; rewrite H12...
      simpl... simpl...
      rewrite <-removeEntry_shift; intuition.
      eauto.
      subst t. assert (PCP: pol_cup p2 (pol_cup p2 p0) = pol_cup p2 p0). 
      eapply pol_cup_pol_cup.
      assert (PCM: pol_cup p0 p2 = pol_cup p2 p0).
      eapply pol_cup_comm.
      rewrite PCM at 2. rewrite <-PCP.
      erewrite pol_cup_comm with (p1 := p2).
      erewrite pol_cup_comm with (p1 := p2).
      econstructor...
      eauto.
      move TC2 at bottom.

      remember (newEntries g' (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1))) as w.
      assert (nd_pfw : NoDup (domain w)).
      subst w g'. erewrite identif_seclabs_of_dep_relabel,max_removeEntry_cons,<-identif_seclabs_of_dep_relabel.
      eapply newEntries_no_dup...
      erewrite identif_seclabs_of_dep_relabel,<-max_removeEntry_cons,<-identif_seclabs_of_dep_relabel.
      eapply typeCheck_no_dup in TC'' as K. destruct K...
      eauto. eauto. eapply in_g_in_domain... eauto.
      eapply in_g_in_domain...
      apply no_dup_isMap in nd_pfw as pfw.
      
      
      assert (NEU: exists (neutral : typeEnv) (pfn : isMap neutral) (nd_pfn : NoDup (domain neutral)),
         tEnv_split w neutral w pfw pfn pfw).
      eapply split_exists_neutral;eauto...
      destruct NEU as [neutral [pfn [nd_pfn TS2]]];
        eapply split_comm in TS2.
      

      assert (nd_pfk'' :
                NoDup
                  (domain
                  (neutral ++  ((b1, b2, vis, Chan un (pol_cup p0 p2) s3)
           :: removeEntry (b1, b2)
                (removeEntry (x1, x2)
                   ((b1, b2, f0, Chan un (pol_cup p0 p2) s3)
                    :: (x1, x2, vis, t) :: removeEntry (b1, b2) g1)))))).
      erewrite <-removeEntry_shift with (b1:=b1).
      unfold removeEntry; fold removeEntry;
        rewrite pairEq_eq_true, pairEq_eq_true.
      rewrite domain_distr. erewrite no_dup_iff.
      split. eauto.
      split. eauto.
      eapply disjoint_iff...
      erewrite disjoint_commute.
      subst w g'.
      erewrite identif_seclabs_of_dep_relabel,max_removeEntry_cons,<-identif_seclabs_of_dep_relabel.
      eapply disjoint_iff. eapply new_entries_disjoint...
      
      (*max (secLabs p) <=
  max (domain ((b1, b2, vis, Chan un (pol_cup p0 p2) s3) :: removeEntry (b1, b2) g1))*)
      eapply typeCheck_no_dup in TYP as [INCL _].
      unfold secLabs in INCL; fold secLabs in INCL.
      eapply incl_preserves_max...
      intros x IN; unfold incl in INCL; specialize INCL with x; eapply INCL in IN; eapply SD...
      eauto.
      tauto.
      eauto.
      eapply in_g_in_domain...
      eauto.
      
     (*max (secLabs p) <=
  max (domain ((b1, b2, vis, Chan un (pol_cup p0 p2) s3) :: removeEntry (b1, b2) g1))*)
      
      
      eapply no_dup_isMap in nd_pfk'' as pfk''.
      eapply typeCheck_weak2 with (pf1 := pfk'') in TC1.
      
      eapply TPar with (pf1 := pfk'') (pf2 := pf2').
      revert dependent pfk''; rewrite removeEntry_swap; repeat (unfold removeEntry; fold removeEntry; erewrite pairEq_eq_true); intros.

      move w at bottom.
      
      remember (Chan un (pol_cup p0 p2) s3) as t3.
      assert (nd_pfp1 : NoDup (domain ((b1, b2, vis, t3) :: removeEntry (b1, b2) g1))).
      eapply no_dup_cons_removeEntry...
      apply no_dup_isMap in nd_pfp1 as pfp1.

       assert (nd_pfp'': NoDup (domain ((((b1, b2, vis, t3) :: removeEntry (b1, b2) (illECast g1)))))).
      eapply no_dup_cons_removeEntry.
      erewrite illEC_eq_domain...
      eapply no_dup_isMap in nd_pfp'' as pfp''.
      move w at bottom.

      assert (TSAV:
                tEnv_split ((b1, b2, vis, t3) :: removeEntry (b1, b2) g1) ((b1, b2, vis, t3) :: removeEntry (b1, b2) (illECast g1))
                           ((b1, b2, vis, t3) :: removeEntry (b1, b2) g1) pfp1 pfp'' pfp1).
      eapply tEnv_split_add_vis.
      eauto.
      (* type_plus t3 t3 t3 *)
      subst t3.
      rewrite <-pol_cup_id at 3...
      intuition.
      eapply split_illECast_cons...

      assert (EQNE: (newEntries g1 (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1)) = w)).
      subst w g'.
      
      erewrite newEntries_removeEntry.
      eauto. eauto.  eauto. eapply not_in_sl...
      
      revert dependent pfk1; erewrite EQNE; intros.
      revert dependent pfk''; erewrite <-Heqg'; intros. 
      eapply split_distr.
      eauto.
      eapply split_illECast_cons. 
      subst g'. simpl. 
      (*cons
    (((b1, b2, vis, t3) :: vis_proj (removeEntry (b1, b2) g1)) ++
     ill_proj (removeEntry (b1, b2) g1))
    ?pfc@{g':=(b1, b2, vis, t3) :: removeEntry (b1, b2) g1}*)
      assert (pfc1 : isMap (((b1, b2, vis, t3) :: vis_proj (removeEntry (b1, b2) g1)))).
      arewrite vis_proj_removeEntry; try assumption; eapply no_dup_isMap,no_dup_cons_removeEntry,no_dup_vis_proj...
      assert (pfc2 : isMap (ill_proj (removeEntry (b1, b2) g1))).
      eapply no_dup_isMap,no_dup_ill_proj,no_dup_removeEntry_no_dup...
      eapply cons_distr with (pf1 := pfc1) (pf2 := pfc2).
      split.
      subst t3. revert dependent pfc1.
      assert (EQV:(b1, b2, vis, Chan un (pol_cup p0 p2) s3) :: vis_proj (removeEntry (b1, b2) g1) =
                  (vis_proj ((b1, b2, vis, Chan un (pol_cup p0 p2) s3) :: removeEntry (b1, b2) g1))).
      unfold vis_proj; fold vis_proj...
      rewrite EQV. 
      intros.  eapply cons_distr in H13 as [C1 C2]. eapply gcons_vis_proj_add...
      eapply cons_distr in H13 as [C1 C2].
      revert dependent pfc2. arewrite ill_proj_removeEntry.
      intros. eapply cons_removeEntry...
      eauto.
      eauto.
      eauto.
      erewrite <-domain_distr...
      
    (* cons neutral ?pfk *)
      eapply neutral_is_cons,split_comm...

(*disjoint (bv (pmap p x1 x2 b1 b2)) (domain neutral)*)
      rewrite bv_pmap.
      assert (DIS:disjoint (bv(pmap p x1 x2 b1 b2)) (domain w)).
      subst;
        rewrite identif_seclabs_of_dep_relabel in *;
        eapply Peirce; intros ABS;
        eapply not_disjoint in ABS as ([y1 y2] &ABS1 &ABS2);
        eapply in_bv_lt_max with (pf := pfk') in ABS1;
        try rewrite removeEntry_swap in ABS1;
        unfold removeEntry in ABS1; fold removeEntry in *;
        try rewrite pairEq_eq_true in ABS1;
         unfold removeEntry in ABS1; fold removeEntry in *;
        try rewrite pairEq_eq_true in ABS1;
         eapply in_domain_in_g in ABS2 as (ff &tt &ABS2);
        eapply newEntries_gte_max in ABS2;
        try lia;
        try eassumption.
      rewrite max_same_domain with (l := domain g1) in ABS1;
        try lia.
      intros. rewrite <-in_removeEntry_cons_iff; try tauto.
      eapply in_g_in_domain...
      eauto.
      rewrite bv_pmap in DIS. eapply disjoint_commute,disjoint_iff; try eapply disjoint_commute; try eassumption.
      intros. eapply split_domain_m, split_comm...
      

      
      eauto.
      unfold domain; fold domain; eapply NoDup_cons. intros ABS; eapply in_g_in_domain,split_domain_l_2 with (g1 := g1) in H3. contradiction. eauto. 
      eauto.
      right...

      +   (* Top = t3 *)
        assert (TP := H21); move TP at bottom; inversion H21; subst.
        remember Top as t.

        assert (DIFF1: (x1, x2) <> (b1, b2)). intros ABS; inversion ABS; subst; eapply in_g_in_domain,split_domain_l_2 with (g1 := g1) in H3. contradiction. eauto.

        assert (nd_pf_tmp: NoDup (domain ((b1, b2, f0, Top)
                                            :: removeEntry (b1, b2) ((x1, x2, vis, t) :: g1)))).
        erewrite <-removeEntry_shift. eapply no_dup_cons_removeEntry_app_1... intuition.
        apply no_dup_isMap in nd_pf_tmp as pf_tmp.
        assert (TC1 := H14); clear H14.

        
         assert (nd_pf_tmp2: NoDup (domain ((b1, b2, vis, Top)
                                            :: removeEntry (b1, b2) ((x1, x2, vis, t) :: g1)))).
        erewrite <-removeEntry_shift. eapply no_dup_cons_removeEntry_app_1... intuition.
        apply no_dup_isMap in nd_pf_tmp2 as pf_tmp2.
        
        eapply typeCheck_strength_vis with (pf1 := pf_tmp2)  in TC1 as TC1'. 
        
         remember ((x1, x2, vis, t) ::  (b1, b2, vis, Top) :: removeEntry (b1, b2) g1) as k.
      assert (nd_pfk: NoDup (domain k)).
      subst k; unfold domain; fold domain; eapply NoDup_cons_iff; eauto.
      split. intros ABS;inversion ABS. inversion H4; subst; eapply in_g_in_domain in H24; intuition auto.
      eapply in_domain_in_g in H4; destruct H4 as [ff [tt ABS2]]. eapply in_removeEntry,in_g_in_domain in ABS2; intuition auto.
      eapply no_dup_cons_removeEntry...
      
      
      assert (nd_pf' :
                NoDup (domain 
      ((newEntries
          k
          (secLabs (dep_relabel p (domain k) nd_pfk))
          (max (domain k)))
         ++
         illECast k))).
      eapply no_dup_isMap in nd_pfk as pfk.
      eapply no_dup_ne_ic...
      instantiate (1 := pfk).
      eapply typeCheck_impl with (pf1 := pf_tmp2)...
      subst k.
      rewrite <-removeEntry_shift...
      apply no_dup_isMap in nd_pf' as pf'.
      
      assert
        (TC':
           typeCheck 
             ((newEntries
                 k
                 (secLabs (dep_relabel p (domain k) nd_pfk))
                 (max (domain k)))
                ++
                illECast k) pf'
             (dep_relabel p (domain k) nd_pfk)).
      assert (pfk_restore : isMap k).
      eauto.
      eapply typeCheck_dep_relabel2 with (pf := pfk_restore)...

      revert dependent pfk_restore. rewrite Heqk. intros.
      eapply typeCheck_impl with (pf1 := pf_tmp2).
     eapply no_dup_cons_removeEntry, NoDup_cons...
     unfold domain; fold domain. eapply NoDup_cons.
     intros ABS; inversion ABS. inversion H4; subst.
      eapply in_g_in_domain in H24; contradiction.
      eapply in_domain_in_g in H4; destruct H4 as [ff [tt ABS2]]; eapply in_removeEntry in ABS2; eapply in_g_in_domain in ABS2; contradiction.
      eapply no_dup_cons_removeEntry...
      eauto.
      
      (*  forall x : name * name * flag * piType,
  In x ((b1, b2, vis, Top) :: removeEntry (b1, b2) ((x1, x2, vis, t) :: g1)) <->
  In x ((x1, x2, vis, t) :: (b1, b2, vis, Top) :: removeEntry (b1, b2) g1) *)
      subst t. rewrite <-removeEntry_shift with (b1 :=x1).
      eapply cons_cons_iff...
      eauto.


      (*typeCheck
    (newEntries g1 (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1)) ++
     (b1, b2, vis, t) :: removeEntry (b1, b2) g1) pfk1
    (dPar (pmap p x1 x2 b1 b2) (dBang u1 u2 x1 x2 (dep_relabel p (domain g1) nd_pf1)))*)
      assert (MAX : max (domain k) = max (domain g1)). rewrite Heqk.
      assert (MAX2: max (domain g1) = max ( domain ((b1, b2, vis, Top):: removeEntry (b1, b2) g1))). eapply max_same_domain, in_removeEntry_cons_iff,in_g_in_domain...
      erewrite <-rewrite_max_var...
      erewrite <-MAX2; simpl...


      remember  ((b1, b2, vis, Top) :: removeEntry (b1, b2) g1) as g'.
      assert (SD: forall x : name * name, In x (domain g') <-> In x (domain g1)).
      subst g'.
      assert (EQ: forall x : name * name,
   In x (domain g1)  <-> In x
    (domain ((b1, b2, vis, Top) :: removeEntry (b1, b2) g1))).
      eapply in_removeEntry_cons_iff, in_g_in_domain...
      intros x; specialize EQ with x; intuition auto.
      
      (*assert (nd_pf'' :
                NoDup
                  (domain
                     (((x1, x2, vis, t)
                         :: (newEntries g' (secLabs (dep_relabel p (domain k) nd_pfk)) (max (domain k)) ++ illECast g'))))).*)
      assert (NIN: ~ In (x1, x2) (secLabs (dep_relabel p (domain k) nd_pfk))).
      erewrite identif_seclabs_of_dep_relabel, MAX; intro ABS; erewrite in_map_iff in ABS; destruct ABS as [y [ABS _]]; inversion ABS; lia.

       assert (NIND:  ~
  In (x1, x2)
    (domain
       (newEntries g' (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1)) ++
                   illECast g'))).
    rewrite domain_distr, illEC_eq_domain;
      intro IN; eapply in_app_iff in IN; inversion IN as [ABS | ABS]. erewrite identif_seclabs_of_dep_relabel in ABS; eapply incl_newEntries_domain in ABS;erewrite in_map_iff in ABS; destruct ABS as [y [ABS _]]; inversion ABS; lia. rewrite Heqg' in ABS; unfold domain in ABS; fold domain in ABS; inversion ABS. inversion H4; subst b1 b2; eapply in_g_in_domain in H24; intuition auto.
    eapply in_domain_in_g in H4; destruct H4 as [ss [tt ABS2]]; eapply in_removeEntry,in_g_in_domain in ABS2; intuition auto.

      
      assert (nd_pf'' :
                NoDup
                  (domain
                     (((x1, x2, vis, t)
                         :: (newEntries g' (secLabs (dep_relabel p (domain k) nd_pfk)) (max (domain k)) ++ illECast g'))))).
       unfold domain; fold domain; eapply NoDup_cons.
      intros ABS.
      eapply in_domain_in_g in ABS.
      destruct ABS as [ff [tt ABS]].
      eapply in_app_iff in ABS as [ABS | ABS].
      erewrite identif_seclabs_of_dep_relabel in ABS;
        eapply newEntries_gte_max in ABS.
      subst. unfold domain,max; fold domain; intuition.
      eapply in_g_in_domain in ABS; erewrite illEC_eq_domain in ABS; subst g'; repeat simpl in ABS; inverts ABS as EQb; try inversion EQb;
        subst; try contradiction;
          try eapply in_domain_in_g in EQb as (ff1 &tt1 &ABS);
          try eapply in_removeEntry,in_g_in_domain in ABS;
          try contradiction.
      subst k.

      assert (MAX2:
                max (domain ((x1, x2, vis, t) :: g')) = max (domain g')).
      subst g'; try rewrite MAX, <-max_removeEntry_cons; try tauto;
        try eapply in_g_in_domain...
      erewrite newEntries_remove0
        with (p := p) (f := vis) in nd_pf';
        try assumption;
        unfold  illECast in nd_pf'.
      rewrite map_cons in nd_pf'. unfold cast at 1 in nd_pf'.
      repeat rewrite domain_distr in nd_pf';
        unfold domain in nd_pf'; fold domain in nd_pf'.
      repeat rewrite domain_distr.
      eapply NoDup_remove_1...

        (* new version of newEntries_remove *)
      erewrite max_dep_relabel...
      rewrite MAX; try lia...
      intros ABS;
        eapply typeCheck_no_dup in TYP as [INCL _];
        try simpl in INCL;
        try unfold incl in INCL;
        try specialize INCL with (x1, x2); intuition.

      (*        erewrite identif_seclabs_of_dep_relabel; intros x IN;
        eapply in_map_iff in IN as (y &EQ &IN); subst x;
          eapply in_map_iff in IN as ([z1 z2] &EQ &IN); subst y;
            unfold fst, snd.
      assert (EQ: z2 + max (domain ((x1, x2, vis, t) :: g')) - max (domain ((x1, x2, vis, t) :: g')) = z2)by lia.
      rewrite EQ. subst g'; eapply cons_removeEntry_iff.
      eauto. eapply in_g_in_domain...  eapply typeCheck_no_dup...
      intros ABS.
      erewrite identif_seclabs_of_dep_relabel,MAX,in_map_iff in ABS;
        destruct ABS as (e &ABS &_); inversion ABS; subst x2; lia.
       *)
      eapply no_dup_isMap in nd_pf'' as pf''.
      
      assert (TC'':
                typeCheck
                  (cast (x1, x2, vis, t) :: (newEntries g' (secLabs (dep_relabel p (domain k) nd_pfk)) (max (domain k)) ++
                                                        illECast g')) pf'' (dep_relabel p (domain k) nd_pfk)).
      eapply typeCheck_impl with (pf1 := pf'),ne_illEC_var...
      intros z INSL; rewrite identif_seclabs_of_dep_relabel in INSL. eapply in_map_iff in INSL as ((z1 & z2) & EQ & INSL). subst z. simpl.
      assert (INDOM: incl (secLabs (dBang u1 u2 x1 x2 p)) (domain g1)). eapply typeCheck_no_dup...
      eapply incl_iff in INDOM.
       simpl in INDOM. assert (MAXEQ: z2 + max (domain k) - max (domain k) = z2) by lia. rewrite MAXEQ; simpl; eapply INDOM... eauto.

      
       revert dependent pf''.
      erewrite MAX, max_dep_relabel with (nd_pf1 := nd_pf1); unfold cast,castF,flag_eq;simpl;
      intros.

      assert (nd_pf2 :
                NoDup
                  (domain
                     (newEntries g' (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1)) ++
                                 illECast g'))).
      eapply no_dup_domain_cons in nd_pf''.
      erewrite <-MAX, max_dep_relabel...
      eapply no_dup_isMap in nd_pf2 as pf2'.
      assert (nd_pf1' :
                 NoDup
                  (domain
                     ((x1, x2, vis, t):: ((newEntries
                 g'
                 (secLabs (dep_relabel p (domain g1) nd_pf1))
                 (max (domain g1)))
                ++
                illECast  g')))).
      unfold domain; fold domain; eapply NoDup_cons...
      eapply no_dup_isMap in nd_pf1' as pf1'.
      
      assert (nd_pf_prem :
                NoDup
                  (domain
                     ((vis_proj
       (newEntries g' (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1)) ++
        illECast g') ++
     ill_proj
       (newEntries g' (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1)) ++
                   illECast g'))))).
       rewrite domain_distr, no_dup_iff.
      split.
      eapply no_dup_vis_proj...
      split. eapply no_dup_ill_proj...
      eapply disjoint_projections...
      eapply no_dup_isMap in nd_pf_prem as pf_prem.

      assert (TC2:
                typeCheck 
             ((newEntries
                 g'
                 (secLabs (dep_relabel p (domain g1) nd_pf1))
                 (max (domain g1)))
                ++
                illECast  g') pf2'
             (dBang u1 u2 x1 x2 (dep_relabel p (domain k) nd_pfk))).
      eapply TInU with
          (u := (u1, u2)) (x := (x1, x2)) (p := pol)
          (pf1 := pf1') (pf2 := pf_prem).
      intuition. eapply in_app_iff; right.
      
      eapply in2_false_illECast. tauto.  rewrite Heqg'; right; eapply removeEntry_in.
      eauto.
      eauto.
      eauto.
      eauto.

       simpl; erewrite domain_distr; eapply max_distr;erewrite illEC_eq_domain,max_same_domain. instantiate (1 := (domain g1))...
       eauto.
       
      (*cons
    (vis_proj
       (newEntries g' (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1)) ++
        illECast g') ++
     ill_proj
       (newEntries g' (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1)) ++
        illECast g')) pf_prem*)
      assert (LEM1 := proj_distr). 
     assert (LEM2 := proj_newEntries_nil).
     assert (LEM3 := proj_illECast_gcons).
     assert (LEM4 :=  gcons_distr).
     assert (LEM5 := gcons_vis_proj_addT).
      assert (LEM6 :  forall pf2,
                 cons (ill_proj ((b1, b2, vis, Top) :: removeEntry (b1, b2) g1)) pf2).
      unfold ill_proj; fold ill_proj; intros; revert dependent pf5; arewrite ill_proj_removeEntry; intros; eapply cons_removeEntry; assert (CON:= H13); eapply LEM4 in CON; destruct CON... 
      assert (PF := pf4). assert (CON:= H13).
      revert dependent pf_prem;
        erewrite  LEM1, Heqg', <-newEntries_removeEntry,identif_seclabs_of_dep_relabel, LEM2, app_nil_l.
      erewrite LEM1, LEM2, app_nil_l. intros.
      subst g'. erewrite LEM4. split; eapply LEM3. eauto.
      eauto. eapply LEM4 in CON; destruct CON as [CON1 CON2]; eauto. eauto. eauto. eauto. eauto. eauto. eauto.
      eauto. eauto. eauto. eauto. eauto. eauto. eauto.
      eauto.
       (*  ~ In (b1, b2) (secLabs p) *)
      intros ABS.
      specialize typeCheck_hid with (b1, b2) ((x1, x2, vis, t) :: g1) pf3 p as ABS2. apply ABS2 in TC1 as ABS3. destruct ABS3 as (tt&ABS3). inversion ABS3. inversion H4.
      assert (f0 = hid).
      eapply flag_of_map with (x := (b1, b2)) (g := g1)...
      contradiction.
      eauto. eauto.
     

      move MAX at bottom.
      assert (DEP: forall nd_pfk, dep_relabel p (domain k) nd_pfk =
                   dep_relabel p (domain g1) nd_pf1).
      erewrite max_dep_relabel...
      erewrite DEP...
      
      
      (* substitution lemma *)
      assert (nd_pfk' :
                NoDup (domain
                       ((b1, b2, vis, Top)
                     :: removeEntry (b1, b2)
                     (removeEntry (x1, x2)
                                  ((b1, b2, f0, Top)
            :: (x1, x2, vis, t) :: removeEntry (b1, b2) g1))))).
      unfold removeEntry.
      assert (EQx : pair_eq (x1, x2) (x1, x2)= true).
      eauto. rewrite EQx. fold removeEntry.
      assert (DIFF'' := DIFF2). clear DIFF2.
       assert (DIFF2: pair_eq (b1, b2) (x1, x2) = false).
       eapply pairEq_neq...
       rewrite DIFF2.
       unfold removeEntry; fold removeEntry;
      assert (EQb : pair_eq (b1, b2) (b1, b2)= true).
       eauto. rewrite EQb.
       eapply no_dup_cons_removeEntry...
(*       erewrite removeEntry_shift.
       Check no_dup_cons_removeEntry_app_1.
      eapply no_dup_cons_removeEntry_app_1...*)
      apply no_dup_isMap in nd_pfk' as pfk'.
      move TC1 at bottom.
      assert (TC01 := TC1). clear TC1.
      assert (RS:
                removeEntry (b1, b2) ((x1, x2, vis, t) :: g1) =
                (x1, x2, vis, t) :: removeEntry (b1, b2) g1 ).                   
      erewrite <-removeEntry_shift. eauto. eauto.
      revert dependent pf_tmp.
      erewrite RS.
      intros. 
      
      assert
        (TC1: typeCheck
                ((b1, b2, vis, Top)
                     :: removeEntry (b1, b2)
                     (removeEntry (x1, x2)
                     (((b1, b2, f0, Top)
            :: (x1, x2, vis, t) :: removeEntry (b1, b2) g1))))
                pfk'  (pmap p x1 x2 b1 b2)).
      eapply typeCheck_substitution.
      eapply no_dup_cons_removeEntry_app_1...
      eauto. eauto. eauto.
       erewrite max_same_domain with (l := domain
       ((b1, b2, f0, Top)
          :: removeEntry (b1, b2) ((x1, x2, vis, t) :: g1))),<-max_removeEntry_cons.
      assert (LT := H12); rewrite <-Nat.ltb_lt in H12;
        simpl; rewrite H12...
      simpl... simpl...
      rewrite <-removeEntry_shift; intuition.
      eauto.
      
      subst t...
      eapply typeCheck_impl with (pf1 := pf3).
      unfold domain; fold domain; eapply NoDup_cons...
      eapply no_dup_cons_removeEntry_app_1...
      eauto.
      (*forall x : name * name * flag * piType,
  In x ((x1, x2, vis, t) :: g1) <->
  In x ((b1, b2, f0, Top) :: (x1, x2, vis, t) :: removeEntry (b1, b2) g1)*)
      erewrite removeEntry_shift.
      eapply in_removeEntry_cons_iff_0.
      subst; unfold domain; fold domain; eapply NoDup_cons.
      intros ABS. 
      eapply in_g_in_domain in H24; contradiction.
      eauto.
      right. subst... eauto.

      remember (newEntries g' (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1))) as w.
      assert (nd_pfw : NoDup (domain w)).
       subst w g'. erewrite identif_seclabs_of_dep_relabel,max_removeEntry_cons,<-identif_seclabs_of_dep_relabel.
      eapply newEntries_no_dup...
      erewrite identif_seclabs_of_dep_relabel,<-max_removeEntry_cons,<-identif_seclabs_of_dep_relabel.
      eapply typeCheck_no_dup in TC' as K. destruct K...
       erewrite max_dep_relabel in H5...
       eauto. eauto. eapply in_g_in_domain... eauto.
       eapply in_g_in_domain...
      apply no_dup_isMap in nd_pfw as pfw.
      
      assert (NEU: exists (neutral : typeEnv) (pfn : isMap neutral) (nd_pfn : NoDup (domain neutral)),
         tEnv_split w neutral w pfw pfn pfw).
      eapply split_exists_neutral;eauto...
      destruct NEU as [neutral [pfn [nd_pfn TS2]]];
        eapply split_comm in TS2.


      assert (nd_pfk'' :
                NoDup
                  (domain
                  (neutral ++  ((b1, b2, vis, Top)
           :: removeEntry (b1, b2)
                (removeEntry (x1, x2)
                   ((b1, b2, f0, Top)
                    :: (x1, x2, vis, t) :: removeEntry (b1, b2) g1)))))).
            erewrite <-removeEntry_shift with (b1:=b1).
      unfold removeEntry; fold removeEntry;
        rewrite pairEq_eq_true, pairEq_eq_true.
      rewrite domain_distr. erewrite no_dup_iff.
      split. eauto.
      split. eauto.
      eapply disjoint_iff...
      erewrite disjoint_commute.
      subst w g'.
      erewrite identif_seclabs_of_dep_relabel,max_removeEntry_cons,<-identif_seclabs_of_dep_relabel.
      eapply disjoint_iff. eapply new_entries_disjoint...
      
      assert (MAX1: max (secLabs p) <=
  max (domain ((b1, b2, vis, Top) :: (x1, x2, vis, t) :: removeEntry (b1, b2) g1))).
      move TC1' at bottom. 
      eapply incl_preserves_max,typeCheck_no_dup.
      eapply no_dup_cons_removeEntry_app_1...
      revert dependent pf_tmp2.
      rewrite <-removeEntry_shift.
      intros... eauto.

      assert (MAX2:
                max
           (domain
              ((b1, b2, vis, Top)
                 :: (x1, x2, vis, t) :: removeEntry (b1, b2) g1)) =
                max (domain ((b1, b2, vis, Top) :: removeEntry (b1, b2) g1))).
      erewrite <-max_removeEntry_cons.
      erewrite max_same_domain with (l := 
       ((x1,x2):: domain ((b1, b2, vis, Top)
                            ::  removeEntry (b1, b2) g1))).
      unfold max; fold max. erewrite <-max_removeEntry_cons.
      rewrite <-Nat.ltb_lt in  H12.
      rewrite H12...
      eauto. eapply in_g_in_domain...
      unfold domain; fold domain.
      eapply cons_cons_iff.
      eauto.
      eapply in_g_in_domain...
      erewrite <-MAX2...
      tauto.
      eauto.
      eapply in_g_in_domain...
      eauto.

      
      eapply no_dup_isMap in nd_pfk'' as pfk''.
      eapply typeCheck_weak2 with (pf1 := pfk'') in TC1.
      
      eapply TPar with (pf1 := pfk'') (pf2 := pf2').
      revert dependent pfk''; rewrite removeEntry_swap; repeat (unfold removeEntry; fold removeEntry; erewrite pairEq_eq_true); intros.

      move w at bottom.
      
      remember Top as t3.
      assert (nd_pfp1 : NoDup (domain ((b1, b2, vis, t3) :: removeEntry (b1, b2) g1))).
      eapply no_dup_cons_removeEntry...
      (*      erewrite removeEntry_swap in pfp1; unfold removeEntry in pfp1; fold removeEntry in pfp1; rewrite pairEq_eq_true in pfp1.*)
      apply no_dup_isMap in nd_pfp1 as pfp1.
       assert (nd_pfp'': NoDup (domain ((((b1, b2, vis, t3) :: removeEntry (b1, b2) (illECast g1)))))).
      eapply no_dup_cons_removeEntry.
      erewrite illEC_eq_domain...
      eapply no_dup_isMap in nd_pfp'' as pfp''.
      move w at bottom.

      assert (TSAV:
                tEnv_split ((b1, b2, vis, t3) :: removeEntry (b1, b2) g1) ((b1, b2, vis, t3) :: removeEntry (b1, b2) (illECast g1))
                           ((b1, b2, vis, t3) :: removeEntry (b1, b2) g1) pfp1 pfp'' pfp1).
      eapply tEnv_split_add_vis.
      eauto.
      (* type_plus t3 t3 t3 *)
      subst t3...
      intuition.
      eapply split_illECast_cons...

      assert (EQNE: (newEntries g1 (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1)) = w)).
      subst w g'.
       
      erewrite newEntries_removeEntry. eauto. eauto. eauto. eapply not_in_sl...
      assert (EQT : t3 = t). subst...
      revert dependent pfk''; erewrite  <-Heqg'; intros.
      revert dependent pfk1; erewrite <-EQT, EQNE,<-Heqg'; intros.        
      eapply split_distr.
      eauto.
      eapply split_illECast_cons.
      subst g'. unfold vis_proj, ill_proj; fold vis_proj; fold ill_proj.
      (*cons
    (((b1, b2, vis, t3) :: vis_proj (removeEntry (b1, b2) g1)) ++
     ill_proj (removeEntry (b1, b2) g1))
    ?pfc@{g':=(b1, b2, vis, t3) :: removeEntry (b1, b2) g1}*)
      assert (LEM5 := gcons_vis_proj_addT).
      assert (pfc1 : isMap (((b1, b2, vis, t3) :: vis_proj (removeEntry (b1, b2) g1)))).
      arewrite vis_proj_removeEntry; eapply no_dup_isMap,no_dup_cons_removeEntry,no_dup_vis_proj...
      assert (pfc2 : isMap (ill_proj (removeEntry (b1, b2) g1))).
      eapply no_dup_isMap,no_dup_ill_proj,no_dup_removeEntry_no_dup...
      eapply cons_distr with (pf1 := pfc1) (pf2 := pfc2).
      split.
      subst t3. revert dependent pfc1.
      assert (EQV:(b1, b2, vis, Top) :: vis_proj (removeEntry (b1, b2) g1) =
                  (vis_proj ((b1, b2, vis, Top) :: removeEntry (b1, b2) g1))).
      unfold vis_proj; fold vis_proj...
      rewrite EQV.
      intros. eapply cons_distr in H13 as [C1 C2]... 
      eapply cons_distr in H13 as [C1 C2].
      revert dependent pfc2. arewrite ill_proj_removeEntry.
      intros. eapply cons_removeEntry...
      eauto.
      eauto.
      erewrite max_dep_relabel...
      erewrite <-domain_distr...
    (* cons neutral ?pfk *)
      eapply neutral_is_cons,split_comm...

       rewrite bv_pmap.
      assert (DIS:disjoint (bv(pmap p x1 x2 b1 b2)) (domain w)).
      subst;
        rewrite identif_seclabs_of_dep_relabel in *;
        eapply Peirce; intros ABS;
        eapply not_disjoint in ABS as ([y1 y2] &ABS1 &ABS2);
        eapply in_bv_lt_max with (pf := pfk') in ABS1;
        try rewrite removeEntry_swap in ABS1;
        unfold removeEntry in ABS1; fold removeEntry in *;
        try rewrite pairEq_eq_true in ABS1;
         unfold removeEntry in ABS1; fold removeEntry in *;
        try rewrite pairEq_eq_true in ABS1;
         eapply in_domain_in_g in ABS2 as (ff &tt &ABS2);
        eapply newEntries_gte_max in ABS2;
        try lia;
        try eassumption.
      rewrite max_same_domain with (l := domain g1) in ABS1;
        try lia.
      intros. rewrite <-in_removeEntry_cons_iff; try tauto.
      eapply in_g_in_domain...
      eauto.
      rewrite bv_pmap in DIS. eapply disjoint_commute,disjoint_iff; try eapply disjoint_commute; try eassumption.
      intros. eapply split_domain_m, split_comm...


      
      eauto.
      unfold domain; fold domain; eapply NoDup_cons. 
      eauto.
      eauto.
      eauto.
      assert (t1 = Top); subst; inversion H0. tauto. right...


      
 
    - Case lcomL.
      intros.
      remember pf0 as nd_pf. remember pf1 as nd_pf_Out.
      remember pf2 as nd_pf_Inp. subst pf0 pf1 pf2.
      remember pf4 as pf1.  remember pf3 as pf2. 
      subst pf4 pf3.
      
      
      (* H:  g> p1 | p2 -tau-> k> p1' | p2' *)
      (* g1 + g2 = g *)
      (* g1 |- p1 | p2 *)
      (* g1> p1 | p2 -tau-> k1 >p1' | p2' *)
      (* GOAL *)
      (* k1 |- p1' | p2' *)

      (* induction over H *)
      (* g0 = g /a /b *)
      (*  LTS1 :  g0, a : chan lin out t, b : s > p1 --a!b -->
g0, a : Chan lin empty t, b : s1  > p1' *)
      (*  LTS2 : g0, a :  Chan lin inp t, b : s' :: g0) > p2 -- a?b -->
g0, a : Chan lin empty t, b : s > p2' *)
      (* IHLTS1 :  forall g3 bg' k1,
           g3 |- p1 ->
           g3 + bg' = g0, a : chan lin out t, b : s ->
           g3 > p1 --a!b-> k1 > p2 -> 
           k1 |- p2 *)
      (* IHLTS2 :  forall g4 bg'' k1,
           g4 |- p2 ->
           g4 + bg'' = g0, a : chan lin out t, b : s' ->
           g4 > p2 --a?b-> k1 > p2' -> 
           k1 |- p2' *)


      (*g0 = g /a /b
      g1 + g2 = g
      g3 + g4 = g1
      g3 + bg' =  g0, a : Chan lin out t, b : s 
      g4 + bg'' = g0, a:  Chan lin out t, b: Chan lin empty t *)

      (* g4(b) = Chan lin empty t         
      S = chan lin inp t
      T = S *)
                     
                        
      inversion TYP. inversion AFT; subst.
      
     
      eapply nonDivergentProcesses in LTS2; intuition.
      assert (nd_pf2 : NoDup (domain g2)).
      eapply no_dup_split_no_dup_r with (pf2 := pf2) (pf := pf)...
       assert (nd_pf3 : NoDup (domain g3)).
      eapply no_dup_split_no_dup_l with (pf1 := pf0) (pf := pf1)...
      assert (nd_pf4 : NoDup (domain g4)).
      eapply no_dup_split_no_dup_r with (pf2 := pf3) (pf := pf1)...
      assert (DIFF: (a1, a2) <> (b1, b2)).
      eapply nonRecActions2 in H18...
      assert (G5 : exists (f : flag), g5 = removeEntry (a1, a2) (removeEntry (b0, b3) g1)). exists ill...

      + assert (b1 = b0 /\ b2 = b3). 
        eapply identif_payload with (q1:= p1);
          try assumption;
        try eapply typeCheck_no_dup with (g := g3)...
         
      destruct H2; subst b0 b3.
      assert (EQT: t = t0).
      eapply tsub_payload with (pf := pf) in H15 as EX.
      destruct EX as [p3 TYP2].
      inversion TYP2; subst.
      assert (vis = f /\ Chan lin io t = Chan lin p3 t0).
      eapply in_isMap... intuition. inversion H8...
      eauto.
      remember pf3 as pf4. subst pf3.
      remember pf0 as pf3. subst pf0.
      assert (IN1 := H17).
      

      assert (EX: exists t, In (b1, b2, vis, t) g3).
      assert (FLG: flagOf g3 (b1, b2) vis \/ flagOf g3 (b1, b2) hid). eapply typeCheck_lts_out_payload...
      destruct FLG as [FLG1 | FLG2].
      inversion FLG1...
      inversion FLG2.  eapply fsub_hid with (pf := pf1) in H2. inversion H2.
      assert (vis = hid /\ s0 = t2).
      eapply in_isMap... intuition; discriminate.
      eauto.
      destruct EX as [tt3 IN3].
      
      assert (TR: exists tt4 : piType, typeOf g4 (b1, b2) tt4 /\ type_remove s0 tt3 tt4).
      destruct s0. destruct m.
      assert (TR2: exists tt4 : piType, typeOf g4 (b1, b2) tt4 /\ type_plus tt3 tt4 (Chan lin p s0)).
      eapply split_type_plus with (g := g1)...
      destruct TR2 as [tt4 [TYP4 TP]]. exists tt4. unfold type_remove, is_unrestricted; intuition auto.
      destruct tt3, tt4; inversion TP...
      destruct H2 as [pp ABS]; inversion ABS.
      inversion H2.
      eapply tsuper_payload_r with (pf1 := pf3) (pf2 := pf4) in IN1 as TSUP.
      destruct TSUP as [p3 TSUP].
      eapply tsuper_payload with (pf1 := pf3) (pf2 := pf4) in IN1 as TSUP1. destruct TSUP1 as [p0 TSUP1].
      inversion TSUP1; subst.
      inversion TSUP; subst.
      assert (POLEQ: p0 = p3 /\ p3 = p).
      eapply split_plus_un with (pf1 := pf3) (pf2 := pf4) (pf3 := pf1) (b1 := b1) (b2 := b2)...
      intuition; subst.
      assert (vis = f /\ tt3 = Chan un p s0).
      eapply in_isMap... intuition; subst tt3 f. 
      unfold type_remove; exists (Chan un p s0); intuition.
      rewrite <-pol_cup_id at 3...
      eauto.
      eauto.
      exists Top; intuition.
      eapply tsuper_top_r...
      assert (typeOf g3 (b1, b2) Top).
      eapply tsuper_top...
      inversion H2; subst.
      assert (vis = f /\ tt3 = Top).
      eapply in_isMap... intuition; subst tt3 f.
      unfold type_remove; intuition auto.
      
      destruct TR as [tt4 [TYP4 TREM]]. inversion TREM as [TSUB [TP ISUN]].
      (*destruct TP as [tt4 [TYP4 TP]].*)

       assert (EXSP: exists s02, typeOf g2 (b1, b2) s02 /\ type_plus s0 s02 s).
      eapply split_type_plus...
      destruct EXSP as [s02 [TYP2 TP2]].
      
    
      assert (LTRO: exists s01, type_remove tt3 t0 s01).
       eapply tsuper_payload with (pf1 := pf3) in H15 as K1.
      eapply fsuper_vis with (pf1 := pf3) in H15 as [K2 _].
      destruct K1 as [p TYP3a]. inversion K2.
      subst. assert (t1 = Chan lin p t0). eapply type_of_map... subst.
     
      
      eapply typeCheck_lts_out_type_remove with (a1 := a1) (a2 := a2) (b1 := b1) (b2 := b2)  (p := p1).
      eauto.
      subst...
      eauto. eauto. eauto. eauto. 
      destruct LTRO as [s03 TREM3].
      
      eapply no_dup_isMap in nd_pf_Out as pf_Out.
      specialize IHLTS1 with
          (pf := pf_Out) (g1  := g3) (pf1 := pf3).

      assert (RW: removeEntry (a1, a2)
                          (removeEntry (b1, b2)
                                       ((a1, a2, vis, Chan lin out t0) :: (b1, b2, vis, s0) :: g5)) = g5).
      rewrite removeEntry_swap; unfold removeEntry; fold removeEntry. erewrite pairEq_eq_true;unfold removeEntry; fold removeEntry. erewrite pairEq_eq_true...
      eauto.
      
      rewrite <-RW in H18 at 2. clear RW.
      move H18 at bottom.   

      eapply lts_type_remove_lin_out with (pf1 := nd_pf3)  (s0 := tt3) (s01 := s03) in H18 as LTSOUT.
      
      
      move IHLTS1 at bottom.

      assert (nd_pfk3: NoDup (domain (((a1, a2, vis, Chan lin empty t0)
                                         :: (b1, b2, vis, s03) :: removeEntry (a1, a2) (removeEntry (b1, b2) g3))))).
      eapply no_dup_cons_removeEntry_app...
      apply no_dup_isMap in nd_pfk3 as pfk3.
      
      specialize IHLTS1 with
          (pfk1 := pfk3)  (nd_pf1 := nd_pf3). 
      assert (SL: sl_pos p1).
      eapply sl_pos_par_l...

      assert (TSO : exists k2 pfk2, tEnv_split g3 k2 ((a1, a2, vis, Chan lin out t) :: (b1, b2, vis, s) :: g0) pf3 pfk2 pf_Out).
      
      assert (nd_pf' :
                NoDup
                  (domain
                     ((a1, a2, vis, Chan lin out t0)
                        :: (b1, b2, vis, s0)
                        :: removeEntry (a1, a2)
                        (removeEntry (b1, b2) g1)))).
      eapply no_dup_cons_removeEntry_app...
      eapply no_dup_isMap in nd_pf' as pf'.
      assert (nd_pf'' :
                NoDup
                  (domain
                     ((a1, a2, vis, Chan lin empty t0)
                        :: (b1, b2, vis, s02)
                        :: removeEntry (a1, a2)
                        (removeEntry (b1, b2) g2)))).
      eapply no_dup_cons_removeEntry_app...
      eapply no_dup_isMap in nd_pf'' as pf''.
      assert (nd_pf''' :
                NoDup
                  (domain
                     ((a1, a2, vis, Chan lin empty t0)
                        :: (b1, b2, vis, tt4)
                        :: removeEntry (a1, a2)
                        (removeEntry (b1, b2) g4)))).
       eapply no_dup_cons_removeEntry_app...
       eapply no_dup_isMap in nd_pf''' as pf'''.

      eapply split_of_split with
          (pf1 := pf') (pf2 := pf'') (pfw0 := pf'''). (*(pf := pf0) .*)
      eauto.

      (*tEnv_split g3
    ((a1, a2, vis, Chan lin empty t0)
     :: (b1, b2, vis, tt4) :: removeEntry (a1, a2) (removeEntry (b1, b2) g4))
    ((a1, a2, vis, Chan lin out t0)
     :: (b1, b2, vis, s0) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) pf3 pf'''
    pf'*)
      eapply type_of_out_action in LTSOUT as K; destruct K as [tt [IN3a | ABS]].
      eapply lts_vis_subject with (a1 :=a1) (a2 := a2) in LTSOUT as FVIS.
      inversion IN3a; inversion FVIS; subst.
      assert (EQ: f = vis /\ Chan lin out tt = t2).
      eapply in_isMap... destruct EQ; subst.

      destruct tt4. destruct m.
      
     inversion TREM; destruct H7; inversion H7; subst.
     eapply split_new_lin_lin.
     eauto. eauto.
     assert (tt = t0). 
     eapply tsuper_payload with (pf1 := pf3) in H15 as [pp1 IN3'].
     inversion IN3'. subst.
     assert (Chan lin out tt = Chan lin pp1 t0).
     eapply type_of_map with (g := g3)...
     inversion H11... eauto. subst...
     eauto. eauto. eauto. eauto. eauto. eauto.
     
     inversion TREM; destruct H7; inversion H7; subst.
     assert (ISUN1: is_unrestricted (Chan un (pol_cup p0 p) tt4)).
     eapply un_is_unrestricted.
     eapply H8 in ISUN1; inversion ISUN1.
     revert dependent pf'; rewrite <-H11; intros.
     eapply split_new_lin_un.
     eauto. eauto.
     assert (tt = t0). 
     eapply tsuper_payload with (pf1 := pf3) in H15 as [pp1 IN3'].
     inversion IN3'. subst.
     assert (Chan lin out tt = Chan lin pp1 t0).
     eapply type_of_map with (g := g3)...
     inversion H12... eauto. subst...
     eauto. eauto.
     assert (p0 = p /\ p = (pol_cup p0 p)).
      inversion TYP4. subst.
     eapply split_plus_un with (pf1 := pf3) (pf2 := pf4) (pf3 := pf1).
     eauto.  eauto. eauto. eauto.
     destruct H10; subst...
     eauto. eauto.

     inversion TREM; destruct H7; inversion H7; subst.
     assert (tt = t0). 
     eapply tsuper_payload with (pf1 := pf3) in H15 as [pp1 IN3'].
     inversion IN3'. subst.
     assert (EQ: Chan lin out tt = Chan lin pp1 t0).
     eapply type_of_map with (g := g3)...
     inversion EQ...
     eauto.
     subst.
     eapply split_new_lin_top.
     eauto. eauto. eauto. eauto. eauto. eauto. eauto.
     eauto. eauto.
     destruct ABS as [ABS | ABS].
     inversion ABS; subst.
      eapply tsuper_payload with (pf1 := pf3) in H15 as [pp1 IN3'].
      assert (Chan un out tt = Chan lin pp1 t0).
      eapply type_of_map with (g := g3)...
      inversion H3... eauto.
            eapply tsuper_payload with (pf1 := pf3) in H15 as [pp1 IN3'].
      assert (Chan un io tt = Chan lin pp1 t0).
      eapply type_of_map with (g := g3)...
      inversion H2... eauto.

      subst t0.
        assert (not_lin_is_unrestricted:  forall p t,
                is_unrestricted (Chan lin p t) -> False).
     unfold is_unrestricted; intros. destruct H2 as [pp [tt ABS]]; inversion ABS...
      revert dependent pf'. 
      rewrite removeEntry_shift. intros.
      revert dependent pf''. rewrite removeEntry_shift; intros.
      subst g0. revert dependent pf_Out.  rewrite removeEntry_shift.
      intros.
      eapply tEnv_split_add_vis.
      eauto. eauto. intros ABS.  eapply not_lin_is_unrestricted in ABS; intuition.
      eapply tEnv_split_add_vis.
      eauto. eauto. intros.
      destruct H2 as [pp [tt EQ]]. subst.
      inversion TP2; subst.
      assert (p0 = p3 /\ p3 = (pol_cup p0 p3)).
      inversion TYP2.
      eapply split_plus_un with (pf1 := pf1) (pf2 := pf2) (pf3 := pf).
      eauto. eauto. eauto. eauto. destruct H2; subst. rewrite <-H3; intuition.
      eauto. eauto. eauto. eauto.
     
      destruct TSO as [k2 [pfk2 TSK]].
      specialize IHLTS1 with (pf2 := pfk2).
      intuition.
      assert (TC1 := H3); clear H3.


      (* s1 = s - t*)
      (* s0 = tt3 + tt4 *)
      (* s2 = s0 - t *)
      (* s03 = tt3 - t *)
      (* s = s0 + s02 *)

      (* s1 = tt4 + ??? *)
      (* s1 = s - t = (s0 + s02) - t = ((tt3 + tt4) + s02) -t *)          
     

     

      assert (LTRI: exists s04, type_plus tt4 t0 s04 /\
             (is_unrestricted s0 -> s03 = s04 /\ s04 = s0)).
      destruct t0. destruct m.
      assert (LT: exists s04, type_plus tt4 (Chan lin p t0) s04).
      inversion TREM3.
     
      eapply plus_sub_exists. eapply type_plus_comm...
      eauto.
      destruct LT as [s04 TP4'].
      exists s04. split. tauto.
      intros. destruct  H2 as [pp [tt  ABS]]. inversion H13.
      move H13 at bottom.
      subst; inversion H13; inversion H2. 
      inversion TREM3. inversion H13. move ISUN at bottom. 
      assert (s03 = tt3 /\ s2 = s0 /\ tt4 = s0).
      assert (is_unrestricted tt3).
      inversion H2; subst; eapply un_is_unrestricted.
      assert (is_unrestricted s0).
      inversion H7; subst; eapply un_is_unrestricted.
      intuition.
      intuition. subst.
      move TP at bottom.
      assert (s0 = tt3).
      destruct s0.
      assert (m = un). inversion H7...
      subst m. 
       eapply tsuper_payload with (pf1 := pf3) in IN1 as IN3'.
      eapply tsuper_payload with (pf1 := pf4) in IN1 as IN4'.
      destruct IN3' as [pp3 TYP3'];
        destruct IN4' as [pp4 TYP4'];
        inversion TYP3'; inversion TYP4'; clear TYP3'; clear TYP4'; subst.
      assert (vis = f /\  tt3 =  Chan un pp3 s0).
      eapply in_isMap...
      intuition; subst.
      assert (pp3 = pp4 /\ pp4 = p0).
      eapply split_plus_un with (pf1 := pf3) (pf2 := pf4) (pf3 := pf1) (b1 := b1) (b2 := b2)...
      intuition; subst...
      eapply split_comm...
      eauto.
      inversion H3...
      subst tt3. exists s0...
      split.
      eapply type_plus_comm...
      assert (is_unrestricted s0).
      inversion H7; subst; eapply un_is_unrestricted.
      intuition.
      inversion H13; intuition; inversion H2; inversion H7; inversion TP; subst; try discriminate. exists Top...  all: try discriminate.
      
      
      (*inversion TREM3; 
      eapply plus_sub_exists. eapply type_plus_comm...
      eauto.*)
      destruct LTRI as [s04 [TP4 ISUN4]].
      
      move H19 at bottom.
        assert (RW: removeEntry (a1, a2)
                          (removeEntry (b1, b2)
                                       ((a1, a2, vis, Chan lin inp t0) :: (b1, b2, vis, s2) :: g5)) = g5).
        rewrite <- removeEntry_shift; unfold removeEntry; fold removeEntry.
        rewrite pairEq_eq_true, pairEq_eq_true...
        eauto.
        rewrite <-RW in H19 at 2.
       eapply lts_type_plus_lin_in with (pf1 := nd_pf4) (s01 := tt4) (s0 := s04) in H19 as LTSIN.
       
      
      
      move IHLTS2 at bottom.
      eapply no_dup_isMap in nd_pf_Inp as pf_Inp.
      specialize IHLTS2 with
          (pf := pf_Inp)  (pf1 := pf4) (nd_pf1 := nd_pf4). 
      assert (SL2: sl_pos q1).
      eapply sl_pos_par_r...

     
      assert (EXSP2: exists s0t,
                type_remove s0 t s0t).
     eapply typeCheck_lts_out_type_remove with (pf := pf1).
     eauto.
     subst...
     eauto. econstructor...
     destruct EXSP2 as [s0t TREM2].
    
     
     assert (EXSP2: exists r4,
                type_plus tt4 r4 s1 /\ type_sub tt4 s1 /\
            (is_unrestricted s1 -> r4 = s1)).
     **  inversion H; inversion H13;  inversion TREM2; subst.
        move TP at bottom. move TP2 at bottom.  move TP4 at bottom. clear  LTSIN .
        destruct H3, H8, H10.

        apply T_Entry in H17 as TYP1. move TYP1 at bottom.
        apply T_Entry in IN3 as TYP3. move TYP3 at bottom.
        move TYP4 at bottom.
        assert (PAYLOAD : t0 = t0)...
        
        destruct t0. destruct m.
        destruct p.
        *** inversion H3; inversion H23; subst...
            inversion H8; inversion H24; subst...
            inversion TP; inversion TP2; subst...
            **** assert (EXR: exists r, pol_plus p0 p7 r).
                 destruct p0; eauto; inversion H22; inversion H29;subst; try discriminate...
            destruct EXR as [r PPR].
            exists (Chan lin r t0).
             assert (ASSOC: pol_plus p3 r p).
            destruct p3; eauto; inversion H22; inversion H29; inversion PPR; subst; try discriminate...
            split. econstructor...
            split.  eapply pol_plus_type_sub...
            intros ABS; eapply not_lin_is_unrestricted in ABS; intuition.
            ****
              assert (tt4 = Chan lin empty t0).
              inversion TP; inversion H22; subst...
              subst...
            ****
              assert (tt4 = Chan lin empty t0).
              inversion TP2; inversion H22; inversion TP; subst; try discriminate || inversion H31; subst.  all: try inversion H28;subst...
        *** inversion H3; inversion H23; subst...
            inversion H8; inversion H24; subst...
            inversion TP; inversion TP2; subst...
            inversion H29; inversion H22; subst.
            inversion TP4; inversion H26.
            exists (Chan lin empty t0)...
            inversion TP2; inversion H22.
            inversion TP4; inversion H24; subst...
            exists (Chan lin empty t0).
            split. econstructor...
            split. eapply Ts_id.
            intros ABS; eapply not_lin_is_unrestricted in ABS; intuition. 
       *** inversion H3; inversion H23; subst...
            inversion H8; inversion H24; subst...
            inversion TP; inversion TP2; subst...
            inversion H29; inversion H22; subst.
            inversion TP4; inversion H26.
            exists (Chan lin empty t0)...
            inversion TP2; inversion H22.
            inversion TP4; inversion H24; subst...
            exists (Chan lin empty t0).
            split. econstructor...
            split. eapply Ts_id.
            intros ABS; eapply not_lin_is_unrestricted in ABS; intuition. 
       *** inversion H3; inversion H23; inversion TP4; subst...
           inversion H3; inversion H23; inversion TP4; inversion H27; subst...
        *** inversion H3; inversion H16; inversion TP; inversion TP2; subst...
           all:try discriminate.
           inversion H27.
           rewrite H11,<-H29,H20; subst...
           exists (Chan un (pol_cup p4 p7) t1).
           assert (EQ: pol_cup p5 (pol_cup p4 p7) =
                       pol_cup (pol_cup p4 p5) p7).
           destruct p4, p5, p7... 
           rewrite <-EQ.
           split. econstructor...
           split. eapply pol_cup_type_sub...
           intros _.
           assert (p4 = p5 /\ p5 = pol_cup p4 p5).  
           inversion TYP4.

           eapply split_plus_un with (pf1 := pf3) (pf2 := pf4) (pf3 := pf1) (b1 := b1) (b2 := b2).
           eauto.  eauto. eauto. eauto.
           intuition; subst.
           assert (EQ2: pol_cup p5 p7 = pol_cup p5 (pol_cup p5 p7)).
           destruct p5, p7; inversion H9; subst... 
           rewrite <-EQ2...
           
        *** inversion TP4; inversion H3; subst...
     ** destruct EXSP2 as [r4 [TP4' [TSUB4' ISUN4']]].

      assert (nd_pf1' :
                NoDup
                  (domain
                     ((a1, a2, vis, Chan lin inp t0)
                        :: (b1, b2, vis, tt4)
                        :: removeEntry (a1, a2)
                        (removeEntry (b1, b2) g1)))).
      eapply no_dup_cons_removeEntry_app...
        eapply no_dup_isMap in nd_pf1' as pf1'.
       assert (nd_pf'' :
                NoDup
                  (domain
                     ((a1, a2, vis, Chan lin empty t0)
                        :: (b1, b2, vis, r4)
                        :: removeEntry (a1, a2)
                        (removeEntry (b1, b2) g2)))).
       eapply no_dup_cons_removeEntry_app...
      eapply no_dup_isMap in nd_pf'' as pf''.
     
     
      move IHLTS2 at bottom.
     assert (TSO : exists k'' pfk'', tEnv_split g4 k'' ((a1, a2, vis, Chan lin inp t) :: (b1, b2, vis, s1) :: g0) pf4 pfk'' pf_Inp).
     inversion TYP4. subst. assert (IN4 := H2); clear H2 TYP4.
     eapply typeCheck_lts_in with (g1 := g4) in LTSIN as IN4a.
     destruct IN4a as [mm [tt [TYP4a | ABS]]].
     inversion TYP4a. subst. assert (IN4a := H2); clear H2 TYP4a.
     assert (EQ: f0 = vis /\ mm = lin /\ tt = t0).
     eapply tsuper_payload with (pf1 := pf4) in H15 as K.
     destruct K as [pp1 TYP4]; inversion TYP4; subst.
     eapply fsuper_vis with (pf1 := pf4) in H15 as [K _].
     inversion K; subst.
     assert (f0 = vis). eapply flag_of_map with (g := g4)...
     assert (EQ: Chan mm inp tt =  Chan lin pp1 t0). eapply type_of_map with (g := g4)...
     inversion EQ;  intuition.
     eapply split_comm... eapply split_comm...
     destruct EQ as [EQ1 [EQ2 EQ3]]; subst.
     
     destruct tt4. destruct m. 
      assert (nd_pf''' :
                NoDup
                  (domain
                     ((a1, a2, vis, Chan lin empty t0)
                        :: (b1, b2, vis, Chan lin empty tt4)
                        :: removeEntry (a1, a2)
                        (removeEntry (b1, b2) g3)))).
      eapply no_dup_cons_removeEntry_app...
      eapply no_dup_isMap in nd_pf''' as pf'''.
      eapply split_of_split with (pf1 := pf1') (pf2 := pf'') (pfw0 := pf''').
      eauto.
      (*tEnv_split g4
    ((a1, a2, vis, Chan lin empty t0)
     :: (b1, b2, vis, Chan lin empty tt4)
        :: removeEntry (a1, a2) (removeEntry (b1, b2) g3))
    ((a1, a2, vis, Chan lin inp t0)
     :: (b1, b2, vis, Chan lin p tt4)
        :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) pf4 pf''' pf1'*)
      eapply split_new_lin_lin.
      eauto. eapply split_comm...
      eauto. eauto. eauto. eauto. 
      assert (flagOf g4 (b1, b2) vis).
      eapply fsuper_vis with (pf2 := pf4) in IN1; intuition.
      eauto. inversion H2; subst.
      assert (f = vis). eapply flag_of_map with (g := g4)...
      subst...
      eauto. eauto.
      
      
      assert (EQ1: ((a1, a2, vis, Chan lin inp t0)
                 :: (b1, b2, vis, Chan lin p tt4) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) =
              ((a1, a2, vis, Chan lin inp t0)
                 :: removeEntry (a1, a2) ((b1, b2, vis, Chan lin p tt4) :: removeEntry (b1, b2) g1))).
      erewrite removeEntry_shift...
       assert (EQ2: ((a1, a2, vis, Chan lin empty t0)
                 :: (b1, b2, vis, r4) :: removeEntry (a1, a2) (removeEntry (b1, b2) g2)) =
              ((a1, a2, vis, Chan lin empty t0)
                 :: removeEntry (a1, a2) ((b1, b2, vis, r4) :: removeEntry (b1, b2) g2))).
       erewrite removeEntry_shift...
       subst g0.
        assert (EQ3: ((a1, a2, vis, Chan lin inp t0)
                 :: (b1, b2, vis, s1) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)) =
              ((a1, a2, vis, Chan lin inp t0)
                 :: removeEntry (a1, a2) ((b1, b2, vis, s1) :: removeEntry (b1, b2) g))).
              erewrite removeEntry_shift...
      revert dependent pf1'; revert dependent pf''; revert dependent pf_Inp.
      erewrite EQ1,EQ2,EQ3. clear EQ1 EQ2 EQ3.
      intros.

      eapply tEnv_split_add_vis.
      eapply no_dup_cons_removeEntry...
      econstructor...
      intros ABS; unfold is_unrestricted in ABS; destruct ABS as [ttt [yyy ABS]]; inversion ABS.
      eapply tEnv_split_add_vis.
      eauto.
      eauto.
      (* is_unrestricted s1 -> tt4 = r4 /\ r4 = s1 *)
      intros ABS; inversion TP4'; subst.
      eapply not_lin_is_unrestricted in ABS; intuition.
      eauto.

      assert (EQ: s1 = s /\ s = Chan un p tt4).
      inversion H; destruct H3.
      eapply tsub_un with (pf := pf1) in IN4 as K1. inversion K1; subst.
       eapply tsub_un with (pf := pf) in  H8 as K2. inversion K2; subst.
       assert (s = Chan un p tt4).
       eapply type_of_map with (g := g)...
       assert (s1 = Chan un p tt4).
       subst; assert (is_unrestricted (Chan un p tt4)). eapply un_is_unrestricted. intuition.
       subst... eauto. eapply split_comm...
       destruct EQ; subst.
       assert (r4 = Chan un p tt4).
       eapply ISUN4', un_is_unrestricted...
       subst.
      assert (nd_pf''' :
                NoDup
                  (domain
                     ((a1, a2, vis, Chan lin empty t0)
                        :: (b1, b2, vis, Chan un p tt4)
                        :: removeEntry (a1, a2)
                        (removeEntry (b1, b2) g3)))).
      eapply no_dup_cons_removeEntry_app...
      eapply no_dup_isMap in nd_pf''' as pf'''.
      eapply split_of_split with (pf1 := pf1') (pf2 := pf'') (pfw0 := pf''').
      eauto.
      (*tEnv_split g4
    ((a1, a2, vis, Chan lin empty t0)
     :: (b1, b2, vis, s1) :: removeEntry (a1, a2) (removeEntry (b1, b2) g3))
    ((a1, a2, vis, Chan lin inp t0)
     :: (b1, b2, vis, Chan un p tt4) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1))
    pf4 pf''' pf1'*)
      eapply split_new_lin_un.
      eauto. eapply split_comm...
      eauto. eauto. eauto. eauto. 
      assert (flagOf g4 (b1, b2) vis).
      eapply fsuper_vis with (pf2 := pf4) in IN1; intuition.
      eauto. 
      assert (f = vis). eapply flag_of_map with (g := g4)...
      subst...
      eauto. 
      
      
      assert (EQ1: ((a1, a2, vis, Chan lin inp t0)
                 :: (b1, b2, vis, Chan un p tt4) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) =
              ((a1, a2, vis, Chan lin inp t0)
                 :: removeEntry (a1, a2) ((b1, b2, vis, Chan un p tt4) :: removeEntry (b1, b2) g1))).
      erewrite removeEntry_shift...
       assert (EQ2: ((a1, a2, vis, Chan lin empty t0)
                 :: (b1, b2, vis, Chan un p tt4) :: removeEntry (a1, a2) (removeEntry (b1, b2) g2)) =
              ((a1, a2, vis, Chan lin empty t0)
                 :: removeEntry (a1, a2) ((b1, b2, vis, Chan un p tt4) :: removeEntry (b1, b2) g2))).
       erewrite removeEntry_shift...
       subst g0.
        assert (EQ3: ((a1, a2, vis, Chan lin inp t0)
                 :: (b1, b2, vis, Chan un p tt4) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)) =
              ((a1, a2, vis, Chan lin inp t0)
                 :: removeEntry (a1, a2) ((b1, b2, vis, Chan un p tt4) :: removeEntry (b1, b2) g))).
              erewrite removeEntry_shift...
      revert dependent pf1'; revert dependent pf''; revert dependent pf_Inp.
      erewrite EQ1,EQ2,EQ3. clear EQ1 EQ2 EQ3.
      intros.

      eapply tEnv_split_add_vis.
      eapply no_dup_cons_removeEntry...
      econstructor...
      intros ABS; eapply not_lin_is_unrestricted in ABS; intuition.   eapply tEnv_split_add_vis.
      eauto.
      eauto.
      (* is_unrestricted s1 -> tt4 = r4 /\ r4 = s1 *)
      intros ISUN1; inversion TP4'; subst...
      eauto.

      assert (EQ: s1 = s /\ s = Top).
      inversion H; destruct H3.
      eapply tsub_top with (pf := pf1) in IN4 as K1. inversion K1; subst.
       eapply tsub_top with (pf := pf) in  H8 as K2. inversion K2; subst.
       assert (s = Top).
       eapply type_of_map with (g := g)...
       inversion H3; subst. split... inversion H16. inversion H14. eauto. eapply split_comm...
       destruct EQ; subst.
       assert (r4 = Top).
       inversion TP4'; subst...
       subst.
       
      assert (nd_pf''' :
                NoDup
                  (domain
                     ((a1, a2, vis, Chan lin empty t0)
                        :: (b1, b2, vis, Top)
                        :: removeEntry (a1, a2)
                        (removeEntry (b1, b2) g3)))).
      eapply no_dup_cons_removeEntry_app...
      eapply no_dup_isMap in nd_pf''' as pf'''.
      eapply split_of_split with (pf1 := pf1') (pf2 := pf'') (pfw0 := pf''').
      eauto.
      (*tEnv_split g4
    ((a1, a2, vis, Chan lin empty t0)
     :: (b1, b2, vis, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g3))
    ((a1, a2, vis, Chan lin inp t0)
     :: (b1, b2, vis, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) pf4
    pf''' pf1'*)
      eapply split_new_lin_top.
      eauto. eapply split_comm...
      eauto. eauto. eauto. eauto. 
      assert (flagOf g4 (b1, b2) vis).
      eapply fsuper_vis with (pf2 := pf4) in IN1; intuition.
      eauto. 
      assert (f = vis). eapply flag_of_map with (g := g4)...
      subst...
      eauto. 
      
      
      assert (EQ1: ((a1, a2, vis, Chan lin inp t0)
                 :: (b1, b2, vis, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) =
              ((a1, a2, vis, Chan lin inp t0)
                 :: removeEntry (a1, a2) ((b1, b2, vis, Top) :: removeEntry (b1, b2) g1))).
      erewrite removeEntry_shift...
       assert (EQ2: ((a1, a2, vis, Chan lin empty t0)
                 :: (b1, b2, vis, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g2)) =
              ((a1, a2, vis, Chan lin empty t0)
                 :: removeEntry (a1, a2) ((b1, b2, vis, Top) :: removeEntry (b1, b2) g2))).
       erewrite removeEntry_shift...
       subst g0.
        assert (EQ3: ((a1, a2, vis, Chan lin inp t0)
                 :: (b1, b2, vis, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)) =
              ((a1, a2, vis, Chan lin inp t0)
                 :: removeEntry (a1, a2) ((b1, b2, vis, Top) :: removeEntry (b1, b2) g))).
              erewrite removeEntry_shift...
      revert dependent pf1'; revert dependent pf''; revert dependent pf_Inp.
      erewrite EQ1,EQ2,EQ3. clear EQ1 EQ2 EQ3.
      intros.

      

      eapply tEnv_split_add_vis.
      eapply no_dup_cons_removeEntry...
      econstructor...
      intros ABS; eapply not_lin_is_unrestricted in ABS; intuition.   eapply tEnv_split_add_vis.
      eauto.
      eauto.
      (* is_unrestricted s1 -> tt4 = r4 /\ r4 = s1 *)
      intros ISUN1; inversion TP4'; subst...
      eauto.

      inversion ABS; subst. 
      eapply type_of_in_action in LTSIN as LIN.
      destruct LIN as [ttt [ABS1 | [ABS1 | ABS1]]].
      assert (EQ: Chan mm io tt = Chan lin inp ttt).
      eapply type_of_map with (g := g4)...
      inversion EQ.
      assert (EQ: Chan mm io tt = Chan un inp ttt).
      eapply type_of_map with (g := g4)...
      inversion EQ.
      assert (EQ: Chan mm io tt = Chan un io ttt).
      eapply type_of_map with (g := g4)...
      inversion EQ. subst.
      eapply tsub_un with (pf := pf1) in H2.
      assert (EQ2: Chan lin io t0 = Chan un io ttt).
       eapply type_of_map with (g := g1)...
       inversion EQ2.
       eapply split_comm... eauto.
      
       destruct TSO as [k'' [pfk'' TSK'']].
       assert (nd_pfk4 :
                 NoDup (domain
                          (((a1, a2, vis, Chan lin empty t0)
                              :: (b1, b2, vis, s04) :: removeEntry (a1, a2) (removeEntry (b1, b2) g4))))).
       eapply no_dup_cons_removeEntry_app...
       eapply no_dup_isMap in nd_pfk4 as pfk4.
      specialize IHLTS2 with (pf2 := pfk'') (pfk1 := pfk4).
       move IHLTS2 at bottom.
       assert (sl_pos q1). eapply sl_pos_par_r...
       intuition.
       move TC1 at bottom.
       assert (TC2 := H7); clear H7.


       eapply TPar with (pf1 := pfk3) (pf2 := pfk4).
        assert (EQ1: ((a1, a2, vis, Chan lin empty t0)
                 :: (b1, b2, vis, s03) :: removeEntry (a1, a2) (removeEntry (b1, b2) g3)) =
              ((a1, a2, vis, Chan lin empty t0)
                 :: removeEntry (a1, a2) ((b1, b2, vis, s03) :: removeEntry (b1, b2) g3))).
      erewrite removeEntry_shift...
       assert (EQ2: ((a1, a2, vis, Chan lin empty t0)
                 :: (b1, b2, vis, s04) :: removeEntry (a1, a2) (removeEntry (b1, b2) g4)) =
              ((a1, a2, vis, Chan lin empty t0)
                 :: removeEntry (a1, a2) ((b1, b2, vis, s04) :: removeEntry (b1, b2) g4))).
       erewrite removeEntry_shift...
       subst g0.
        assert (EQ3: ((a1, a2, vis, Chan lin empty t0)
                 :: (b1, b2, vis, s0) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) =
              ((a1, a2, vis, Chan lin empty t0)
                 :: removeEntry (a1, a2) ((b1, b2, vis, s0) :: removeEntry (b1, b2) g1))).
        erewrite removeEntry_shift...
         subst g5. 
      revert dependent pfk3; revert dependent pfk4; revert dependent pfk1.
     erewrite EQ1,EQ2,EQ3. clear EQ1 EQ2 EQ3.
     intros.

      eapply tEnv_split_add_vis.
      eapply no_dup_cons_removeEntry...
      econstructor...
      intros ABS; eapply not_lin_is_unrestricted in ABS; intuition.
       eapply tEnv_split_add_vis.
       eauto.
       (* type_plus s03 s04 s0 *)
       move TP4 at bottom.
       inversion TREM as [_ [TP0 _]]; inversion TREM3 as [_ [TP3 _]]. 
       destruct t0. destruct m. destruct p.
       try inversion TP4;  inversion TP3; inversion H10; inversion H20; subst...
       try inversion TP0; inversion TP4;  inversion TP3; inversion H10; inversion H20; inversion H11; subst; try discriminate; eauto;
       inversion H11; inversion H23; inversion H27; inversion H16; inversion H24; inversion H3; subst; try discriminate...
       try inversion TP0; inversion TP4;  inversion TP3; inversion H10; inversion H20; inversion H11; subst; try discriminate; eauto;
         inversion H11; inversion H23; inversion H27; inversion H16; inversion H24; inversion H3; subst; try discriminate...
       try inversion TP0; inversion TP4;  inversion TP3; inversion H10; inversion H20; inversion H11; subst; try discriminate; eauto;
         inversion H11; inversion H23; inversion H27; inversion H16; inversion H24; inversion H3; subst; try discriminate...
       try inversion TP0; inversion TP4;  inversion TP3; inversion H10; inversion H20; inversion H11; subst; try discriminate; eauto.
      inversion H21; inversion H9; subst.
      assert (EQ : pol_cup p7 (pol_cup p3 p) =
                   (pol_cup (pol_cup p p7) p3)).
      destruct p3,p,p7...
      erewrite <-EQ...
      inversion TP4; inversion TP3; inversion TP0; subst...
      (* is_unrestricted s0 -> s03 = s04 /\ s04 = s0 *)
      intuition.
      all:eauto.

     ** eauto.
     ** eauto.
     ** assert (EX: exists (m : mode) (t : piType),
                   typeOf g4 (a1, a2) (Chan m inp t) \/ typeOf g4 (a1, a2) (Chan m io t)). eapply typeCheck_lts_in...
        destruct EX as [mm [tt [TYP1' | TYP1']]].
        inversion TYP1'; subst.
         eapply tsuper_payload_r with (pf2 := pf4) in H15 as IN4'.
       destruct IN4' as [pp4 TYP4']; inversion TYP4'; subst.
      assert (f = f0 /\  Chan mm inp tt =  Chan lin pp4 t0).
      eapply in_isMap...
      destruct H7; inversion H8; subst.
      assert (flagOf g3 (a1, a2) vis /\ flagOf g4  (a1, a2) vis).
      eapply fsuper_vis...
      destruct H7 as [_ FY]; inversion FY; subst.
       assert (f0 = vis /\  Chan lin inp t0 =  t).
      eapply in_isMap...
      intuition. subst...
      eauto.
      inversion TYP1'; subst.
       eapply tsuper_payload_r with (pf2 := pf4) in H15 as IN4'.
       destruct IN4' as [pp4 TYP4']; inversion TYP4'; subst.
      assert (f = f0 /\  Chan mm io tt =  Chan lin pp4 t0).
      eapply in_isMap...
      destruct H7; inversion H8; subst.
      assert (EX: exists (m : mode) (t : piType),
                 typeOf g3 (a1, a2) (Chan m out t) \/ typeOf g3 (a1, a2) (Chan m io t)). eapply typeCheck_lts_out...
      
       eapply tsuper_payload with (pf1 := pf3) in H15 as IN4''.
       destruct IN4'' as [pp3 TYP3']; inversion TYP3'; subst.
       destruct EX as [mm' [tt' [TYP1'' | TYP1'']]].
      inversion TYP1''; subst.
      assert (f = f1 /\  Chan lin pp3 t0 =  Chan mm' out tt').
      eapply in_isMap...
      intuition; inversion H12; subst.
      assert (ABS: pol_plus out io io).
      eapply split_plus_lin with (pf1 := pf3) (pf2 := pf4) (pf3 := pf1) (b1 := a1) (b2 := a2)...
      inversion ABS.
      inversion TYP1''; subst.
       assert (f = f1 /\  Chan lin pp3 t0 =  Chan mm' io tt').
      eapply in_isMap...
      intuition; inversion H12; subst.
      assert (ABS: pol_plus io io io).
      eapply split_plus_lin with (pf1 := pf3) (pf2 := pf4) (pf3 := pf1) (b1 := a1) (b2 := a2)...
      inversion ABS.
      all:eauto.
     ** inversion TYP4; subst.
        assert (flagOf g3 (b1, b2) vis /\ flagOf g4  (b1, b2) vis).
      eapply fsuper_vis...
      destruct H3 as [_ FY]; inversion FY; subst.
       assert (f = vis /\  tt4 =  t).
      eapply in_isMap...
      intuition. subst...
     ** eauto.
     ** discriminate.
     ** destruct G5 as (_ &EQ). subst g5. intros.
        erewrite split_domain_r with (g2 := g4) (g := g1);
          try eassumption.
        intros; erewrite <-in_removeEntry_cons_iff_2;
          try tauto...
     ** eapply typeCheck_no_dup with (pf := pf4)...
     ** (*  incl (secLabs q1) (domain (hid_proj g4)) *)
       eapply typeCheck_hid_proj...
     ** eauto.
     ** eauto.
     ** eauto.
     ** eapply tsuper_payload with (pf1 := pf3) in H15 as IN4'.
       destruct IN4' as [pp4 TYP4']; inversion TYP4'; subst.
      
      assert (EX: exists (m : mode) (t : piType),
                 typeOf g3 (a1, a2) (Chan m out t) \/ typeOf g3 (a1, a2) (Chan m io t)). eapply typeCheck_lts_out...
      
       eapply tsuper_payload with (pf1 := pf3) in H15 as IN4''.
       destruct IN4'' as [pp3 TYP3']; inversion TYP3'; subst.
       destruct EX as [mm' [tt' [TYP1'' | TYP1'']]].
      inversion TYP1''; subst.
      assert (f0 = f1 /\  Chan lin pp3 t0 =  Chan mm' out tt').
      eapply in_isMap...
      intuition; inversion H10; subst.
       assert (flagOf g3 (a1, a2) vis /\ flagOf g4  (a1, a2) vis).
      eapply fsuper_vis...
      destruct H8 as [FY _]; inversion FY; subst.
       assert (f1 = vis /\  Chan lin out tt' =  t).
      eapply in_isMap...
      intuition. subst...
      inversion TYP1''; subst.
       assert (f0 = f1 /\  Chan lin pp3 t0 =  Chan mm' io tt').
       eapply in_isMap...
       intuition; inversion H10; subst.
        assert (EX: exists (m : mode) (t : piType),
                   typeOf g4 (a1, a2) (Chan m inp t) \/ typeOf g4 (a1, a2) (Chan m io t)). eapply typeCheck_lts_in...
        destruct EX as [mm [tt [TYP1' | TYP1']]].
        inversion TYP1'; subst.
         eapply tsuper_payload_r with (pf2 := pf4) in H15 as IN4'.
       destruct IN4' as [pp4' TYP4'']; inversion TYP4''; subst.
      assert (f0 = f2 /\  Chan mm inp tt =  Chan lin pp4' tt').
      eapply in_isMap...
      destruct H11; inversion H12; subst.
      assert (ABS: pol_plus io inp io).
      eapply split_plus_lin with (pf1 := pf3) (pf2 := pf4) (pf3 := pf1) (b1 := a1) (b2 := a2)...
      inversion ABS.
      eauto.
      inversion TYP1'; subst.
      eapply tsub_io_r with (pf := pf1) in H8 as K8.
      inversion K8; subst.
      assert (vis = f2 /\ Chan lin io tt' = Chan mm io tt).
      eapply in_isMap...
      intuition. inversion H14; subst.
      assert (ABS: pol_plus io io io).
      eapply split_plus_lin with (pf1 := pf3) (pf2 := pf4) (pf3 := pf1) (b1 := a1) (b2 := a2)...
      inversion ABS.
      all:eauto.
     ** eauto.
     **  destruct G5 as (_ &EQ). subst g5. intros.
        erewrite split_domain_r with (g2 := g3) (g := g1);
          try eassumption.
        intros; erewrite <-in_removeEntry_cons_iff_2;
          try tauto...
        eapply split_comm...
    ** eapply typeCheck_no_dup with (pf := pf3)...
     ** (*  incl (secLabs q1) (domain (hid_proj g4)) *)
       eapply typeCheck_hid_proj...
      + eapply tsuper_payload with (pf1 := pf1) in H0 as IN1'.
       destruct IN1' as [pp1 TYP1']; inversion TYP1'; subst.
      
      assert (vis = f /\  Chan un io t0 =  Chan lin pp1 t).
      eapply in_isMap with (g := g1)...
      intuition; inversion H8; subst.
      eauto.

      
    - Case lclsL.
      intros.
      remember pf0 as nd_pf. remember pf1 as nd_pf_Out.
      remember pf2 as nd_pf_Inp. subst pf0 pf1 pf2.
      remember pf4 as pf1.  remember pf3 as pf2. 
      subst pf4 pf3.

      
                        
      inversion TYP. inversion AFT; subst.
      remember g3 as gk3. remember g4 as gtmp. subst g3 g4.
      remember gtmp as g3. remember g5 as g4. subst g5 gtmp.
      
      assert (nd_pf2 : NoDup (domain g2)).
      eapply no_dup_split_no_dup_r with (pf2 := pf2) (pf := pf)...
       assert (nd_pf3 : NoDup (domain g3)).
      eapply no_dup_split_no_dup_l with (pf1 := pf0) (pf := pf1)...
      assert (nd_pf4 : NoDup (domain g4)).
      eapply no_dup_split_no_dup_r with (pf2 := pf3) (pf := pf1)...
      assert (DIFF: (a1, a2) <> (b1, b2)).
      eapply nonRecActions2 in H20...

      

      +  assert (EQT: t = t0).
     
      eapply tsub_payload with (pf := pf) in H18 as EX.
      destruct EX as [p3 TYP2].
      inversion TYP2; subst.
      assert (vis = f /\ Chan lin io t = Chan lin p3 t0).
      eapply in_isMap... intuition. inversion H8...
      eauto.
      remember pf3 as pf4. subst pf3.
      remember pf0 as pf3. subst pf0.
      assert (IN1 := H18).

      assert (G9: exists (f :flag),  g9 = removeEntry (a1, a2) (removeEntry (b1, b2) g1)).
      exists ill...

      assert (EX: exists t, In (b1, b2, hid, t) g3).
      assert (FLG: flagOf g3 (b1, b2) vis \/ flagOf g3 (b1, b2) hid). eapply typeCheck_lts_out_payload...
      destruct FLG as [FLG1 | FLG2].
      inversion FLG1; subst.
      eapply fsuper_hid with (pf1 := pf3) in H19 as [ [K _] | [K _]].
      inversion K; subst. exists t...
      inversion K; subst. assert (vis = ill). eapply flag_of_map with (g := g3)... discriminate. eauto.
      inversion FLG2; subst.  exists t1...
      destruct EX as [tt3 IN3].
      
      assert (IN1b := H19); move IN1b at bottom.
      assert (TR: exists tt4 : piType, typeOf g4 (b1, b2) tt4 /\ type_remove s0 tt3 tt4).
      destruct s0. destruct m.
      assert (TR2: exists tt4 : piType, typeOf g4 (b1, b2) tt4 /\ type_plus tt3 tt4 (Chan lin p s0)).
      eapply split_type_plus with (g := g1)...
      destruct TR2 as [tt4 [TYP4 TP]]. exists tt4. unfold type_remove, is_unrestricted; intuition auto.
      destruct tt3, tt4; inversion TP...
      destruct H2 as [pp ABS]; inversion ABS.
      inversion H2.
      eapply tsuper_payload_r with (pf1 := pf3) (pf2 := pf4) in IN1b as TSUP.
      destruct TSUP as [p4 TSUP].
      eapply tsuper_payload with (pf1 := pf3) (pf2 := pf4) in IN1b as TSUP1. destruct TSUP1 as [p3 TSUP1].
      inversion TSUP1; subst.
      inversion TSUP; subst.
      assert (POLEQ: p3 = p4 /\ p4 = p).
      eapply split_plus_un with (pf1 := pf3) (pf2 := pf4) (pf3 := pf1) (b1 := b1) (b2 := b2)...
      intuition; subst.
      assert (tt3 = Chan un p s0).
      eapply type_of_map with (g := g3)...
      exists tt3; subst; split... unfold type_remove; split;
      econstructor. rewrite <-pol_cup_id at 3...
      intuition. eauto. eauto.
       exists Top; intuition.
      eapply tsuper_top_r...
      assert (typeOf g3 (b1, b2) Top).
      eapply tsuper_top...
      inversion H2; subst.
      assert (hid = f /\ tt3 = Top).
      eapply in_isMap... intuition; subst tt3 f.

      
      destruct TR as [tt4 [TYP4 TREM]]. inversion TREM as [TSUB [TP ISUN]].
      (*destruct TP as [tt4 [TYP4 TP]].*)

       assert (EXSP: exists s02, typeOf g2 (b1, b2) s02 /\ type_plus s0 s02 s).
      eapply split_type_plus...
      destruct EXSP as [s02 [TYP2 TP2]].
      
      
      assert (LTRO: exists s01, type_remove tt3 t0 s01).
       eapply tsuper_payload with (pf1 := pf3) in H18 as K1.
      eapply fsuper_vis with (pf1 := pf3) in H18 as [K2 _].
      destruct K1 as [p TYP3a]. inversion K2.
      subst. assert (t1 = Chan lin p t0). eapply type_of_map...
      eapply typeCheck_lts_out_type_remove with (a1 := a1) (a2 := a2) (b1 := b1) (b2 := b2)  (p := p1).
      eauto.
      subst...
      eauto. eauto. eauto. eauto. 
      destruct LTRO as [s03 TREM3].
      
      eapply no_dup_isMap in nd_pf_Out as pf_Out.
      specialize IHLTS1 with
          (pf := pf_Out) (g1  := g3) (pf1 := pf3).

      assert (RW: removeEntry (a1, a2)
                          (removeEntry (b1, b2)
                                       ((a1, a2, vis, Chan lin out t0) :: (b1, b2, hid, s0) :: g9)) = g9).
      rewrite removeEntry_swap; unfold removeEntry; fold removeEntry. erewrite pairEq_eq_true;unfold removeEntry; fold removeEntry. erewrite pairEq_eq_true...
      eauto.
      
      move H20 at bottom.   
      rewrite <-RW in H20 at 2. clear RW.
      
      eapply lts_type_remove_lin_out with (pf1 := nd_pf3)  (s0 := tt3) (s01 := s03) (g0 := ((a1, a2, vis, Chan lin out t0) :: (b1, b2, hid, s0) :: g9))in H20 as LTSOUT.

     
      
      
      move IHLTS1 at bottom.

      assert (nd_pfk3: NoDup (domain (((a1, a2, vis, Chan lin empty t0)
                                         :: (b1, b2, vis, s03) :: removeEntry (a1, a2) (removeEntry (b1, b2) g3))))).
      eapply no_dup_cons_removeEntry_app...
      apply no_dup_isMap in nd_pfk3 as pfk3.
      
      specialize IHLTS1 with
          (pfk1 := pfk3)  (nd_pf1 := nd_pf3). 
      assert (SL: sl_pos p1).
      eapply sl_pos_par_l...

      assert (TSO : exists k2 pfk2, tEnv_split g3 k2 ((a1, a2, vis, Chan lin out t) :: (b1, b2, hid, s) :: g0) pf3 pfk2 pf_Out).
      
      assert (nd_pf' :
                NoDup
                  (domain
                     ((a1, a2, vis, Chan lin out t0)
                        :: (b1, b2, hid, s0)
                        :: removeEntry (a1, a2)
                        (removeEntry (b1, b2) g1)))).
      eapply no_dup_cons_removeEntry_app...
      eapply no_dup_isMap in nd_pf' as pf'.
      assert (nd_pf'' :
                NoDup
                  (domain
                     ((a1, a2, vis, Chan lin empty t0)
                        :: (b1, b2, ill, s02)
                        :: removeEntry (a1, a2)
                        (removeEntry (b1, b2) g2)))).
      eapply no_dup_cons_removeEntry_app...
      eapply no_dup_isMap in nd_pf'' as pf''.
      assert (nd_pf''' :
                NoDup
                  (domain
                     ((a1, a2, vis, Chan lin empty t0)
                        :: (b1, b2, ill, tt4)
                        :: removeEntry (a1, a2)
                        (removeEntry (b1, b2) g4)))).
       eapply no_dup_cons_removeEntry_app...
       eapply no_dup_isMap in nd_pf''' as pf'''.

      eapply split_of_split with
          (pf1 := pf') (pf2 := pf'') (pfw0 := pf'''). (*(pf := pf0) .*)
      eauto.

      (*tEnv_split g3
    ((a1, a2, vis, Chan lin empty t0)
     :: (b1, b2, ill, tt4) :: removeEntry (a1, a2) (removeEntry (b1, b2) g4))
    ((a1, a2, vis, Chan lin out t0)
     :: (b1, b2, hid, s0) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) pf3 pf'''
    pf'*)
      eapply type_of_out_action in LTSOUT as K; destruct K as [tt [IN3a | ABS]].
      eapply lts_vis_subject with (a1 :=a1) (a2 := a2) in LTSOUT as FVIS.
      inversion IN3a; inversion FVIS; subst.
      assert (EQ: f = vis /\ Chan lin out tt = t2).
      eapply in_isMap... destruct EQ; subst.

      destruct tt4. destruct m.
      
     inversion TREM; destruct H7; inversion H7; subst.
     eapply split_new_lin_lin.
     eauto. eauto.
     assert (tt = t0).
     eapply tsuper_payload with (pf1 := pf3) in H18 as [pp1 IN3'].
     inversion IN3'. subst.
     assert (Chan lin out tt = Chan lin pp1 t0).
     eapply type_of_map with (g := g3)...
     inversion H11... eauto. subst.
     eauto. eauto. eauto. eauto. eauto. eauto. eauto.
     
     inversion TREM; destruct H7; inversion H7; subst.
     assert (ISUN1: is_unrestricted (Chan un (pol_cup p0 p) tt4)).
     eapply un_is_unrestricted.
     eapply H8 in ISUN1; inversion ISUN1.
     revert dependent pf'; rewrite <-H11; intros.
     eapply split_new_lin_un.
     eauto. eauto.
     assert (tt = t0). 
     eapply tsuper_payload with (pf1 := pf3) in H18 as [pp1 IN3'].
     inversion IN3'. subst.
     assert (Chan lin out tt = Chan lin pp1 t0).
     eapply type_of_map with (g := g3)...
     inversion H12... eauto. subst...
     eauto. eauto.
     assert (p0 = p /\ p = (pol_cup p0 p)).
      inversion TYP4. subst.
     eapply split_plus_un with (pf1 := pf3) (pf2 := pf4) (pf3 := pf1).
     eauto.  eauto. eauto. eauto.
     destruct H10; subst...
     eauto. eauto.

     inversion TREM; destruct H7; inversion H7; subst.
     assert (tt = t0). 
     eapply tsuper_payload with (pf1 := pf3) in H18 as [pp1 IN3'].
     inversion IN3'. subst.
     assert (Chan lin out tt = Chan lin pp1 t0).
     eapply type_of_map with (g := g3)...
     inversion H11... eauto. subst.
     eapply split_new_lin_top.
     eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
     eauto.
     destruct ABS as [ABS | ABS].
     inversion ABS; subst.
      eapply tsuper_payload with (pf1 := pf3) in H18 as [pp1 IN3'].
      assert (Chan un out tt = Chan lin pp1 t0).
      eapply type_of_map with (g := g3)...
      inversion H3... eauto.
            eapply tsuper_payload with (pf1 := pf3) in H18 as [pp1 IN3'].
      assert (Chan un io tt = Chan lin pp1 t0).
      eapply type_of_map with (g := g3)...
      inversion H2... eauto.

      subst t0.
        assert (not_lin_is_unrestricted:  forall p t,
                is_unrestricted (Chan lin p t) -> False).
     unfold is_unrestricted; intros. destruct H2 as [pp [tt ABS]]; inversion ABS...
      revert dependent pf'. 
      rewrite removeEntry_shift. intros.
      revert dependent pf''. rewrite removeEntry_shift; intros.
      subst g0. revert dependent pf_Out.  rewrite removeEntry_shift.
      intros.
      eapply tEnv_split_add_vis.
      eauto. eauto. intros ABS.  eapply not_lin_is_unrestricted in ABS; intuition.  
      (*tEnv_split ((b1, b2, hid, s0) :: removeEntry (b1, b2) g1)
    ((b1, b2, ill, s02) :: removeEntry (b1, b2) g2)
    ((b1, b2, hid, s) :: removeEntry (b1, b2) g) ?pf131 ?pf214 
    ?pf19*)
      inversion TYP2. subst.
      assert (f = ill).
      eapply fsuper_hid with (pf1 := pf1) (pf2 := pf2) in H1 as [[_ FYP2] | [FYP1 _]].
      inversion FYP2; subst. assert (f = ill). eapply flag_of_map with (g := g2)... subst...
      inversion FYP1; subst. assert (hid = ill). eapply flag_of_map with (g := g1)... discriminate. eauto.
      subst.
      eapply split_cons_remove_3...
      eauto. eauto. eauto.
      
     
      destruct TSO as [k2 [pfk2 TSK]].
      specialize IHLTS1 with (pf2 := pfk2).
      intuition.
      assert (TC1 := H3); clear H3.


      (* s1 = s - t*)
      (* s0 = tt3 + tt4 *)
      (* s2 = s0 - t *)
      (* s03 = tt3 - t *)
      (* s = s0 + s02 *)

      (* s1 = tt4 + ??? *)
      (* s1 = s - t = (s0 + s02) - t = ((tt3 + tt4) + s02) -t *)          
     


      assert (LTRI: exists s04, type_plus tt4 t0 s04 /\
             (is_unrestricted s0 -> s03 = s04 /\ s04 = s0)).
      destruct t0. destruct m.
      assert (LT: exists s04, type_plus tt4 (Chan lin p t0) s04).
      inversion TREM3.
     
      eapply plus_sub_exists. eapply type_plus_comm...
      eauto.
      destruct LT as [s04 TP4'].
      exists s04. split. tauto.
      intros ABS. inversion H17; destruct H3; inversion H3; subst; eapply not_lin_is_unrestricted in ABS. contradiction.
      (* m = un*)
      inversion H17. destruct H3 as [TPP ISUNN].
      inversion TREM3. destruct H7 as [TPP2 ISUNN2]. 
      assert (s03 = tt3 /\ s2 = s0 /\ tt4 = s0).
      assert (is_unrestricted tt3).
      inversion TPP2; subst; eapply un_is_unrestricted.
      assert (is_unrestricted s0).
      inversion TPP; subst; eapply un_is_unrestricted.
      intuition. intuition; subst.
      move TP at bottom.
      assert (s0 = tt3).
      destruct s0.
      assert (m = un). inversion TPP2; inversion TP. subst. inversion H12. tauto.
      subst m. 
       eapply tsuper_payload with (pf1 := pf3) in IN1 as IN3'.
      eapply tsuper_payload with (pf1 := pf4) in IN1 as IN4'.
      destruct IN3' as [pp3 TYP3'];
        destruct IN4' as [pp4 TYP4'];
        inversion TYP3'; inversion TYP4'; clear TYP3'; clear TYP4'; subst. inversion TP; subst. 
      assert (p3 = p0 /\ p0 = p0).
      inversion TYP4; subst.
      eapply split_plus_un with (pf1 := pf3) (pf2 := pf4) (pf3 := pf1) (b1 := b1) (b2 := b2)...
      intuition; subst.
      rewrite H13...
      eapply split_comm...
      eauto.
      inversion TPP...
      subst tt3. exists s0...
      split.
      eapply type_plus_comm...
      assert (is_unrestricted s0).
      inversion TPP2; subst; eapply un_is_unrestricted.
      intuition.
      inversion H17. destruct H3; inversion H3; subst.
      inversion TREM. destruct H9. inversion H9; subst.
      exists Top... 
      
      
      destruct LTRI as [s04 [TP4 ISUN4]].
      
      move H21 at bottom.
        assert (RW: removeEntry (a1, a2)
                          (removeEntry (b1, b2)
                                       ((a1, a2, vis, Chan lin inp t0) :: (b1, b2, ill, s2) :: g9)) = g9).
        rewrite <- removeEntry_shift; unfold removeEntry; fold removeEntry.
        rewrite pairEq_eq_true, pairEq_eq_true...
        eauto.
        rewrite <-RW in H21 at 2.
       eapply lts_type_plus_lin_in with (pf1 := nd_pf4) (s01 := tt4) (s0 := s04) in H21 as LTSIN.
       
     
      
      move IHLTS2 at bottom.
      eapply no_dup_isMap in nd_pf_Inp as pf_Inp.
      specialize IHLTS2 with
          (pf := pf_Inp)  (pf1 := pf4) (nd_pf1 := nd_pf4). 
      assert (SL2: sl_pos q1).
      eapply sl_pos_par_r...

     
      assert (EXSP2: exists s0t,
                type_remove s0 t s0t).
     eapply typeCheck_lts_out_type_remove with (pf := pf1).
     eauto.
     subst...
     eauto. econstructor...
     destruct EXSP2 as [s0t TREM2].
     
     
      assert (EXSP2: exists r4,
                type_plus tt4 r4 s1 /\ type_sub tt4 s1 /\
            (is_unrestricted s1 -> r4 = s1)).
     **  inversion H. destruct H3 as [TPP ISUNN].  inversion TREM2; subst. destruct H7 as [TPP2 ISUNN2].
        move TP at bottom. move TP2 at bottom.  move TP4 at bottom. clear  LTSIN .
        
        apply T_Entry in H19 as TYP1. move TYP1 at bottom.
        apply T_Entry in IN3 as TYP3. move TYP3 at bottom.
        move TYP4 at bottom.
        assert (PAYLOAD : t0 = t0)...

        
        destruct t0. destruct m.
        destruct p.
        *** inversion TP4. inversion H11; subst...
            inversion TPP. inversion H12; subst...
            inversion TP; inversion TP2; subst...
            all: try discriminate.
            inversion H14; subst. clear H14.
            **** assert (EXR: exists r, pol_plus p0 p6 r).
                 destruct p0; eauto; inversion H12; inversion H13; subst; try discriminate...
            destruct EXR as [r PPR].
            exists (Chan lin r t0).
            inversion TPP; subst.
            assert (ASSOC: pol_plus p r p5).
            (*assert (LEM1 : forall p1 p2, pol_plus p1 empty p2 -> p1 = p2). intros; destruct p3, p8; inversion H7...
            assert (LEM2 : forall p1 p2, pol_plus empty p1 p2 -> p1 = p2). intros. destruct p3, p8; inversion H7; inversion H10...*)
            destruct p; inversion H10; inversion H12; inversion PPR;  subst; try discriminate; eapply pol_plus_comm; inversion H13; eauto.
            split. econstructor...
            split.  eapply pol_plus_type_sub...
            intros ABS; eapply not_lin_is_unrestricted in ABS; intuition.
            
        *** inversion TP4; inversion H11; subst...
            inversion TPP; inversion H12; subst...
            inversion TP; inversion TP2; subst;try discriminate...
            inversion H14; subst. clear H14.
            inversion TPP; inversion H12; inversion H10; inversion H13; subst; try discriminate.
            exists (Chan lin empty t0).
            split. econstructor...
            split.   econstructor...
            intros ABS; eapply not_lin_is_unrestricted in ABS; intuition.
            exists (Chan lin empty t0).
            split. econstructor...
            split.   econstructor...
             intros ABS; eapply not_lin_is_unrestricted in ABS; intuition.
        (*    exists (Chan lin out t0)...
            inversion TPP; inversion TP2; inversion H12; subst; try discriminate; inversion H16; subst.
            assert (p4 = inp). inversion TPP2; inversion H10; inversion TP2; subst; inversion H13... inversion H13; subst.
            discriminate.
            inversion TP; inversion H9...
            exists (Chan lin empty t0).
            split. econstructor...
            split. eapply Ts_id.
            intros ABS; eapply not_lin_is_unrestricted in ABS; intuition. *)
       *** inversion TP4; inversion H11; subst...
            inversion TPP; inversion H12; subst...
            inversion TP; inversion TP2; subst;try discriminate...
            inversion H14; subst. clear H14.
            inversion TPP; inversion H12; inversion H10; inversion H13; subst; try discriminate.
            exists (Chan lin empty t0).
            split. econstructor...
            split.   econstructor...
            intros ABS; eapply not_lin_is_unrestricted in ABS; intuition.
            exists (Chan lin empty t0).
            split. econstructor...
            split.   econstructor...
             intros ABS; eapply not_lin_is_unrestricted in ABS; intuition.
            
           (* inversion H15; subst. clear H15.
            exists (Chan lin empty t0)...
            exists (Chan lin inp t0)...
            inversion TPP; inversion TP2; inversion H12; subst; try discriminate; inversion H16; subst.
            assert (p4 = out). inversion TPP2; inversion H10; inversion TP2; subst; inversion H13... inversion H13; subst.
            discriminate.
            inversion TP; inversion H9...
            exists (Chan lin empty t0).
            split. econstructor...
            split. eapply Ts_id.
            intros ABS; eapply not_lin_is_unrestricted in ABS; intuition. *)
       *** inversion TP4; inversion H11; subst...
            inversion TPP; inversion H12; subst...
            (*inversion TP; inversion TP2; subst...
            inversion H15; subst. clear H15.
            exists (Chan lin empty t0)...*)
        *** inversion TP4; inversion TP; inversion TP2; subst...
            all:try discriminate.
            inversion TPP; subst.
            inversion H14; inversion H12; subst.
            assert (is_unrestricted (Chan un (pol_cup (pol_cup p4 p0) p7) t1)). eapply un_is_unrestricted...
            intuition. inversion H9.
            rewrite <-H15.
            assert (p4 = p0 /\ p0 = (pol_cup p4 p0)).
            inversion TYP1; inversion TYP4.
            eapply split_plus_un with (pf1 := pf3) (pf2 := pf4) (pf3 := pf1) (b1 := b1) (b2 := b2)...
            destruct H10; subst p4.
            assert ((pol_cup p0 p0) = p7 /\ p7 =  (pol_cup (pol_cup p0 p0) p7)).
            inversion TYP1; inversion TYP2.
             eapply split_plus_un with (pf1 := pf1) (pf2 := pf2) (pf3 := pf) (b1 := b1) (b2 := b2)...
             destruct H10. subst p7.
           rewrite <-H16, <-H16 in H15. subst.
           exists (Chan un p0 t1).
           split. rewrite H16 at 3. econstructor...
           split. eapply pol_cup_type_sub...
           intros _...
        *** inversion TP4; inversion TPP; subst...
     ** destruct EXSP2 as [r4 [TP4' [TSUB4' ISUN4']]].

       assert (nd_pf1' :
                NoDup
                  (domain
                     ((a1, a2, vis, Chan lin inp t0)
                        :: (b1, b2, ill, tt4)
                        :: removeEntry (a1, a2)
                        (removeEntry (b1, b2) g1)))).
      eapply no_dup_cons_removeEntry_app...
        eapply no_dup_isMap in nd_pf1' as pf1'.
       assert (nd_pf'' :
                NoDup
                  (domain
                     ((a1, a2, vis, Chan lin empty t0)
                        :: (b1, b2, ill, r4)
                        :: removeEntry (a1, a2)
                        (removeEntry (b1, b2) g2)))).
       eapply no_dup_cons_removeEntry_app...
      eapply no_dup_isMap in nd_pf'' as pf''.
     
     
      move IHLTS2 at bottom.
     assert (TSO : exists k'' pfk'', tEnv_split g4 k'' ((a1, a2, vis, Chan lin inp t) :: (b1, b2, ill, s1) :: g0) pf4 pfk'' pf_Inp).
     inversion TYP4. subst. assert (IN4 := H2); clear H2 TYP4.
     eapply typeCheck_lts_in with (g1 := g4) in LTSIN as IN4a.
     destruct IN4a as [mm [tt [TYP4a | ABS]]].
     inversion TYP4a. subst. assert (IN4a := H2); clear H2 TYP4a.
     assert (EQ: f0 = vis /\ mm = lin /\ tt = t0).
     eapply tsuper_payload with (pf1 := pf4) in H18 as K.
     destruct K as [pp1 TYP4]; inversion TYP4; subst.
     eapply fsuper_vis with (pf1 := pf4) in H18 as [K _].
     inversion K; subst.
     assert (f0 = vis). eapply flag_of_map with (g := g4)...
     assert (EQ: Chan mm inp tt =  Chan lin pp1 t0). eapply type_of_map with (g := g4)...
     inversion EQ;  intuition.
     eapply split_comm... eapply split_comm...
     destruct EQ as [EQ1 [EQ2 EQ3]]; subst.
     
     destruct tt4. destruct m. 
      assert (nd_pf''' :
                NoDup
                  (domain
                     ((a1, a2, vis, Chan lin empty t0)
                        :: (b1, b2, ill, Chan lin empty tt4)
                        :: removeEntry (a1, a2)
                        (removeEntry (b1, b2) g3)))).
      eapply no_dup_cons_removeEntry_app...
      eapply no_dup_isMap in nd_pf''' as pf'''.
      eapply split_of_split with (pf1 := pf1') (pf2 := pf'') (pfw0 := pf''').
      eauto.
      (*tEnv_split g4
    ((a1, a2, vis, Chan lin empty t0)
     :: (b1, b2, ill, Chan lin empty tt4)
        :: removeEntry (a1, a2) (removeEntry (b1, b2) g3))
    ((a1, a2, vis, Chan lin inp t0)
     :: (b1, b2, ill, Chan lin p tt4) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1))
    pf4 pf''' pf1'*)
      eapply split_new_lin_lin.
      eauto. eapply split_comm...
      eauto. eauto. eauto. eauto.
      assert (flagOf g4 (b1, b2) ill).
      eapply finv_hid_r with (pf2 := pf3), split_comm...
      assert (f = ill).
      eapply flag_of_map with (g := g4)...
      subst...
      eauto. eauto.
      
      
      assert (EQ1: ((a1, a2, vis, Chan lin inp t0)
                 :: (b1, b2, ill, Chan lin p tt4) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) =
              ((a1, a2, vis, Chan lin inp t0)
                 :: removeEntry (a1, a2) ((b1, b2, ill, Chan lin p tt4) :: removeEntry (b1, b2) g1))).
      erewrite removeEntry_shift...
       assert (EQ2: ((a1, a2, vis, Chan lin empty t0)
                 :: (b1, b2, ill, r4) :: removeEntry (a1, a2) (removeEntry (b1, b2) g2)) =
              ((a1, a2, vis, Chan lin empty t0)
                 :: removeEntry (a1, a2) ((b1, b2, ill, r4) :: removeEntry (b1, b2) g2))).
       erewrite removeEntry_shift...
       subst g0.
        assert (EQ3: ((a1, a2, vis, Chan lin inp t0)
                 :: (b1, b2, ill, s1) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)) =
              ((a1, a2, vis, Chan lin inp t0)
                 :: removeEntry (a1, a2) ((b1, b2, ill, s1) :: removeEntry (b1, b2) g))).
              erewrite removeEntry_shift...
      revert dependent pf1'; revert dependent pf''; revert dependent pf_Inp.
      erewrite EQ1,EQ2,EQ3. clear EQ1 EQ2 EQ3.
      intros.

      eapply tEnv_split_add_vis.
      eapply no_dup_cons_removeEntry...
      econstructor...
      intros ABS; unfold is_unrestricted in ABS; destruct ABS as [ttt [yyy ABS]]; inversion ABS.
      
      eapply tEnv_split_add_fp.
      eauto. eauto. eauto. 
      (* is_unrestricted s1 -> tt4 = r4 /\ r4 = s1 *)
      intros ABS; inversion TP4'; subst.
      eapply not_lin_is_unrestricted in ABS; intuition.
      eauto.

      assert (EQ: s1 = s /\ s = Chan un p tt4).
      inversion H; destruct H3.
      eapply tsub_un with (pf := pf1) in IN4 as K1. inversion K1; subst.
       eapply tsub_un with (pf := pf) in  H8 as K2. inversion K2; subst.
       assert (s = Chan un p tt4).
       eapply type_of_map with (g := g)...
       assert (s1 = Chan un p tt4).
       subst; assert (is_unrestricted (Chan un p tt4)). eapply un_is_unrestricted. intuition.
       subst... eauto. eapply split_comm...
       destruct EQ; subst.
       assert (r4 = Chan un p tt4).
       eapply ISUN4', un_is_unrestricted...
       subst.
      assert (nd_pf''' :
                NoDup
                  (domain
                     ((a1, a2, vis, Chan lin empty t0)
                        :: (b1, b2, ill, Chan un p tt4)
                        :: removeEntry (a1, a2)
                        (removeEntry (b1, b2) g3)))).
      eapply no_dup_cons_removeEntry_app...
      eapply no_dup_isMap in nd_pf''' as pf'''.
      eapply split_of_split with (pf1 := pf1') (pf2 := pf'') (pfw0 := pf''').
      eauto.
      (*tEnv_split g4
    ((a1, a2, vis, Chan lin empty t0)
     :: (b1, b2, ill, Chan un p tt4) :: removeEntry (a1, a2) (removeEntry (b1, b2) g3))
    ((a1, a2, vis, Chan lin inp t0)
     :: (b1, b2, ill, Chan un p tt4) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) pf4
    pf''' pf1'*)
      eapply split_new_lin_un.
      eauto. eapply split_comm...
      eauto. eauto. eauto. eauto. 
      assert (flagOf g4 (b1, b2) ill).
       eapply finv_hid_r with (pf2 := pf3), split_comm...
      assert (f = ill).
      eapply flag_of_map with (g := g4)...
      subst...
      eauto. 
      
      
      assert (EQ1: ((a1, a2, vis, Chan lin inp t0)
                 :: (b1, b2, ill, Chan un p tt4) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) =
              ((a1, a2, vis, Chan lin inp t0)
                 :: removeEntry (a1, a2) ((b1, b2, ill, Chan un p tt4) :: removeEntry (b1, b2) g1))).
      erewrite removeEntry_shift...
       assert (EQ2: ((a1, a2, vis, Chan lin empty t0)
                 :: (b1, b2, ill, Chan un p tt4) :: removeEntry (a1, a2) (removeEntry (b1, b2) g2)) =
              ((a1, a2, vis, Chan lin empty t0)
                 :: removeEntry (a1, a2) ((b1, b2, ill, Chan un p tt4) :: removeEntry (b1, b2) g2))).
       erewrite removeEntry_shift...
       subst g0.
        assert (EQ3: ((a1, a2, vis, Chan lin inp t0)
                 :: (b1, b2, ill, Chan un p tt4) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)) =
              ((a1, a2, vis, Chan lin inp t0)
                 :: removeEntry (a1, a2) ((b1, b2, ill, Chan un p tt4) :: removeEntry (b1, b2) g))).
              erewrite removeEntry_shift...
      revert dependent pf1'; revert dependent pf''; revert dependent pf_Inp.
      erewrite EQ1,EQ2,EQ3. clear EQ1 EQ2 EQ3.
      intros.

      eapply tEnv_split_add_vis.
      eapply no_dup_cons_removeEntry...
      econstructor...
      intros ABS; eapply not_lin_is_unrestricted in ABS; intuition.
     
      eapply tEnv_split_add_fp.
      eauto.
      eauto.
      eauto.
      (* is_unrestricted s1 -> tt4 = r4 /\ r4 = s1 *)
      intros ISUN1; inversion TP4'; subst...
      eauto.

      assert (EQ: s1 = s /\ s = Top).
      inversion H; destruct H3.
      eapply tsub_top with (pf := pf1) in IN4 as K1. inversion K1; subst.
       eapply tsub_top with (pf := pf) in  H8 as K2. inversion K2; subst.
       assert (s = Top).
       eapply type_of_map with (g := g)...
       inversion H3; subst. split... all:try discriminate.
       eauto.
       eapply split_comm...
(*       eapply split_comm...
       eapply split_comm...
*)       
      assert (nd_pf''' :
                NoDup
                  (domain
                     ((a1, a2, vis, Chan lin empty t0)
                        :: (b1, b2, ill, Top)
                        :: removeEntry (a1, a2)
                        (removeEntry (b1, b2) g3)))).
      eapply no_dup_cons_removeEntry_app...
      eapply no_dup_isMap in nd_pf''' as pf'''.
      eapply split_of_split with (pf1 := pf1') (pf2 := pf'') (pfw0 := pf''').
      eauto.
      (*tEnv_split g4
    ((a1, a2, vis, Chan lin empty t0)
     :: (b1, b2, vis, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g3))
    ((a1, a2, vis, Chan lin inp t0)
     :: (b1, b2, vis, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) pf4
    pf''' pf1'*)
      eapply split_new_lin_top.
      eauto. eapply split_comm...
      eauto. eauto. eauto. eauto. 
      assert (flagOf g4 (b1, b2) ill).
       eapply finv_hid_r with (pf2 := pf3), split_comm...
      assert (f = ill).
      eapply flag_of_map with (g := g4)...
      subst...
      eauto. 
      destruct EQ; inversion TP4'; subst. 
      
      assert (EQ1: ((a1, a2, vis, Chan lin inp t0)
                 :: (b1, b2, ill, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) =
              ((a1, a2, vis, Chan lin inp t0)
                 :: removeEntry (a1, a2) ((b1, b2, ill, Top) :: removeEntry (b1, b2) g1))).
      erewrite removeEntry_shift...
       assert (EQ2: ((a1, a2, vis, Chan lin empty t0)
                 :: (b1, b2, ill, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g2)) =
              ((a1, a2, vis, Chan lin empty t0)
                 :: removeEntry (a1, a2) ((b1, b2, ill, Top) :: removeEntry (b1, b2) g2))).
       erewrite removeEntry_shift...
       subst g0.
        assert (EQ3: ((a1, a2, vis, Chan lin inp t0)
                 :: (b1, b2, ill, Top) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)) =
              ((a1, a2, vis, Chan lin inp t0)
                 :: removeEntry (a1, a2) ((b1, b2, ill, Top) :: removeEntry (b1, b2) g))).
              erewrite removeEntry_shift...
      revert dependent pf1'; revert dependent pf''; revert dependent pf_Inp.
      erewrite EQ1,EQ2,EQ3. clear EQ1 EQ2 EQ3.
      intros.

       (*tEnv_split
    ((a1, a2, vis, Chan lin inp t0)
     :: removeEntry (a1, a2) ((b1, b2, ill, Top) :: removeEntry (b1, b2) g1))
    ((a1, a2, vis, Chan lin empty t0)
     :: removeEntry (a1, a2) ((b1, b2, ill, Top) :: removeEntry (b1, b2) g2))
    ((a1, a2, vis, Chan lin inp t0)
     :: removeEntry (a1, a2) ((b1, b2, ill, Top) :: removeEntry (b1, b2) g)) pf1' pf''
    pf_Inp*)
       eapply tEnv_split_add_vis.
       eapply no_dup_cons_removeEntry...
      econstructor...
      intros ABS; eapply not_lin_is_unrestricted in ABS; intuition.
     
      eapply tEnv_split_add_fp.
      eauto.
      eauto.
      eauto.
      (* is_unrestricted s1 -> tt4 = r4 /\ r4 = s1 *)
      intros ISUN1; inversion TP4'; subst...
      eauto.

      inversion ABS; subst. 
      eapply type_of_in_action in LTSIN as LIN.
      destruct LIN as [ttt [ABS1 | [ABS1 | ABS1]]].
      assert (EQ: Chan mm io tt = Chan lin inp ttt).
      eapply type_of_map with (g := g4)...
      inversion EQ.
      assert (EQ: Chan mm io tt = Chan un inp ttt).
      eapply type_of_map with (g := g4)...
      inversion EQ.
      assert (EQ: Chan mm io tt = Chan un io ttt).
      eapply type_of_map with (g := g4)...
      inversion EQ. subst.
      eapply tsub_un with (pf := pf1) in H2.
      assert (EQ2: Chan lin io t0 = Chan un io ttt).
       eapply type_of_map with (g := g1)...
       inversion EQ2.
       eapply split_comm... eauto.
      
       destruct TSO as [k'' [pfk'' TSK'']].
       assert (nd_pfk4 :
                 NoDup (domain
                          (((a1, a2, vis, Chan lin empty t0)
                              :: (b1, b2, vis, s04) :: removeEntry (a1, a2) (removeEntry (b1, b2) g4))))).
       eapply no_dup_cons_removeEntry_app...
       eapply no_dup_isMap in nd_pfk4 as pfk4.
      specialize IHLTS2 with (pf2 := pfk'') (pfk1 := pfk4).
       move IHLTS2 at bottom.
       assert (sl_pos q1). eapply sl_pos_par_r...
       intuition.
       move TC1 at bottom.
       assert (TC2 := H7); clear H7.

       remember (b1, b2) as b.
       assert (nd_pfn : NoDup (domain ((b, vis, s0) :: removeEntry b g8))).
       eapply no_dup_cons_removeEntry...
       eapply no_dup_isMap in nd_pfn as pfn.
       assert (EQ1: fst b = b1). subst...
       assert (EQ2: snd b = b2). subst...
       rewrite <-EQ1, <-EQ2.
       eapply TNew with  (pf1 := pfn).
       subst; right...
       subst b g7 g8.
       revert dependent pfn.
       erewrite <-removeEntry_shift.
       unfold removeEntry; fold removeEntry.
       rewrite pairEq_eq_true.
       intros.
       assert (nd_pfkpar: NoDup( domain ((a1, a2, vis, Chan lin empty t0) :: (b1, b2, vis, s0)
     :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)))).
       eapply no_dup_cons_removeEntry_app...
       eapply no_dup_isMap in nd_pfkpar as pf_kpar.
       eapply typeCheck_impl with (pf1 := pf_kpar).
       eauto. erewrite removeEntry_swap.
       eapply no_dup_cons_removeEntry_app...
       eauto.
       clear EQ1 EQ2.
       
       eapply TPar with (pf1 := pfk3) (pf2 := pfk4).
        assert (EQ1: ((a1, a2, vis, Chan lin empty t0)
                 :: (b1, b2, vis, s03) :: removeEntry (a1, a2) (removeEntry (b1, b2) g3)) =
              ((a1, a2, vis, Chan lin empty t0)
                 :: removeEntry (a1, a2) ((b1, b2, vis, s03) :: removeEntry (b1, b2) g3))).
      erewrite removeEntry_shift...
       assert (EQ2: ((a1, a2, vis, Chan lin empty t0)
                 :: (b1, b2, vis, s04) :: removeEntry (a1, a2) (removeEntry (b1, b2) g4)) =
              ((a1, a2, vis, Chan lin empty t0)
                 :: removeEntry (a1, a2) ((b1, b2, vis, s04) :: removeEntry (b1, b2) g4))).
       erewrite removeEntry_shift...
       subst g0.
        assert (EQ3: ((a1, a2, vis, Chan lin empty t0)
                 :: (b1, b2, vis, s0) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) =
              ((a1, a2, vis, Chan lin empty t0)
                 :: removeEntry (a1, a2) ((b1, b2, vis, s0) :: removeEntry (b1, b2) g1))).
        erewrite removeEntry_shift...
      revert dependent pfk3; revert dependent pfk4; revert dependent pf_kpar.
     erewrite EQ1,EQ2,EQ3. clear EQ1 EQ2 EQ3.
      intros.

      eapply tEnv_split_add_vis.
      eapply no_dup_cons_removeEntry...
      econstructor...
      intros ABS; eapply not_lin_is_unrestricted in ABS; intuition.
       eapply tEnv_split_add_vis.
       eauto.
       (* type_plus s03 s04 s0 *)
       move TP4 at bottom.
       inversion TREM as [_ [TP0 _]]; inversion TREM3 as [_ [TP3 _]]. 
       destruct t0. destruct m. destruct p.
       try inversion TP4;  inversion TP3; inversion TP0; inversion H10; inversion H15; subst; try discriminate;
         inversion H22; inversion H23; inversion H16; subst; eauto.
       try inversion TP4;  inversion TP3; inversion TP0; inversion H10; inversion H15; subst; try discriminate;
         inversion H22; inversion H23; inversion H16; subst; eauto; try discriminate.
       try inversion TP4;  inversion TP3; inversion TP0; inversion H10; inversion H15; subst; try discriminate;
         inversion H22; inversion H23; inversion H16; subst; eauto; try discriminate.
       try inversion TP4;  inversion TP3; inversion TP0; inversion H10; inversion H15; subst; try discriminate;
         inversion H22; inversion H23; inversion H16; subst; eauto; try discriminate.
       try inversion TP4;  inversion TP3; inversion TP0; inversion H10; inversion H15; subst; try discriminate;
         inversion H22; inversion H23; inversion H7; inversion H8; subst; eauto; try discriminate.
       inversion TP0; inversion H22; inversion H23; subst.
       assert (EQ :
                 pol_cup p5 (pol_cup p0 p) =
                 (pol_cup (pol_cup p p5) p0)).
       destruct p, p0, p5...
       rewrite <-EQ...
        try inversion TP4;  inversion TP3; inversion TP0; inversion H10; try discriminate; subst;
         inversion TP4; inversion TP0; inversion TP3; subst; eauto; try discriminate.
      (* is_unrestricted s0 -> s03 = s04 /\ s04 = s0 *)
      intuition.
      all:eauto.
(*      eapply cons_cons_iff. *)
      

     ** eauto.
     ** eauto.
     ** assert (EX: exists (m : mode) (t : piType),
                   typeOf g4 (a1, a2) (Chan m inp t) \/ typeOf g4 (a1, a2) (Chan m io t)). eapply typeCheck_lts_in...
        destruct EX as [mm [tt [TYP1' | TYP1']]].
        inversion TYP1'; subst.
         eapply tsuper_payload_r with (pf2 := pf4) in IN1 as IN4'.
       destruct IN4' as [pp4 TYP4']; inversion TYP4'; subst.
      assert (f = f0 /\  Chan mm inp tt =  Chan lin pp4 t0).
      eapply in_isMap...
      destruct H7; inversion H8; subst.
      assert (flagOf g3 (a1, a2) vis /\ flagOf g4  (a1, a2) vis).
      eapply fsuper_vis...
      destruct H7 as [_ FY]; inversion FY; subst.
       assert (f0 = vis /\  Chan lin inp t0 =  t).
      eapply in_isMap...
      intuition. subst...
      eauto.
      inversion TYP1'; subst.
       eapply tsuper_payload_r with (pf2 := pf4) in IN1 as IN4'.
       destruct IN4' as [pp4 TYP4']; inversion TYP4'; subst.
      assert (f = f0 /\  Chan mm io tt =  Chan lin pp4 t0).
      eapply in_isMap...
      destruct H7; inversion H8; subst.
      assert (EX: exists (m : mode) (t : piType),
                 typeOf g3 (a1, a2) (Chan m out t) \/ typeOf g3 (a1, a2) (Chan m io t)). eapply typeCheck_lts_out...
      
       eapply tsuper_payload with (pf1 := pf3) in IN1 as IN4''.
       destruct IN4'' as [pp3 TYP3']; inversion TYP3'; subst.
       destruct EX as [mm' [tt' [TYP1'' | TYP1'']]].
      inversion TYP1''; subst.
      assert (f = f1 /\  Chan lin pp3 t0 =  Chan mm' out tt').
      eapply in_isMap...
      intuition; inversion H12; subst.
      assert (ABS: pol_plus out io io).
      eapply split_plus_lin with (pf1 := pf3) (pf2 := pf4) (pf3 := pf1) (b1 := a1) (b2 := a2)...
      inversion ABS.
      inversion TYP1''; subst.
       assert (f = f1 /\  Chan lin pp3 t0 =  Chan mm' io tt').
      eapply in_isMap...
      intuition; inversion H12; subst.
      assert (ABS: pol_plus io io io).
      eapply split_plus_lin with (pf1 := pf3) (pf2 := pf4) (pf3 := pf1) (b1 := a1) (b2 := a2)...
      inversion ABS.
      all:eauto.
     ** inversion TYP4; subst.
         assert (flagOf g4 (b1, b2) ill).
       eapply finv_hid_r with (pf2 := pf3), split_comm...
      assert (f = ill).
      eapply flag_of_map with (g := g4)...
      subst...
     ** eauto.
     ** discriminate.
     ** destruct G9 as (_ &EQ); subst g9.
        intros; try rewrite split_domain_r with (g2 := g4) (g := g1);
          try tauto; try eassumption.
        intros.
        rewrite <-in_removeEntry_cons_iff_2; try tauto.
        eauto.
        eauto.
     ** eapply typeCheck_no_dup with (pf := pf4)...
     ** (* incl (secLabs q1) (domain (hid_proj g4)) *)
       eapply typeCheck_hid_proj; try eassumption.
     ** eauto.
     **  eauto.
     ** eauto.
     ** eapply tsuper_payload with (pf1 := pf3) in IN1 as IN4'.
       destruct IN4' as [pp4 TYP4']; inversion TYP4'; subst.
      
      assert (EX: exists (m : mode) (t : piType),
                 typeOf g3 (a1, a2) (Chan m out t) \/ typeOf g3 (a1, a2) (Chan m io t)). eapply typeCheck_lts_out...
      
       eapply tsuper_payload with (pf1 := pf3) in IN1 as IN4''.
       destruct IN4'' as [pp3 TYP3']; inversion TYP3'; subst.
       destruct EX as [mm' [tt' [TYP1'' | TYP1'']]].
      inversion TYP1''; subst.
      assert (f0 = f1 /\  Chan lin pp3 t0 =  Chan mm' out tt').
      eapply in_isMap...
      intuition; inversion H10; subst.
       assert (flagOf g3 (a1, a2) vis /\ flagOf g4  (a1, a2) vis).
      eapply fsuper_vis...
      destruct H8 as [FY _]; inversion FY; subst.
       assert (f1 = vis /\  Chan lin out tt' =  t).
      eapply in_isMap...
      intuition. subst...
      inversion TYP1''; subst.
       assert (f0 = f1 /\  Chan lin pp3 t0 =  Chan mm' io tt').
       eapply in_isMap...
       intuition; inversion H10; subst.
        assert (EX: exists (m : mode) (t : piType),
                   typeOf g4 (a1, a2) (Chan m inp t) \/ typeOf g4 (a1, a2) (Chan m io t)). eapply typeCheck_lts_in...
        destruct EX as [mm [tt [TYP1' | TYP1']]].
        inversion TYP1'; subst.
         eapply tsuper_payload_r with (pf2 := pf4) in IN1 as IN4'.
       destruct IN4' as [pp4' TYP4'']; inversion TYP4''; subst.
      assert (f0 = f2 /\  Chan mm inp tt =  Chan lin pp4' tt').
      eapply in_isMap...
      destruct H11; inversion H12; subst.
      assert (ABS: pol_plus io inp io).
      eapply split_plus_lin with (pf1 := pf3) (pf2 := pf4) (pf3 := pf1) (b1 := a1) (b2 := a2)...
      inversion ABS.
      eauto.
      inversion TYP1'; subst.
      eapply tsub_io_r with (pf := pf1) in H8 as K8.
      inversion K8; subst.
      assert (vis = f2 /\ Chan lin io tt' = Chan mm io tt).
      eapply in_isMap...
      intuition. inversion H13; subst.
      assert (ABS: pol_plus io io io).
      eapply split_plus_lin with (pf1 := pf3) (pf2 := pf4) (pf3 := pf1) (b1 := a1) (b2 := a2)...
      inversion ABS.
      all:eauto.
     ** eauto.
     **  destruct G9 as (_ &EQ); subst g9.
        intros; try rewrite split_domain_l with (g1 := g3) (g := g1);
          try tauto; try eassumption.
        intros.
        rewrite <-in_removeEntry_cons_iff_2; try tauto.
        eauto.
        eauto.
     ** eapply typeCheck_no_dup with (pf := pf3)...
     ** (*incl (secLabs p1) (domain (hid_proj g3))*)
       eapply typeCheck_hid_proj; try eassumption.
      + eapply tsuper_payload with (pf1 := pf1) in H0 as IN1'.
       destruct IN1' as [pp1 TYP1']; inversion TYP1'; subst.
      
      assert (vis = f /\  Chan un io t0 =  Chan lin pp1 t).
      eapply in_isMap with (g := g1)...
      intuition; inversion H8; subst.
      eauto.
      
    - Case ucomL .
      intros.
      remember pf0 as nd_pf. remember pf1 as nd_pf_Out.
      remember pf2 as nd_pf_Inp. subst pf0 pf1 pf2.
      remember pf4 as pf1.  remember pf3 as pf2. 
      subst pf4 pf3.
      
                        
      inversion TYP. inversion AFT; subst.

      eapply nonDivergentProcesses in LTS2; intuition.
      eapply tsuper_payload with (pf1 := pf1) in H0 as ABS.
      destruct ABS as [pp TYP1].
      assert (ABS: Chan un pp t = Chan lin io t0).
      eapply type_of_map with (g := g1)...
      inversion ABS... eauto.


      remember g3 as gk3. remember g4 as gtmp. remember pf3 as pftmp. subst g3 g4 pf3. remember pf0 as pf3. subst pf0.
      remember gtmp as g3. remember g5 as g4. subst g5 gtmp. remember pftmp as pf4. 
     eapply lts_rewrite_pf with (pf1 := nd_pf1) in H19 .
     assert (LTSOUT0 := H19).
     assert (nd_pf'0 : NoDup (domain g'0)).
     subst g'0 g7. eapply no_dup_cons_removeEntry...
     eapply lts_rewrite_pf with (pf1 := nd_pf'0) in H21.
     assert (LTSIN0 := H21).
     subst pftmp. clear pf5 pf6.
     
      assert (nd_pf2 : NoDup (domain g2)).
      eapply no_dup_split_no_dup_r with (pf2 := pf2) (pf := pf)...
       assert (nd_pf3 : NoDup (domain g3)).
      eapply no_dup_split_no_dup_l with (pf1 := pf3) (pf := pf1)...
      assert (nd_pf4 : NoDup (domain g4)).
      eapply no_dup_split_no_dup_r with (pf2 := pf4) (pf := pf1)...
      assert (DIFF: (a1, a2) <> (b1, b2)).
      eapply nonRecActions2 in H19...

      assert (INa := H0).
      assert (IN1a := H16).
      assert (INb := H1).

      (*assert (K4IN:
                exists k4 : typeEnv, lts g4 q1 (aIn a1 a2 b1 b2) k4 q2 nd_pf4).
      eapply no_dup_isMap in nd_pf'0 as pf'0.
      eapply split_lts_exists_lts with (pf := pf'0).
      subst g7. Search s2.
      eapply split_comm...
      eauto.
      Search q1*)
      + assert (b1 = b0 /\ b2 = b3).
        eapply identif_payload with (q1 := p1)...
        eapply typeCheck_no_dup with (pf := pf3)...
      destruct H4; subst b0 b3.
      assert (EQT: t = t0).
      eapply tsub_payload with (pf := pf) in IN1a as EX.
      destruct EX as [p3 TYP2].
      inversion TYP2; subst.
      assert (vis = f /\ Chan un io t = Chan un p3 t0).
      eapply in_isMap... intuition. inversion H10...
      eauto.

      assert (G7: exists (f : flag), g7 = removeEntry (b1, b2) g1).
      exists ill...

      assert (EX: exists t, In (b1, b2, vis, t) g3).
      assert (FLG: flagOf g3 (b1, b2) vis \/ flagOf g3 (b1, b2) hid). eapply typeCheck_lts_out_payload...
      destruct FLG as [FLG1 | FLG2].
      inversion FLG1...
      inversion FLG2.  eapply fsub_hid with (pf := pf1) in H4. inversion H4; subst.
      eapply fsub_hid with (pf := pf) in H11.
      assert (vis = hid).
      eapply flag_of_map with (g := g)... discriminate.
      eauto. eauto.
      destruct EX as [tt3 IN3].
      assert (IN1b := H17).
      
      assert (TR: exists tt4 : piType, typeOf g4 (b1, b2) tt4 /\ type_remove s0 tt3 tt4).
      destruct s0. destruct m.
      assert (TR2: exists tt4 : piType, typeOf g4 (b1, b2) tt4 /\ type_plus tt3 tt4 (Chan lin p s0)).
      eapply split_type_plus with (g := g1)...
      destruct TR2 as [tt4 [TYP4 TP]]. exists tt4. unfold type_remove, is_unrestricted; intuition auto.
      destruct tt3, tt4; inversion TP...
      destruct H4 as [pp ABS]; inversion ABS.
      inversion H4.
      eapply tsuper_payload_r with (pf1 := pf3) (pf2 := pf4) in IN1b as TSUP.
      destruct TSUP as [p3 TSUP].
      eapply tsuper_payload with (pf1 := pf3) (pf2 := pf4) in IN1b as TSUP1. destruct TSUP1 as [p0 TSUP1].
      inversion TSUP1; subst.
      inversion TSUP; subst.
      assert (POLEQ: p0 = p3 /\ p3 = p).
      eapply split_plus_un with (pf1 := pf3) (pf2 := pf4) (pf3 := pf1) (b1 := b1) (b2 := b2)...
      intuition; subst.
      assert (vis = f /\ tt3 = Chan un p s0).
      eapply in_isMap... intuition; subst tt3 f. 
      unfold type_remove; exists (Chan un p s0); intuition.
      rewrite <-pol_cup_id at 3...
      eauto.
      eauto.
      exists Top; intuition.
      eapply tsuper_top_r...
      assert (typeOf g3 (b1, b2) Top).
      eapply tsuper_top...
      inversion H4; subst.
      assert (vis = f /\ tt3 = Top).
      eapply in_isMap... intuition; subst tt3 f.
      unfold type_remove; intuition auto.
      
      destruct TR as [tt4 [TYP4 TREM]]. inversion TREM as [TSUB [TP ISUN]].

       assert (EXSP: exists s02, typeOf g2 (b1, b2) s02 /\ type_plus s0 s02 s).
      eapply split_type_plus...
      destruct EXSP as [s02 [TYP2 TP2]].
      inversion TYP2; subst.
      assert (IN2b := H4). clear H4.
    
      assert (LTRO: exists s01, type_remove tt3 t0 s01).
       eapply tsuper_payload with (pf1 := pf3) in IN1a as K1.
      eapply fsuper_vis with (pf1 := pf3) in IN1a as [K2 _].
      destruct K1 as [p TYP3a]. inversion K2; subst.
      assert (t = Chan un p t0). eapply type_of_map with (g := g3)...
      eapply typeCheck_lts_out_type_remove with (a1 := a1) (a2 := a2) (b1 := b1) (b2 := b2)  (p := p1).
      eauto.
      subst...
      eauto. eauto. eauto. eauto. 
      destruct LTRO as [s03 TREM3].
      
      eapply no_dup_isMap in nd_pf_Out as pf_Out.
      specialize IHLTS1 with
          (pf := pf_Out) (g1  := g3) (pf1 := pf3).

      
      (*assert (RW: removeEntry (b1, b2)
                                       ((b1, b2, vis, s0) :: g7)= g7).
      unfold removeEntry; fold removeEntry; erewrite pairEq_eq_true...
      rewrite <-RW in H19 at 2. clear RW.
      move H19 at bottom.   *)
      
      eapply lts_type_remove_un_out with (pf1 := nd_pf3)  (s0 := tt3) (s01 := s03) in H19 as LTSOUT.

      
      move IHLTS1 at bottom.

      assert (nd_pfk3: NoDup (domain (( (b1, b2, vis, s03) :: removeEntry (b1, b2) g3)))).
      eapply no_dup_cons_removeEntry...
      apply no_dup_isMap in nd_pfk3 as pfk3.
      
      specialize IHLTS1 with
          (pfk1 := pfk3)  (nd_pf1 := nd_pf3). 
      assert (SL: sl_pos p1).
      eapply sl_pos_par_l...

      assert (TSO : exists k2 pfk2, tEnv_split g3 k2 g pf3 pfk2 pf_Out).
     eapply split_of_split with
          (pf1 := pf1) (pf2 := pf2) (pfw0 := pf4)...
      

     
      destruct TSO as [k2 [pfk2 TSK]].
      specialize IHLTS1 with (pf2 := pfk2).
      intuition.
      assert (TC1 := H5); clear H5.

      assert (LTRI: exists s04, type_plus tt4 t0 s04 /\
             (is_unrestricted s0 -> s03 = s04 /\ s04 = s0)).
      destruct t0. destruct m.
      assert (LT: exists s04, type_plus tt4 (Chan lin p t0) s04).
      inversion TREM3.
     
      eapply plus_sub_exists. eapply type_plus_comm...
      eauto.
      destruct LT as [s04 TP4'].
      exists s04. split. tauto.
      intros. destruct  H4 as [pp [tt  ABS]].
      inversion TP; inversion TP4'; subst; discriminate.
      assert (s03 = tt3 /\ s2 = s0 /\ tt4 = s0).
      assert (is_unrestricted tt3).
      inversion TREM3; destruct H5; inversion H5; subst; eapply un_is_unrestricted.
      assert (is_unrestricted s0).
      inversion TSUB; subst; eauto; destruct H4 as [pp [tt ISUN1]]; inversion ISUN1; subst; eapply un_is_unrestricted...
      apply ISUN in H5. subst.
      move TP at bottom.
      assert (s0 = tt3).
      destruct s0.
      assert (m = un). inversion H15; inversion H5...
      subst m. 
       eapply tsuper_payload with (pf1 := pf3) in IN1b as IN3'.
      eapply tsuper_payload with (pf1 := pf4) in IN1b as IN4'.
      destruct IN3' as [pp3 TYP3'];
        destruct IN4' as [pp4 TYP4'];
        inversion TYP3'; inversion TYP4'; clear TYP3'; clear TYP4'; subst.
      assert (tt3 =  Chan un pp3 s0).
      eapply type_of_map with (g := g3)...
      assert (POLEQ: pp3 = pp4 /\ pp4 = p0).
      eapply split_plus_un with (pf1 := pf3) (pf2 := pf4) (pf3 := pf1) (b1 := b1) (b2 := b2)...
      destruct POLEQ; subst...
      eapply split_comm...
      eauto.
      inversion TP; subst...
      subst tt3.  inversion TREM3; destruct H9 as [_ ISUN1]; apply ISUN1 in H4 as K; subst.
      inversion H15;destruct H10 as [_ ISUN2]; apply ISUN2 in H4 as K2; subst.
      intuition. intuition; subst.
      inversion H15; destruct H5 as [TP3 ISUN2].
      exists s0...
      split.
      eapply type_plus_comm...
      assert (is_unrestricted s0).
      inversion H4; subst; eapply un_is_unrestricted.
      intuition.
      destruct H5 as [pp [tt S0EQ]].
      subst. eapply tsuper_payload with (pf1 := pf3) in IN1b as K. destruct K as [pp1 K1]; inversion K1; subst.
      eapply tsuper_payload_r with (pf2 := pf4) in IN1b as K2.
      destruct K2 as [pp2 K2]; inversion K2; subst.
      assert (pp1 = pp2 /\ pp2 = pp).
      eapply split_plus_un...
      destruct H13; subst.
      eapply type_of_map with (g := g3)...
      eauto. eauto.
      
      inversion TREM3; inversion TP; intuition; subst; exists Top; eauto; try discriminate ||
      inversion H13 || inversion H12...
      
      destruct LTRI as [s04 [TP4 ISUN4]].
      
      move H21 at bottom.
      inversion H15 as [_ [TP1 ISUN1]].

      subst g'0.
      eapply lts_un_input_action with (s := s2) (r := s0) in H21 as K1EQ.
      destruct K1EQ as (ne &DISNE &K1EQ).
      
      assert (RW: removeEntry (b1, b2) ((b1, b2, vis, s2) :: g7) = g7).
        unfold removeEntry; fold removeEntry;
          rewrite pairEq_eq_true...
        rewrite K1EQ in LTSIN0.
        move LTSIN0 at bottom.
      eapply no_dup_isMap in nd_pf'0 as pf4'.
      
      
      move IHLTS2 at bottom.
      eapply no_dup_isMap in nd_pf_Inp as pf_Inp.

      


      specialize IHLTS2 with (pf := pf_Inp). 
      assert (SL2: sl_pos q1).
      eapply sl_pos_par_r...

     
      assert (EXSP2: exists s0t,
                type_remove s0 t0 s0t).
     eapply typeCheck_lts_out_type_remove with (pf := pf1).
     eauto.
     subst...
     eauto. econstructor...
     destruct EXSP2 as [s0t TREM2].
     

     assert (EXSP2: exists r4,
                type_plus tt4 r4 s1 /\ type_sub tt4 s1 /\
                (is_unrestricted s1 -> r4 = s1)).
     
      inversion H. destruct H5 as [TPP ISUNN].  inversion TREM2; subst. destruct H9 as [TPP2 ISUNN2].
        move TP at bottom. move TP2 at bottom.  move TP4 at bottom.
        
        apply T_Entry in IN1b as TYP1. move TYP1 at bottom.
        apply T_Entry in IN3 as TYP3. move TYP3 at bottom.
        move TYP4 at bottom.
        assert (PAYLOAD : t0 = t0)...


        assert (pp_emptyR: forall p r, pol_plus p empty r -> p =r). intros. inversion H9; destruct p, r...
         assert (pp_emptyL: forall p r, pol_plus empty p r -> p =r). intros. inversion H9; destruct p, r...
        destruct t0. destruct m.
        destruct p.
        * inversion TP4. inversion H11; subst...
            inversion TPP. inversion H12; subst...
            inversion TP; inversion TP2; subst...
            all: try discriminate.
            assert (p4 = p5)...
            assert (p0 = p)...
            inversion H20; inversion H26; subst.
            clear H13 H14 H18 H20 H26.
            assert (EXR: exists r, pol_plus p r p5).
            eapply pol_plus_of_pol_plus.
            eapply pol_plus_comm...
            eauto.
            destruct EXR as [r TPR].
            exists (Chan lin r t0).
            split.
            econstructor...
            split. eauto.
            intros ABS. eapply not_lin_is_unrestricted in ABS; intuition. 
        *inversion TP4; inversion H11; subst...
            inversion TPP; inversion H12; subst...
            inversion TP; inversion TP2; subst...
            move H15 at bottom.
            inversion H15; inversion H26; subst.
            destruct H10 as [TPP3 _]; inversion TPP3; subst.
            clear H14 H20 H26.
            destruct p0.
            exists (Chan lin p4 t0)...
            inversion H13.
            exists (Chan lin empty t0)...
            inversion H18; inversion H24; inversion H28; subst; try discriminate.
            split. econstructor...
            split. eauto. intros ABS. eapply not_lin_is_unrestricted in ABS; intuition.
             split. econstructor...
            split. eauto. intros ABS. eapply not_lin_is_unrestricted in ABS; intuition. 
            inversion H13.
        * inversion TP4; inversion H11; subst...
            inversion TPP; inversion H12; subst...
            inversion TP; inversion TP2; subst...
            move H15 at bottom.
            inversion H15; inversion H26; subst.
            destruct H10 as [TPP3 _]; inversion TPP3; subst.
            clear H14 H20 H26.
            destruct p0.
            exists (Chan lin p4 t0)...
            inversion H13.
            exists (Chan lin empty t0)...
            inversion H18; inversion H24; inversion H28; subst; try discriminate.
            split. econstructor...
            split. eauto. intros ABS. eapply not_lin_is_unrestricted in ABS; intuition.
             split. econstructor...
            split. eauto. intros ABS. eapply not_lin_is_unrestricted in ABS; intuition. 
            inversion H13.  inversion H13.
       * inversion TP4; inversion H11; subst...
            inversion TPP; inversion H12; subst...
            inversion TP; inversion TP2; subst...
            inversion H13; inversion H18; subst. clear H15.
            exists (Chan lin empty t0)...
        * inversion TP4; inversion TP; inversion TP2; subst...
            all:try discriminate.
            inversion TPP; subst.
            inversion H14; inversion H20; subst.
            assert (is_unrestricted (Chan un (pol_cup (pol_cup p4 p0) p7) t2)). eapply un_is_unrestricted...
            intuition. inversion H11.
            rewrite <-H24.
            assert (p4 = p0 /\ p0 = (pol_cup p4 p0)).
            inversion TYP1; inversion TYP4.
            eapply split_plus_un with (pf1 := pf3) (pf2 := pf4) (pf3 := pf1) (b1 := b1) (b2 := b2)...
            destruct H12; subst p4.
            assert ((pol_cup p0 p0) = p7 /\ p7 =  (pol_cup (pol_cup p0 p0) p7)).
            inversion TYP1; inversion TYP2.
             eapply split_plus_un with (pf1 := pf1) (pf2 := pf2) (pf3 := pf) (b1 := b1) (b2 := b2)...
             destruct H12. subst p7.
           rewrite <-H25,<-H25 in H11. subst.
           exists (Chan un p0 t2).
           split. rewrite <-H26. econstructor...
           split. eapply pol_cup_type_sub...
           intros _...
        * inversion TP4; inversion TPP; subst...
        * destruct EXSP2 as [r4 [TP4' [TSUB4' ISUN4']]].

        assert (nd_pf1' :
                NoDup
                  (domain
                     ((b1, b2, vis, s1)
                        ::  removeEntry (b1, b2) g1))).
        eapply no_dup_cons_removeEntry...
        eapply no_dup_isMap in nd_pf1' as pf1'.
       assert (nd_pf''' :
                NoDup
                  (domain
                     ((b1, b2, vis, r4)
                        :: removeEntry (b1, b2) g3))).
       eapply no_dup_cons_removeEntry...
      eapply no_dup_isMap in nd_pf''' as pf'''.
     
      move IHLTS2 at bottom.
      assert (IN4: In (a1, a2, vis, Chan un io t0) g4).
       inversion TYP4. subst. assert (IN4 := H4); clear H4 TYP4.
     eapply typeCheck_lts_in with (pf1 := pf4) in LTS2 as IN4a.
     destruct IN4a as [mm [tt [ABS | TYP4a]]].
     inversion ABS; subst.
      eapply tsuper_payload with (pf1 := pf4) in IN1a as K.
      destruct K as [pp1 TYP4]; inversion TYP4; subst.
      assert (EQ: Chan mm inp tt = Chan un pp1 t0).
      eapply type_of_map with (g := g4)...
      inversion EQ. subst. 
      eapply typeCheck_lts_out with (pf1 := pf3) in LTS1 as IN3a.
      destruct IN3a as [mm [ttt [ABS1 | ABS1]]].
      eapply tsuper_payload with (pf1 := pf3) in IN1a as K.
      destruct K as [pp1 TYP3]; inversion TYP3; subst.
      assert (EQ2: Chan mm out ttt = Chan un pp1 t0).
      eapply type_of_map with (g := g3)...
      inversion EQ2; subst.
      assert (ABS2: out = inp /\ inp = io).
      eapply split_plus_un with (pf1 := pf3) (pf2 := pf4)(pf3 := pf1) (b1 := a1) (b2 := a2)...
      destruct ABS2; discriminate.
      eauto.
       eapply tsuper_payload with (pf1 := pf3) in IN1a as K.
      destruct K as [pp1 TYP3]; inversion TYP3; subst.
      assert (EQ2: Chan mm io ttt = Chan un pp1 t0).
      eapply type_of_map with (g := g3)...
      inversion EQ2; subst.
      assert (ABS2: io = inp /\ inp = io).
      eapply split_plus_un with (pf1 := pf3) (pf2 := pf4)(pf3 := pf1) (b1 := a1) (b2 := a2)...
      destruct ABS2; discriminate.
      eauto. eauto. eapply split_comm...
     inversion TYP4a. subst. assert (IN4a := H4); clear H4 TYP4a.
     assert (EQ: f1 = vis /\ mm = un /\ tt = t0).
     eapply tsuper_payload with (pf1 := pf4) in IN1a as K.
     destruct K as [pp1 TYP4]; inversion TYP4; subst.
     eapply fsuper_vis with (pf1 := pf4) in IN1a as [K _].
     inversion K; subst.
     assert (f1 = vis). eapply flag_of_map with (g := g4)...
     assert (EQ: Chan mm io tt =  Chan un pp1 t0). eapply type_of_map with (g := g4)...
     inversion EQ;  intuition.
     eapply split_comm... eapply split_comm...
     destruct EQ as [EQ1 [EQ2 EQ3]]; subst...
     eauto.

     inversion TYP4. subst g5 n t.
     assert (f0 = vis).
     eapply fsuper_vis with (pf2 := pf4) in IN1b as [ _ K].
     eapply flag_of_map with (g := g4)...
     eauto.
     subst f0.

     assert (TSO : exists k'' pfk'', tEnv_split g4 k'' g' pf4 pfk'' pf_Inp).
     destruct tt4. destruct m. 
     (* m = lin *)
     assert (nd_pf'':
                NoDup
                  (domain
                     ((b1, b2, vis, Chan lin empty tt4)
                        :: removeEntry (b1, b2) g2))).
       eapply no_dup_cons_removeEntry...
       eapply no_dup_isMap in nd_pf'' as pf''.
     
     eapply split_of_split with
         (pf1 := pf1')  (pf2 := pf'') (pfw0 := pf''').
     eapply no_dup_cons_removeEntry...
     
      inversion TP4'; subst.
     eapply split_new_un_lin.
     eauto. eapply split_comm...
     eauto. eauto. eauto. 
     eauto. eauto.
      inversion TP4'; subst. subst g'.
     eapply tEnv_split_add_vis.
     eauto. eauto. intros ABS; eapply not_lin_is_unrestricted in ABS; intuition.
     eauto.
     (* m = un*)
     assert (EQ: s1 = s /\ s = Chan un p tt4).
      inversion H. destruct H9.
      eapply tsub_un with (pf := pf1) in H4 as K1. inversion K1; subst.
       eapply tsub_un with (pf := pf) in  H11 as K2. inversion K2; subst.
       assert (s = Chan un p tt4).
       eapply type_of_map with (g := g)...
       assert (s1 = Chan un p tt4).
       subst; assert (is_unrestricted (Chan un p tt4)). eapply un_is_unrestricted. intuition.
       subst... eauto. eapply split_comm...
       destruct EQ; subst.
       assert (r4 = Chan un p tt4).
       eapply ISUN4', un_is_unrestricted...
       subst.
     
      assert (nd_pf'':
                NoDup
                  (domain
                     ((b1, b2, vis, Chan un p tt4)
                        :: removeEntry (b1, b2) g2))).
       eapply no_dup_cons_removeEntry...
       eapply no_dup_isMap in nd_pf'' as pf''.
     
     eapply split_of_split with
         (pf1 := pf1')  (pf2 := pf'') (pfw0 := pf''').
     eapply no_dup_cons_removeEntry...
     eapply split_new_un_un with (a1 :=a1) (a2 := a2);
       try eassumption.
     eapply split_comm... 
     eauto.
     subst g';
       eapply tEnv_split_add_vis...
     (* typeOf g4 (b1, b2) Top *)
     inversion TP4'; subst.
      assert (nd_pf'':
                NoDup
                  (domain
                     ((b1, b2, vis, Top)
                        :: removeEntry (b1, b2) g2))).
       eapply no_dup_cons_removeEntry...
       eapply no_dup_isMap in nd_pf'' as pf''.
     eapply split_of_split with
         (pf1 := pf1')  (pf2 := pf'') (pfw0 := pf''').
     eapply no_dup_cons_removeEntry...
     eapply split_new_un_top; try eassumption.
     eapply split_comm...
     eauto.
     subst g';
       eapply tEnv_split_add_vis...

      
     destruct TSO as [k'' [pfk'' TSK'']].
     revert dependent pfk1.
     rewrite K1EQ.
     intros.
     move TC1 at bottom.
     assert (K4IN:
               exists k4 : typeEnv, lts g4 q1 (aIn a1 a2 b1 b2) k4 q2 nd_pf4).
     eapply split_lts_exists_lts with (pf := pf_Inp)...
     destruct K4IN as [k4 K4IN].
     eapply lts_un_input_action with (r := s04) in K4IN as K4EQ.
     destruct K4EQ as (ne4 &DIS4 &K4EQ).
     
     
     assert (nd_pfk4: NoDup(domain k4)).
     eapply lts_un_input_action_newEntries with (k := ne4) (pf := nd_pf4) in K4IN as K.
     destruct K as [NE4NIL | NE4REPL].
     subst; eapply no_dup_cons_removeEntry...
     destruct NE4REPL as (q & REPL &INCL &NE4REPL).
     subst ne4 k4.
     rewrite domain_distr; eapply distr_no_dup.
     eapply newEntries_no_dup.
     eapply wf_rewrite,prop27,incl_incl2.
     eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf4)...
     eauto.
     eapply incl_tran with (m := secLabs q1)...
     eapply typeCheck_no_dup with (pf := pf4)...
     eauto.
     eapply no_dup_cons_removeEntry...
     eapply disjoint_commute, disjoint_iff with (l1 := domain g4).  eapply new_entries_disjoint.
     unfold sl_pos, pos in *; intros.
     specialize SLP with x1 x2;
       unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL; specialize INCL with (x1,x2); intuition.
     assert (MAX: max(domain g1) >= max (secLabs q)).
     eapply incl_preserves_max, incl_tran with (m := secLabs q1)...
     assert(  incl (secLabs q1) (domain g4)).
     eapply typeCheck_no_dup with (pf := pf4)...
     eapply incl_iff with (m1 := domain g4);
       try eassumption.
     eapply split_domain_l_2,split_comm...
     erewrite split_max with (pf := pf1). lia.
     eapply split_comm...
     eapply in_removeEntry_cons_iff,in_g_in_domain...
     eauto.
     eauto.

     eapply disjoint_commute,disjoint_iff...
     eapply disjoint_commute...
     eapply sl_pos_par_r...
     eapply typeCheck_no_dup with (pf := pf4)...

     eapply no_dup_isMap in nd_pfk4 as pfk4.
     specialize IHLTS2 with (pfk1 := pfk4).
     move IHLTS2 at bottom.
     assert (sl_pos q1). eapply sl_pos_par_r...
     eapply IHLTS2 with (nd_pf1 := nd_pf4) (pf2 := pfk'') in H5.
     assert (TC2 := H5); clear H5 IHLTS2.
      
     
     remember ((b1, b2, vis, s2) :: g7) as g4'.
     assert (nd_pf4' : NoDup(domain g4')).
     subst...

      assert (DOMEQ:
                 forall x : name * name, In x (domain g4') <-> In x (domain g4)).
        subst g4' g7.
       assert (IFF1: forall x : name * name,
                  In x (domain g1) <-> In x (domain ((b1, b2, vis, s2) :: removeEntry (b1, b2) g1))).
       eapply in_removeEntry_cons_iff, in_g_in_domain...
       assert (IFF2: forall x : name * name,
                  In x (domain g4) <-> In x (domain  g1)).
       intros; eapply split_domain_r...
       intros. specialize IFF1 with x; specialize IFF2 with x; intuition.
     
     assert (NE:
               ne = nil \/
               exists q,
                 replication q1 q2 q /\
                 incl (secLabs q) (secLabs q1) /\
                 ne = newEntries g4' (secLabs (dep_relabel q (domain g4') nd_pf4')) (max (domain g4'))).
     eapply lts_un_input_action_newEntries.
     eauto. tauto. subst g4' g7. econstructor.
     right. eapply removeEntry_in...

      eapply disjoint_commute,disjoint_iff.
     eapply disjoint_commute...
     intros. rewrite <- in_removeEntry_cons_iff;
       try tauto; try subst g4'...
     eapply sl_pos_par_r...
     eapply typeCheck_no_dup with (pf := pf4)...
     
     assert (NE1:
               ne4 = nil \/
               exists q,
                 replication q1 q2 q /\
                 incl (secLabs q) (secLabs q1) /\
                 ne4 = newEntries g4 (secLabs (dep_relabel q (domain g4) nd_pf4)) (max (domain g4))).
     eapply lts_un_input_action_newEntries.
     eauto. eauto. subst g4' g7...

     eapply disjoint_commute,disjoint_iff...
     eapply disjoint_commute...
     eapply sl_pos_par_r...
     eapply typeCheck_no_dup with (pf := pf4)...
    
  


     assert (TPP: type_plus s03 s04 s0).
       move TP4 at bottom.
       inversion TREM as [_ [TP0 _]]; inversion TREM3 as [_ [TP3 _]].
         assert (pp_emptyR: forall p r, pol_plus p empty r -> p =r). intros. inversion H5; destruct p, r...
         assert (pp_emptyL: forall p r, pol_plus empty p r -> p =r). intros. inversion H5; destruct p, r...
       destruct t0. destruct m. destruct p.
       try inversion TP4; subst; eapply pp_emptyR in H12; subst; inversion TP3; inversion H10; subst; eapply pp_emptyL in H12; subst...
       try inversion TP3; subst; inversion H12;  subst; inversion TP4;  inversion TP0; subst; inversion H13; subst; inversion H18; subst; inversion H25; subst...
       try inversion TP3; subst; inversion H12;  subst; inversion TP4;  inversion TP0; subst; inversion H13; subst; inversion H18; subst; inversion H25; subst...
       try inversion TP3; subst; inversion H12;  subst; inversion TP4;  inversion TP0; subst; inversion H13; subst; inversion H18; subst; inversion H25; subst...
       assert (PDS: forall p5 p0 p, pol_cup p5 (pol_cup p0 p) = pol_cup (pol_cup p p5) p0).
       intros a b c. destruct a,b,c...
       try inversion TP4; inversion TP0; subst; try discriminate; inversion H13;  subst; inversion TP3; subst;
        erewrite <-PDS...
       try inversion TP4; inversion TP0; subst; try discriminate; inversion TP3; subst...
     
     destruct NE, NE1.
     
     (* NON REPLICATED INPUT *)
     **** subst ne ne4.
      assert (nd_pfk :
                 NoDup (domain
                          (( (b1, b2, vis, s04) :: removeEntry (b1, b2) g4)))).
       eapply no_dup_cons_removeEntry...
       eapply no_dup_isMap in nd_pfk as pfk.
       
       eapply TPar with (pf1 := pfk3) (pf2 := pfk4).
       assert (EQ: (nil ++ (b1, b2, vis, s0) :: removeEntry (b1, b2) g4') =(b1, b2, vis, s0) :: removeEntry (b1, b2) g4').
       simpl...
       revert dependent pfk1. rewrite EQ. intros.
       subst g4'. revert dependent pfk1.
       unfold removeEntry. fold removeEntry.
       rewrite pairEq_eq_true. intros.
       subst g7 k4.
       eapply tEnv_split_add_vis...
       eauto. eauto.
     **** 
       destruct H9 as [q [REPL [INCL NE4EQ]]].
       assert (NEEQ: ne = newEntries g4' (secLabs (dep_relabel q (domain g4') nd_pf4')) (max (domain g4'))).
       eapply lts_un_input_action_newEntries_2;
       try eapply typeCheck_no_dup with (pf := pf4)...

       eapply disjoint_commute,disjoint_iff.
       eapply disjoint_commute...
       intros. rewrite <- in_removeEntry_cons_iff;
         try tauto; try subst g4'...
       
       erewrite identif_seclabs_of_dep_relabel in NEEQ.
       assert (MAX: max (domain g4') = max (domain (g4))).
       eapply max_same_domain...
       erewrite MAX,<-identif_seclabs_of_dep_relabel in NEEQ.
       assert (NENIL: ne4 = nil).
       subst ne4; eapply newEntries_nil with (g := g4')...
       subst...
       
       eapply TPar with (pf1 := pfk3) (pf2 := pfk4).
       subst. revert dependent pfk4. rewrite NENIL. intros.
       revert dependent pfk1.
       unfold removeEntry. fold removeEntry.
       rewrite pairEq_eq_true. intros.
       eapply tEnv_split_add_vis...
       eauto. eauto.

     ****

       destruct H5 as [q [REPL [INCL NE4EQ]]].
       assert (NEEQ: ne4 = newEntries g4 (secLabs (dep_relabel q (domain g4) nd_pf4)) (max (domain g4))).
       eapply lts_un_input_action_newEntries_2;
         try eapply typeCheck_no_dup with (pf := pf4)...

       eapply disjoint_commute,disjoint_iff.
     eapply disjoint_commute...
     intros. rewrite <- in_removeEntry_cons_iff;
       try tauto; try subst g4'...
       
       erewrite identif_seclabs_of_dep_relabel in NEEQ.
       assert (MAX: max (domain g4') = max (domain (g4))).
       eapply max_same_domain...
       erewrite <-MAX in NEEQ.
       erewrite <-identif_seclabs_of_dep_relabel with (pf := nd_pf4')in NEEQ.
       assert (NENIL: ne = nil).
       subst ne; eapply newEntries_nil with (g := g4).
       eauto.
       eauto. subst...
       
       eapply TPar with (pf1 := pfk3) (pf2 := pfk4).
       subst. revert dependent pfk1. rewrite NENIL. intros.
       revert dependent pfk1.
       unfold removeEntry. fold removeEntry.
       rewrite pairEq_eq_true. intros.
       eapply tEnv_split_add_vis...
       eauto. eauto.
       
       (* REPLICATED INPUT *)
     ****
       destruct H5 as  [rp' [RP' [INRP' EQNE']]].
       destruct H9 as  [rp [RP [INRP EQNE4]]].
       assert (rp = rp').
       eapply replication_unique...
       subst rp'. clear RP'.
       revert dependent pfk4. rewrite K4EQ. intros.
       move Heqg4' at bottom. subst g7.
       revert dependent pfk1.
       rewrite Heqg4'.
       unfold removeEntry; fold removeEntry; rewrite pairEq_eq_true. intros.
       
       remember ( newEntries g3 (secLabs (dep_relabel rp (domain g3) nd_pf3)) (max (domain g3))) as ne3.
       remember ( newEntries g1 (secLabs (dep_relabel rp (domain g1) nd_pf1)) (max (domain g1))) as ne1.
       assert (nd_pfne4: NoDup(domain ne4)).
       subst. eapply newEntries_no_dup...
       eapply wf_rewrite,prop27,incl_incl2.
       eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf4)...
       eauto.
       eapply incl_tran with (m := secLabs q1)...
       eapply typeCheck_no_dup with (pf := pf4)...
       assert (nd_pfne3: NoDup(domain ne3)).
       subst. eapply newEntries_no_dup...
       eapply wf_rewrite,prop27,incl_incl2.
       eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf4)...
       eauto.
       eapply incl_tran with (m := secLabs q1)...
       assert ( incl (secLabs q1) (domain g4)).
       eapply typeCheck_no_dup with (pf := pf4)...
       eapply incl_iff with (m1 := domain g4);
         try eassumption.
       intros; eapply split_domain_m.
       eapply split_comm...
        assert (nd_pfne1: NoDup(domain ne1)).
       subst. eapply newEntries_no_dup...
       eapply wf_rewrite,prop27,incl_incl2.
       eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf4)...
       eauto.
       eapply incl_tran with (m := secLabs q1)...
       assert ( incl (secLabs q1) (domain g4)).
       eapply typeCheck_no_dup with (pf := pf4)...
       eapply incl_iff with (m1 := domain g4);
         try eassumption.
       intros; eapply split_domain_r...
       eapply no_dup_isMap in nd_pfne4 as pfne4.
       eapply no_dup_isMap in nd_pfne3 as pfne3.
       eapply no_dup_isMap in nd_pfne1 as pfne1.
       
       assert (TSNE: tEnv_split ne3 ne4 ne1 pfne3 pfne4 pfne1).
       subst; eapply split_newEntries...
       assert (ne1 = ne).
       subst.
       assert (MAX : (max (domain g1) =
                      (max (domain ((b1, b2, vis, s2) :: removeEntry (b1, b2) g1))))).
       eapply max_same_domain,in_removeEntry_cons_iff, in_g_in_domain...
       erewrite <-MAX.
       assert (EQ: secLabs
                 (dep_relabel rp (domain ((b1, b2, vis, s2) :: removeEntry (b1, b2) g1)) nd_pf4') =
               secLabs (dep_relabel rp (domain g1) nd_pf1)).
       erewrite identif_seclabs_of_dep_relabel,<-MAX,<-identif_seclabs_of_dep_relabel with (pf := nd_pf1)...
       rewrite EQ.
        
      eapply newEntries_removeEntry.
      eauto.
      assert (SLPQ1: sl_pos q1). 
      eapply sl_pos_par_l in SLP...
      unfold sl_pos,pos; intros.
      move INRP at bottom.
      unfold incl in INRP; specialize INRP with (x1, x2).
      apply INRP in H5; unfold sl_pos, pos in SLPQ1;
        specialize SLPQ1  with x1 x2...
       intros ABS. unfold incl in INRP; specialize INRP with (b1, b2); eapply INRP in ABS.
       assert (ABS2: exists t, In (b1, b2, hid, t ) g4).
       eapply typeCheck_hid...
       destruct ABS2 as [tt ABS2].
       assert (hid = vis).
       eapply flag_of_map with (g := g4)...
       discriminate.
       subst ne1.
       
       
       move TC1 at bottom.  move TC2 at bottom.

        assert (nd_pfnek3:
                           NoDup
                             (domain
                                (ne3 ++
                                     ((b1, b2, vis, s03)
                                        :: removeEntry (b1, b2) g3)))).
        erewrite domain_distr, no_dup_iff.
        split. assumption.
        split. eapply no_dup_cons_removeEntry...
        erewrite disjoint_commute. subst ne3.
        assert (DIS: disjoint (domain g3)
    (domain
       (newEntries g3 (secLabs (dep_relabel rp (domain g3) nd_pf3))
          (max (domain g3))))).
        eapply new_entries_disjoint.
        unfold sl_pos, pos in *; intros.
        specialize SLP with x1 x2;
                   unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INRP; specialize INRP with (x1,x2); intuition.
        assert (MAX: max(domain g3) >= max (secLabs rp)).
        eapply incl_preserves_max, incl_tran with (m := secLabs q1)... assert(  incl (secLabs q1) (domain g4)).
        eapply typeCheck_no_dup with (pf := pf4)...
        eapply incl_iff with (m1 := domain g4);
          try eassumption.
        intros; eapply split_domain_m,split_comm... 
        lia.
        eapply disjoint_iff with (l1  := domain g3), in_removeEntry_cons_iff,in_g_in_domain...
        eapply no_dup_isMap in nd_pfnek3 as pfnek3.

        assert (TC' :
                  typeCheck ( ne3 ++ (b1, b2, vis, s03) :: removeEntry (b1, b2) g3) pfnek3 p2).
        eapply typeCheck_weak2 with (pfk := pfne3).
        erewrite <-domain_distr...
        eauto. 
        (* cons ne3 pfne3 *)
        assert (INVNE: forall c1 c2 ff tt,
                   In (c1, c2, ff, tt) ne3 ->
                   In (c1, c2 - max (domain g3)) (secLabs rp) /\ In (c1, c2 - max (domain g3), ff, tt) g3).
        intros.
        eapply inverse_newEntries.
        eauto.
        (* sl_pos rp *)
          unfold sl_pos in SL2;
          unfold sl_pos.
        eapply incl_pos with (l2 :=(secLabs q1))...
        (* incl (secLabs rp) (domain g3) *)
        eapply incl_tran with (m := secLabs q1).
        assumption.
        eapply incl_iff with (m1 := domain g4).
        eapply typeCheck_no_dup with (pf := pf4)...
        intros. eapply split_domain_m,split_comm...
        (*In (c1, c2, ff, tt)
    (newEntries g3
       (map (fun x : name * name => (fst x, snd x + max (domain g3))) (secLabs rp))
       (max (domain g3)))*)
        subst. erewrite <-identif_seclabs_of_dep_relabel...
        eapply cons_char.
        destruct ne3. left...
        right. intros.
        specialize INVNE with c1 c2 ff tt.
        apply INVNE in H9; clear INVNE.
        destruct H9 as [INSL IN3'].
        remember (c2 - max (domain g3)) as c''.
        assert (ff = ill).
        assert (IN1: In (c1, c'') (secLabs q1)).
        eapply INRP...
        assert (NOTINSL: ~In (c1, c'') (secLabs p1)).
        intros ABS.
        assert (ND: NoDup (secLabs (dPar p1 q1))).
        eapply typeCheck_no_dup with (pf := pf1)...
        unfold secLabs in ND. fold secLabs in ND.
        erewrite no_dup_iff in ND; destruct ND as [ND1 [ND2 DIS]].
        eapply disjoint_absurd...
        assert (NOTINFN: ~ In (c1, c'') (fn p1)).
        intros ABS.
        assert (DIS: disjoint (fn (dPar p1 q1)) (secLabs (dPar p1 q1))).
        eapply fn_disjoint_sl with (pf := pf1)...
        unfold fn, secLabs in DIS;
          fold fn in DIS; fold secLabs  in DIS.
        eapply disjoint_absurd with (x:= (c1, c'')) (l := (fn p1 ++ fn q1)) (m := (secLabs q1 ++ secLabs p1)).
        eauto. eapply in_app_iff; left...
        eapply in_app_iff; left...
        assert (IN0: exists tt, In (c1, c'', hid, tt) g4).
        eapply typeCheck_hid...
        destruct IN0 as [ttt F0].
        assert (F1: In (c1, c'') (domain g1)).
        eapply split_domain_l_2 with (x := (c1, c'')) in H6 as K.  eapply in_g_in_domain in IN3' as K1; eapply K in K1...
        eapply in_domain_in_g in F1.
        destruct F1 as [f1 [tt1 F1]].
        assert (FP: exists f3, flagOf g3 (c1, c'') f3 /\ flag_plus hid f3 f1).
        eapply split_flag_plus with (pf1 := pf4) (pf2 := pf3) (pf := pf1), split_comm...
        destruct FP as [f3' [F3 FP]].
        assert (ff = f3').
        eapply flag_of_map with (g := g3) (x := (c1, c''))...
        subst ff.
        assert (F1': flagOf g1 (c1, c'')  hid).
        eapply fsub_hid,split_comm...
        inversion F1'. subst g5 n f0.
        assert (f1 = hid).
        eapply flag_of_map with (g := g1) (x := (c1, c''))...
        subst f1.
        inversion FP...

        subst.
        eapply typeCheck_ill with (p := p1)...
       
        subst ne3;
          rewrite identif_seclabs_of_dep_relabel in *;
          eapply Peirce; intros ABS;
          eapply not_disjoint in ABS as ([x1 x2] &ABS1 &ABS2);
          eapply in_bv_lt_max with (pf := pfk3) in ABS1;
          eapply in_domain_in_g in ABS2 as (ff &tt &ABS2);
          eapply newEntries_gte_max in ABS2;
          try lia;
          try eassumption.
        erewrite max_same_domain with (l := domain g3) in ABS1;
          try lia.
        intros. erewrite <-in_removeEntry_cons_iff; try tauto.
        eauto.
        eapply TPar with
          (pf1 := pfnek3) (pf2 := pfk4).

        
          

                 (*  tEnv_split (ne3 ++ (b1, b2, vis, s03) :: removeEntry (b1, b2) g3)
    (ne4 ++ (b1, b2, vis, s04) :: removeEntry (b1, b2) g4)
    (ne ++ (b1, b2, vis, s0) :: removeEntry (b1, b2) g1) pfnek3 pfk4 pfk1*)

       revert dependent pfk1. rewrite <-H5. intros.
        eapply split_distr with
            (pf1 := pfne3) (pf2 := pfne4) (pf := pfne1).
        eauto.
        eapply tEnv_split_add_vis...
        eauto.
        eauto.
     **** eauto.
     **** eauto.
     **** eauto.
     **** eauto.
     **** eauto.
     **** eauto.
     **** eauto.
     **** eapply incl_preserves_max, typeCheck_no_dup...
        *  subst g7. econstructor. right. eapply removeEntry_in...
        * eauto.
        * eapply type_plus_comm...
        * eauto.
        * subst g7.
          erewrite <-max_removeEntry_cons; try eassumption.
          erewrite <-split_max with (g := g1) (g1 := g4);
            try eassumption.
          try eapply incl_preserves_max, typeCheck_no_dup...
          eapply split_comm...
          eauto.
        * eauto.
        * eauto.
        * eauto.
        * eapply tsuper_payload with (pf1 := pf3) in IN1a as K.
          destruct K as [pp3 TYP3].
          inversion TYP3; subst.
          eapply fsuper_vis with (pf1 := pf3) in IN1a as K.
          destruct K as [FYP3 _].
          eapply tsub_un with (pf := pf1) in H4 .
          inversion TYP3; inversion FYP3; subst.
          assert (Chan un pp3 t0 = Chan un io t0).
          eapply type_of_map with (g := g1)...
          rewrite <-H9.
           assert (f1 = vis).
          eapply flag_of_map with (g := g3)...
          subst...
          all:eauto.
        * eauto.
        * eauto.
        * eapply typeCheck_no_dup with (pf := pf3)...
        * (* incl (secLabs p1) (domain (hid_proj g3)) *)
          eapply typeCheck_hid_proj...

    - Case uclsL .
      intros.
      remember pf0 as nd_pf. remember pf1 as nd_pf_Out.
      remember pf2 as nd_pf_Inp. subst pf0 pf1 pf2.
      remember pf4 as pf1.  remember pf3 as pf2. 
      subst pf4 pf3.
      
                        
      inversion TYP. inversion AFT; subst.
       remember g3 as gk3. remember g4 as gtmp. subst g3 g4.
      remember gtmp as g3. remember g5 as g4. subst g5 gtmp.
      assert (TSSUB := H6).
      remember pf3 as pf4. subst pf3.
      remember pf0 as pf3. subst pf0.

      assert (ABS: Chan un io t = Chan lin io t0).
      eapply tsub_io with (pf := pf) in H20 as K.
      eapply type_of_map with (g := g)...
      eauto. inversion ABS...
      
      remember g3 as gk3. remember g4 as gtmp. subst g3 g4.
      remember gtmp as g3. remember g5 as g4. subst g5 gtmp.
      assert (TSSUB := H6).
      remember pf3 as pf4. subst pf3.
      remember pf0 as pf3. subst pf0.

      
      assert (nd_pf2 : NoDup (domain g2)).
      eapply no_dup_split_no_dup_r with (pf2 := pf2) (pf := pf)...
       assert (nd_pf3 : NoDup (domain g3)).
      eapply no_dup_split_no_dup_l with (pf1 := pf3) (pf := pf1)...
      assert (nd_pf4 : NoDup (domain g4)).
      eapply no_dup_split_no_dup_r with (pf2 := pf4) (pf := pf1)...
      assert (DIFF: (a1, a2) <> (b1, b2)).
      eapply nonRecActions2 in LTS1...

      assert (TC_OUT := H7).
      assert (TC_INP := H8).
      assert (INa := H0).
      assert (IN1a := H19).
      assert (INb := H1).
      assert (IN1b := H21).
      assert (LTSOUTSUB := H22).
      assert (LTSINSUB := H23).
      clear H19 H21 H22 H23.
      remember pf6 as nd_pf'0. subst pf6.

      
      (*assert (K4IN:
                exists k4 : typeEnv, lts g4 q1 (aIn a1 a2 b1 b2) k4 q2 nd_pf4).
      eapply no_dup_isMap in nd_pf'0 as pf'0.
      eapply split_lts_exists_lts with (pf := pf'0).
      subst g7. Search s2.
      eapply split_comm...
      eauto.
      Search q1*)
      + 
      assert (EQT: t = t0).
      eapply tsub_payload with (pf := pf) in IN1a as EX.
      destruct EX as [p3 TYP2].
      inversion TYP2; subst.
      assert (vis = f /\ Chan un io t = Chan un p3 t0).
      eapply in_isMap... intuition. inversion H10...
      eauto.
      

      assert (EX: exists t, In (b1, b2, hid, t) g3).
      assert (FLG: flagOf g3 (b1, b2) vis \/ flagOf g3 (b1, b2) hid). eapply typeCheck_lts_out_payload...
      destruct FLG as [FLG1 | FLG2].
      inversion FLG1.  eapply fsub_vis with (pf := pf1) in H4. inversion H4; subst.
      eapply fsub_vis with (pf := pf) in H11.
      assert (vis = hid).
      eapply flag_of_map with (g := g)... discriminate.
      eauto. eauto.
      inversion FLG2...
      destruct EX as [tt3 IN3].
      
      assert (TR: exists tt4 : piType, typeOf g4 (b1, b2) tt4 /\ type_remove s0 tt3 tt4).
      destruct s0. destruct m.
      assert (TR2: exists tt4 : piType, typeOf g4 (b1, b2) tt4 /\ type_plus tt3 tt4 (Chan lin p s0)).
      eapply split_type_plus with (g := g1)...
      destruct TR2 as [tt4 [TYP4 TP]]. exists tt4. unfold type_remove, is_unrestricted; intuition auto.
      destruct tt3, tt4; inversion TP...
      destruct H4 as [pp ABS]; inversion ABS.
      inversion H4.
      eapply tsuper_payload_r with (pf1 := pf3) (pf2 := pf4) in IN1b as TSUP.
      destruct TSUP as [p3 TSUP].
      eapply tsuper_payload with (pf1 := pf3) (pf2 := pf4) in IN1b as TSUP1. destruct TSUP1 as [p0 TSUP1].
      inversion TSUP1; subst.
      inversion TSUP; subst.
      assert (POLEQ: p0 = p3 /\ p3 = p).
      eapply split_plus_un with (pf1 := pf3) (pf2 := pf4) (pf3 := pf1) (b1 := b1) (b2 := b2)...
      intuition; subst.
      assert (hid = f /\ tt3 = Chan un p s0).
      eapply in_isMap... intuition; subst tt3 f. 
      unfold type_remove; exists (Chan un p s0); intuition. 
      rewrite <-pol_cup_id at 3...
      eauto.
      eauto.
      exists Top; intuition.
      eapply tsuper_top_r...
      assert (typeOf g3 (b1, b2) Top).
      eapply tsuper_top...
      inversion H4; subst.
      assert (hid = f /\ tt3 = Top).
      eapply in_isMap... intuition; subst tt3 f.
      unfold type_remove; intuition auto.
      
      destruct TR as [tt4 [TYP4 TREM]]. inversion TREM as [TSUB [TP ISUN]].

       assert (EXSP: exists s02, typeOf g2 (b1, b2) s02 /\ type_plus s0 s02 s).
      eapply split_type_plus...
      destruct EXSP as [s02 [TYP2 TP2]].
      inversion TYP2; subst.
      assert (IN2b := H4). clear H4.
    
      assert (LTRO: exists s01, type_remove tt3 t0 s01).
       eapply tsuper_payload with (pf1 := pf3) in IN1a as K1.
      eapply fsuper_vis with (pf1 := pf3) in IN1a as [K2 _].
      destruct K1 as [p TYP3a]. inversion K2; subst.
      assert (t = Chan un p t0). eapply type_of_map with (g := g3)...
      eapply typeCheck_lts_out_type_remove with (a1 := a1) (a2 := a2) (b1 := b1) (b2 := b2)  (p := p1).
      eauto.
      subst...
      eauto. eauto. eauto. eauto. 
      destruct LTRO as [s03 TREM3].
      
      eapply no_dup_isMap in nd_pf_Out as pf_Out.
      specialize IHLTS1 with
          (pf := pf_Out) (g1  := g3) (pf1 := pf3).

      
      (*assert (RW: removeEntry (b1, b2)
                                       ((b1, b2, vis, s0) :: g7)= g7).
      unfold removeEntry; fold removeEntry; erewrite pairEq_eq_true...
      rewrite <-RW in H19 at 2. clear RW.
      move H19 at bottom.   *)
      
      eapply lts_type_remove_un_out with (pf1 := nd_pf3)  (s0 := tt3) (s01 := s03) in LTSOUTSUB as LTSOUT.

      
      move IHLTS1 at bottom.

      assert (nd_pfk3: NoDup (domain (( (b1, b2, vis, s03) :: removeEntry (b1, b2) g3)))).
      eapply no_dup_cons_removeEntry...
      apply no_dup_isMap in nd_pfk3 as pfk3.
      
      specialize IHLTS1 with
          (pfk1 := pfk3)  (nd_pf1 := nd_pf3). 
      assert (SL: sl_pos p1).
      eapply sl_pos_par_l...

      assert (TSO : exists k2 pfk2, tEnv_split g3 k2 g pf3 pfk2 pf_Out).
     eapply split_of_split with
          (pf1 := pf1) (pf2 := pf2) (pfw0 := pf4)...
      

     
      destruct TSO as [k2 [pfk2 TSK]].
      specialize IHLTS1 with (pf2 := pfk2).
      intuition.
      assert (TC1 := H5); clear H5.
      assert (H15 := H17).

      assert (LTRI: exists s04, type_plus tt4 t0 s04 /\
             (is_unrestricted s0 -> s03 = s04 /\ s04 = s0)).
      destruct t0. destruct m.
      assert (LT: exists s04, type_plus tt4 (Chan lin p t0) s04).
      inversion TREM3.
     
      eapply plus_sub_exists. eapply type_plus_comm...
      eauto.
      destruct LT as [s04 TP4'].
      exists s04. split. tauto.
      intros. destruct  H4 as [pp [tt  ABS]].
      inversion TP; inversion TP4'; subst; discriminate.
      assert (s03 = tt3 /\ s2 = s0 /\ tt4 = s0).
      assert (is_unrestricted tt3).
      inversion TREM3; destruct H5; inversion H5; subst; eapply un_is_unrestricted.
      assert (is_unrestricted s0).
      inversion TSUB; subst; eauto; destruct H4 as [pp [tt ISUN1]]; inversion ISUN1; subst; eapply un_is_unrestricted...
      apply ISUN in H5. subst.
      move TP at bottom.
      assert (s0 = tt3).
      destruct s0.
      assert (m = un). inversion H17. inversion H5...
      subst m. 
       eapply tsuper_payload with (pf1 := pf3) in IN1b as IN3'.
      eapply tsuper_payload with (pf1 := pf4) in IN1b as IN4'.
      destruct IN3' as [pp3 TYP3'];
        destruct IN4' as [pp4 TYP4'];
        inversion TYP3'; inversion TYP4'; clear TYP3'; clear TYP4'; subst.
      assert (tt3 =  Chan un pp3 s0).
      eapply type_of_map with (g := g3)...
      assert (POLEQ: pp3 = pp4 /\ pp4 = p0).
      eapply split_plus_un with (pf1 := pf3) (pf2 := pf4) (pf3 := pf1) (b1 := b1) (b2 := b2)...
      destruct POLEQ; subst...
      eapply split_comm...
      eauto.
      inversion TP; subst...
      subst tt3.  inversion TREM3; destruct H9 as [_ ISUN1]; apply ISUN1 in H4 as K; subst.
      inversion H17;destruct H10 as [_ ISUN2]; apply ISUN2 in H4 as K2; subst.
      intuition. intuition; subst.
      inversion H17; destruct H5 as [TP3 ISUN2].
      exists s0...
      split.
      eapply type_plus_comm...
      assert (is_unrestricted s0).
      inversion H4; subst; eapply un_is_unrestricted.
      intuition.
      destruct H5 as [pp [tt S0EQ]].
      subst. eapply tsuper_payload with (pf1 := pf3) in IN1b as K. destruct K as [pp1 K1]; inversion K1; subst.
      eapply tsuper_payload_r with (pf2 := pf4) in IN1b as K2.
      destruct K2 as [pp2 K2]; inversion K2; subst.
      assert (pp1 = pp2 /\ pp2 = pp).
      eapply split_plus_un...
      destruct H13; subst.
      eapply type_of_map with (g := g3)...
      eauto. eauto.
      
      inversion TREM3; inversion TP; intuition; subst; exists Top; eauto; try discriminate ||
      inversion H13 || inversion H12...
      
      destruct LTRI as [s04 [TP4 ISUN4]].
      
      inversion H15 as [_ [TP1 ISUN1]].

      subst g'0.
      eapply lts_un_input_action with (s := s2) (r := s0) in LTSINSUB as K1EQ.
      destruct K1EQ as (ne &DISNE &K1EQ).
      
      assert (RW: removeEntry (b1, b2) ((b1, b2, vis, s2) :: g6) = g6).
        unfold removeEntry; fold removeEntry;
          rewrite pairEq_eq_true...
        rewrite K1EQ in LTSINSUB.
        move LTSINSUB at bottom.
      eapply no_dup_isMap in nd_pf'0 as pf4'.
     
      
      move IHLTS2 at bottom.
      eapply no_dup_isMap in nd_pf_Inp as pf_Inp.



      specialize IHLTS2 with (pf := pf_Inp). 
      assert (SL2: sl_pos q1).
      eapply sl_pos_par_r...

     
      assert (EXSP2: exists s0t,
                type_remove s0 t0 s0t).
     eapply typeCheck_lts_out_type_remove with (pf := pf1).
     eauto.
     subst...
     eauto. econstructor...
     destruct EXSP2 as [s0t TREM2].
     

     assert (EXSP2: exists r4,
                type_plus tt4 r4 s1 /\ type_sub tt4 s1 /\
                (is_unrestricted s1 -> r4 = s1)).
     
      inversion H. destruct H5 as [TPP ISUNN].  inversion TREM2; subst. destruct H9 as [TPP2 ISUNN2].
        move TP at bottom. move TP2 at bottom.  move TP4 at bottom.
        
        apply T_Entry in IN1b as TYP1. move TYP1 at bottom.
        apply T_Entry in IN3 as TYP3. move TYP3 at bottom.
        move TYP4 at bottom.
        assert (PAYLOAD : t0 = t0)...

        clear H17.
        assert (pp_emptyR: forall p r, pol_plus p empty r -> p =r). intros. inversion H9; destruct p, r...
         assert (pp_emptyL: forall p r, pol_plus empty p r -> p =r). intros. inversion H9; destruct p, r...
        destruct t0. destruct m.
        destruct p.
        * inversion TP4. inversion H11; subst...
            inversion TPP. inversion H12; subst...
            inversion TP; inversion TP2; subst...
            all: try discriminate.
            assert (p4 = p5)...
            assert (p0 = p)...
            inversion H20. inversion H20; subst.
            clear H13 H14 H17 H20 H19.
            assert (EXR: exists r, pol_plus p r p5).
            eapply pol_plus_of_pol_plus.
            eapply pol_plus_comm...
            eauto.
            destruct EXR as [r TPR].
            exists (Chan lin r t0).
            split.
            econstructor...
            split. eauto.
            intros ABS. eapply not_lin_is_unrestricted in ABS; intuition. 
        * inversion TP4; inversion H11; subst...
            inversion TPP; inversion H12; subst...
            inversion TP; inversion TP2; subst...
            inversion H20; subst.
            move H15 at bottom.
            inversion H15. inversion H10; subst.
            destruct H10 as [TPP3 _]; inversion TPP3; subst.
            clear H14 H17 H20.
            destruct p0.
            exists (Chan lin p4 t0)...
            inversion H13.
            exists (Chan lin empty t0)...
            inversion H16; subst; inversion H22; subst; inversion H18.  split. econstructor...
            split. eauto. intros ABS. eapply not_lin_is_unrestricted in ABS; intuition.
             split. econstructor...
            split. eauto. intros ABS. eapply not_lin_is_unrestricted in ABS; intuition. 
            inversion H13.
        *inversion TP4; inversion H11; subst...
            inversion TPP; inversion H12; subst...
            inversion TP; inversion TP2; subst...
            inversion H20; subst.
            move H15 at bottom.
            inversion H15. inversion H10; subst.
            destruct H10 as [TPP3 _]; inversion TPP3; subst.
            clear H14 H17 H20.
            destruct p0.
            exists (Chan lin p4 t0)...
            inversion H13.
            exists (Chan lin empty t0)...
            inversion H16; subst; inversion H22; subst; inversion H18.  split. econstructor...
            split. eauto. intros ABS. eapply not_lin_is_unrestricted in ABS; intuition.
             split. econstructor...
            split. eauto. intros ABS. eapply not_lin_is_unrestricted in ABS; intuition. 
            inversion H13. inversion H13.
       * inversion TP4; inversion H11; subst...
            inversion TPP; inversion H12; subst...
            inversion TP; inversion TP2; subst...
            inversion H13; inversion H18; subst. clear H15.
            inversion H16; subst;
              exists (Chan lin empty t0)...
            inversion H16; subst;
              exists (Chan lin empty t0)...
            all:try discriminate.
        * inversion TP4; inversion TP; inversion TP2; subst...
            all:try discriminate.
            inversion TPP; subst.
            inversion H14. inversion H17; subst.
            assert (is_unrestricted (Chan un (pol_cup (pol_cup p4 p0) p7) t2)). eapply un_is_unrestricted...
            intuition. inversion H11.
            rewrite <-H18.
            assert (p4 = p0 /\ p0 = (pol_cup p4 p0)).
            inversion TYP1; inversion TYP4.
            eapply split_plus_un with (pf1 := pf3) (pf2 := pf4) (pf3 := pf1) (b1 := b1) (b2 := b2)...
            destruct H12; subst p4.
            assert ((pol_cup p0 p0) = p7 /\ p7 =  (pol_cup (pol_cup p0 p0) p7)).
            inversion TYP1; inversion TYP2.
             eapply split_plus_un with (pf1 := pf1) (pf2 := pf2) (pf3 := pf) (b1 := b1) (b2 := b2)...
             destruct H12. subst p7.
           rewrite <-H19 in H18. 
           exists (Chan un p0 t2).
           split. rewrite H18. econstructor...
           split. eapply pol_cup_type_sub...
           subst; intros _...
        * inversion TP4; inversion TPP; subst...
        * destruct EXSP2 as [r4 [TP4' [TSUB4' ISUN4']]].

        assert (nd_pf1' :
                NoDup
                  (domain
                     ((b1, b2, ill, s1)
                        ::  removeEntry (b1, b2) g1))).
        eapply no_dup_cons_removeEntry...
        eapply no_dup_isMap in nd_pf1' as pf1'.
       assert (nd_pf''' :
                NoDup
                  (domain
                     ((b1, b2, ill, r4)
                        :: removeEntry (b1, b2) g3))).
       eapply no_dup_cons_removeEntry...
      eapply no_dup_isMap in nd_pf''' as pf'''.
     
      move IHLTS2 at bottom.
      assert (IN4: In (a1, a2, vis, Chan un io t0) g4).
       inversion TYP4. subst. assert (IN4 := H4); clear H4 TYP4.
     eapply typeCheck_lts_in with (pf1 := pf4) in LTS2 as IN4a.
     destruct IN4a as [mm [tt [ABS | TYP4a]]].
     inversion ABS; subst.
      eapply tsuper_payload with (pf1 := pf4) in IN1a as K.
      destruct K as [pp1 TYP4]; inversion TYP4; subst.
      assert (EQ: Chan mm inp tt = Chan un pp1 t0).
      eapply type_of_map with (g := g4)...
      inversion EQ. subst. 
      eapply typeCheck_lts_out with (pf1 := pf3) in LTS1 as IN3a.
      destruct IN3a as [mm [ttt [ABS1 | ABS1]]].
      eapply tsuper_payload with (pf1 := pf3) in IN1a as K.
      destruct K as [pp1 TYP3]; inversion TYP3; subst.
      assert (EQ2: Chan mm out ttt = Chan un pp1 t0).
      eapply type_of_map with (g := g3)...
      inversion EQ2; subst.
      assert (ABS2: out = inp /\ inp = io).
      eapply split_plus_un with (pf1 := pf3) (pf2 := pf4)(pf3 := pf1) (b1 := a1) (b2 := a2)...
      destruct ABS2; discriminate.
      eauto.
       eapply tsuper_payload with (pf1 := pf3) in IN1a as K.
      destruct K as [pp1 TYP3]; inversion TYP3; subst.
      assert (EQ2: Chan mm io ttt = Chan un pp1 t0).
      eapply type_of_map with (g := g3)...
      inversion EQ2; subst.
      assert (ABS2: io = inp /\ inp = io).
      eapply split_plus_un with (pf1 := pf3) (pf2 := pf4)(pf3 := pf1) (b1 := a1) (b2 := a2)...
      destruct ABS2; discriminate.
      eauto. eauto. eapply split_comm...
     inversion TYP4a. subst. assert (IN4a := H4); clear H4 TYP4a.
     assert (EQ: f1 = vis /\ mm = un /\ tt = t0).
     eapply tsuper_payload with (pf1 := pf4) in IN1a as K.
     destruct K as [pp1 TYP4]; inversion TYP4; subst.
     eapply fsuper_vis with (pf1 := pf4) in IN1a as [K _].
     inversion K; subst.
     assert (f1 = vis). eapply flag_of_map with (g := g4)...
     assert (EQ: Chan mm io tt =  Chan un pp1 t0). eapply type_of_map with (g := g4)...
     inversion EQ;  intuition.
     eapply split_comm... eapply split_comm...
     destruct EQ as [EQ1 [EQ2 EQ3]]; subst...
     eauto.

     inversion TYP4. subst g5 n t.
     assert (f0 = ill).
     eapply fsuper_hid with (pf2 := pf4) (pf1 := pf3) in IN1b as [[K1 K2] | [K1 K2]].
     eapply flag_of_map with (g := g4)...
     assert (hid = ill).
     eapply flag_of_map with (g := g3)...
     discriminate.
     eauto.
     subst f0.

     assert (TSO : exists k'' pfk'', tEnv_split g4 k'' g' pf4 pfk'' pf_Inp).
     destruct tt4. destruct m. 
     (* m = lin *)
     assert (nd_pf'':
                NoDup
                  (domain
                     ((b1, b2, ill, Chan lin empty tt4)
                        :: removeEntry (b1, b2) g2))).
       eapply no_dup_cons_removeEntry...
       eapply no_dup_isMap in nd_pf'' as pf''.
     
     eapply split_of_split with
         (pf1 := pf1')  (pf2 := pf'') (pfw0 := pf''').
     eapply no_dup_cons_removeEntry...
     
      inversion TP4'; subst.
     eapply split_new_un_lin.
     eauto. eapply split_comm...
     eauto. eauto. eauto. 
     eauto. eauto.
      inversion TP4'; subst. subst g'.
     eapply tEnv_split_add_fp.
     eauto. eauto. eauto. intros ABS; eapply not_lin_is_unrestricted in ABS; intuition.
     eauto.
     (* m = un*)
     assert (EQ: s1 = s /\ s = Chan un p tt4).
      inversion H. destruct H9.
      eapply tsub_un with (pf := pf1) in H4 as K1. inversion K1; subst.
       eapply tsub_un with (pf := pf) in  H11 as K2. inversion K2; subst.
       assert (s = Chan un p tt4).
       eapply type_of_map with (g := g)...
       assert (s1 = Chan un p tt4).
       subst; assert (is_unrestricted (Chan un p tt4)). eapply un_is_unrestricted. intuition.
       subst... eauto. eapply split_comm...
       destruct EQ; subst.
       assert (r4 = Chan un p tt4).
       eapply ISUN4', un_is_unrestricted...
       subst.
     
      assert (nd_pf'':
                NoDup
                  (domain
                     ((b1, b2, ill, Chan un p tt4)
                        :: removeEntry (b1, b2) g2))).
       eapply no_dup_cons_removeEntry...
       eapply no_dup_isMap in nd_pf'' as pf''.
     
     eapply split_of_split with
         (pf1 := pf1')  (pf2 := pf'') (pfw0 := pf''').
     eapply no_dup_cons_removeEntry...
     eapply split_new_un_un with (a1 :=a1) (a2 := a2);
       try eassumption.
     eapply split_comm... 
     eauto.
     subst g';
       eapply tEnv_split_add_fp...
     (* typeOf g4 (b1, b2) Top *)
     inversion TP4'; subst.
      assert (nd_pf'':
                NoDup
                  (domain
                     ((b1, b2, ill, Top)
                        :: removeEntry (b1, b2) g2))).
       eapply no_dup_cons_removeEntry...
       eapply no_dup_isMap in nd_pf'' as pf''.
     eapply split_of_split with
         (pf1 := pf1')  (pf2 := pf'') (pfw0 := pf''').
     eapply no_dup_cons_removeEntry...
     eapply split_new_un_top; try eassumption.
     eapply split_comm...
     eauto.
     subst g';
       eapply tEnv_split_add_fp...

      
     destruct TSO as [k'' [pfk'' TSK'']].
     revert dependent pfk1.
     rewrite K1EQ.
     intros.
     move TC1 at bottom.
     assert (K4IN:
               exists k4 : typeEnv, lts g4 q1 (aIn a1 a2 b1 b2) k4 q2 nd_pf4).
     eapply split_lts_exists_lts with (pf := pf_Inp)...
     destruct K4IN as [k4 K4IN].
     eapply lts_un_input_action with (r := s04) in K4IN as K4EQ.
     destruct K4EQ as (ne4 &DIS4 &K4EQ).
     
     
     assert (nd_pfk4: NoDup(domain k4)).
      eapply lts_un_input_action_newEntries with (k := ne4) (pf := nd_pf4) in K4IN as K.
     destruct K as [NE4NIL | NE4REPL].
     subst; eapply no_dup_cons_removeEntry...
     destruct NE4REPL as (q & REPL &INCL &NE4REPL).
     subst ne4 k4.
     rewrite domain_distr; eapply distr_no_dup.
     eapply newEntries_no_dup.
     eapply wf_rewrite,prop27,incl_incl2.
     eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf4)...
     eauto.
     eapply incl_tran with (m := secLabs q1)...
     eapply typeCheck_no_dup with (pf := pf4)...
     eauto.
     eapply no_dup_cons_removeEntry...
     eapply disjoint_commute, disjoint_iff with (l1 := domain g4).  eapply new_entries_disjoint.
     unfold sl_pos, pos in *; intros.
     specialize SLP with x1 x2;
       unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INCL; specialize INCL with (x1,x2); intuition.
     assert (MAX: max(domain g1) >= max (secLabs q)).
     eapply incl_preserves_max, incl_tran with (m := secLabs q1)...
     assert(  incl (secLabs q1) (domain g4)).
     eapply typeCheck_no_dup with (pf := pf4)...
     eapply incl_iff with (m1 := domain g4);
       try eassumption.
     eapply split_domain_l_2,split_comm...
     erewrite split_max with (pf := pf1). lia.
     eapply split_comm...
     eapply in_removeEntry_cons_iff,in_g_in_domain...
     eauto.
     eauto.

     eapply disjoint_commute,disjoint_iff...
     eapply disjoint_commute...
     eapply sl_pos_par_r...
     eapply typeCheck_no_dup with (pf := pf4)...
     
     eapply no_dup_isMap in nd_pfk4 as pfk4.
     specialize IHLTS2 with (pfk1 := pfk4).
     move IHLTS2 at bottom.
     assert (sl_pos q1). eapply sl_pos_par_r...
     eapply IHLTS2 with (nd_pf1 := nd_pf4) (pf2 := pfk'') in H5.
     assert (TC2 := H5); clear H5 IHLTS2.
      
     revert dependent nd_pf'0.
     subst g8.
     remember ((b1, b2, ill, s2) :: removeEntry (b1, b2) g1) as g4'.
     intros.
     remember  nd_pf'0 as nd_pf4'. 
     subst nd_pf'0.

      assert (DOMEQ:
                 forall x : name * name, In x (domain g4') <-> In x (domain g4)).
        subst g4'.
       assert (IFF1: forall x : name * name,
                  In x (domain g1) <-> In x (domain ((b1, b2, ill, s2) :: removeEntry (b1, b2) g1))).
       eapply in_removeEntry_cons_iff, in_g_in_domain...
       assert (IFF2: forall x : name * name,
                  In x (domain g4) <-> In x (domain  g1)).
       intros; eapply split_domain_r...
       intros. specialize IFF1 with x; specialize IFF2 with x; intuition.
     
     assert (NE:
               ne = nil \/
               exists q,
                 replication q1 q2 q /\
                 incl (secLabs q) (secLabs q1) /\
                 ne = newEntries g4' (secLabs (dep_relabel q (domain g4') nd_pf4')) (max (domain g4'))).
     eapply lts_un_input_action_newEntries.
     eauto. tauto. subst g4'. econstructor.
     right. eapply removeEntry_in...

      eapply disjoint_commute,disjoint_iff.
     eapply disjoint_commute...
     intros. rewrite <- in_removeEntry_cons_iff;
       try tauto; try subst g4'...
     eapply sl_pos_par_r...
     eapply typeCheck_no_dup with (pf := pf4)...
     
     assert (NE1:
               ne4 = nil \/
               exists q,
                 replication q1 q2 q /\
                 incl (secLabs q) (secLabs q1) /\
                 ne4 = newEntries g4 (secLabs (dep_relabel q (domain g4) nd_pf4)) (max (domain g4))).
     eapply lts_un_input_action_newEntries.
     eauto. eauto. subst g4'...

       eapply disjoint_commute,disjoint_iff...
     eapply disjoint_commute...
     eapply sl_pos_par_r...
     eapply typeCheck_no_dup with (pf := pf4)...
   

     assert (TPP: type_plus s03 s04 s0).
       move TP4 at bottom.
       inversion TREM as [_ [TP0 _]]; inversion TREM3 as [_ [TP3 _]].
         assert (pp_emptyR: forall p r, pol_plus p empty r -> p =r). intros. inversion H5; destruct p, r...
         assert (pp_emptyL: forall p r, pol_plus empty p r -> p =r). intros. inversion H5; destruct p, r...
       destruct t0. destruct m. destruct p.
       try inversion TP4; subst; eapply pp_emptyR in H12; subst; inversion TP3; inversion H10; subst; eapply pp_emptyL in H12; subst...
       try inversion TP3; subst; inversion H12;  subst; inversion TP4;  inversion TP0; subst; inversion H13; subst; inversion H16; subst; inversion H20; subst...
       try inversion TP3; subst; inversion H12;  subst; inversion TP4;  inversion TP0; subst; inversion H13; subst; inversion H16; subst; inversion H20; subst...
       try inversion TP3; subst; inversion H12;  subst; inversion TP4;  inversion TP0; subst; inversion H13; subst; inversion H16; subst; inversion H20; subst...
       assert (PDS: forall p5 p0 p, pol_cup p5 (pol_cup p0 p) = pol_cup (pol_cup p p5) p0).
       intros a b c. destruct a,b,c...
       try inversion TP4; inversion TP0; subst; try discriminate; inversion H13;  subst; inversion TP3; subst;
        erewrite <-PDS...
       try inversion TP4; inversion TP0; subst; try discriminate; inversion TP3; subst...

      
     destruct NE, NE1.
     
     (* NON REPLICATED INPUT *)
     **** subst ne ne4.
     remember (b1, b2) as b.
      assert (nd_pfn : NoDup (domain (((b, vis, s0) :: removeEntry b (((b, hid, s0) :: removeEntry b (nil ++ (b, vis, s0) :: removeEntry b g4'))))))).
       eapply no_dup_cons_removeEntry,no_dup_cons_removeEntry,no_dup_cons_removeEntry...
       eapply no_dup_isMap in nd_pfn as pfn.
       assert (EQ1: fst b = b1). subst...
       assert (EQ2: snd b = b2). subst...
       rewrite <-EQ1, <-EQ2.
       eapply TNew with  (pf1 := pfn).
       eauto.
       revert dependent nd_pfn.
       revert dependent pfn.
       subst b.
       unfold removeEntry; fold removeEntry.
       rewrite pairEq_eq_true.
       assert (EQ: (nil ++ (b1, b2, vis, s0) :: removeEntry (b1, b2) g4' =  (b1, b2, vis, s0) :: removeEntry (b1, b2) g4')). eauto.
       rewrite EQ. unfold removeEntry; fold removeEntry.
       rewrite pairEq_eq_true.
       subst g4'.
       unfold removeEntry; fold removeEntry.
       rewrite pairEq_eq_true. intros.
       eapply TPar with (pf1 := pfk3) (pf2 := pfk4).
       subst k4.
       eapply tEnv_split_add_vis...
       eauto. eauto.
     **** 
       destruct H9 as [q [REPL [INCL NE4EQ]]].
       assert (NEEQ: ne = newEntries g4' (secLabs (dep_relabel q (domain g4') nd_pf4')) (max (domain g4'))).
       eapply lts_un_input_action_newEntries_2...
       eapply typeCheck_no_dup with (pf := pf4)...

       eapply disjoint_commute,disjoint_iff.
     eapply disjoint_commute...
     intros. rewrite <- in_removeEntry_cons_iff;
       try tauto; try subst g4'...
      
       erewrite identif_seclabs_of_dep_relabel in NEEQ.
       assert (MAX: max (domain g4') = max (domain (g4))).
       eapply max_same_domain...
       erewrite MAX,<-identif_seclabs_of_dep_relabel in NEEQ.
       assert (NENIL: ne4 = nil).
       subst ne4; eapply newEntries_nil with (g := g4')...
       subst...

       subst ne. remember (b1, b2) as b.
      assert (nd_pfn : NoDup (domain (((b, vis, s0) :: removeEntry b (((b, hid, s0) :: removeEntry b (nil ++ (b, vis, s0) :: removeEntry b g4'))))))).
       eapply no_dup_cons_removeEntry,no_dup_cons_removeEntry,no_dup_cons_removeEntry...
       eapply no_dup_isMap in nd_pfn as pfn.
       assert (EQ1: fst b = b1). subst...
       assert (EQ2: snd b = b2). subst...
       rewrite <-EQ1, <-EQ2.
       eapply TNew with  (pf1 := pfn).
       eauto.
       revert dependent nd_pfn.
       revert dependent pfn.
       subst b.
       unfold removeEntry; fold removeEntry.
       rewrite pairEq_eq_true.
       assert (EQ: (nil ++ (b1, b2, vis, s0) :: removeEntry (b1, b2) g4' =  (b1, b2, vis, s0) :: removeEntry (b1, b2) g4')). eauto.
       rewrite EQ. unfold removeEntry; fold removeEntry.
       rewrite pairEq_eq_true.
       subst g4'.
       unfold removeEntry; fold removeEntry.
       rewrite pairEq_eq_true. intros.
       
       eapply TPar with (pf1 := pfk3) (pf2 := pfk4).
       subst. revert dependent pfk4. rewrite NENIL. intros.
       revert dependent pfk1.
       unfold removeEntry. fold removeEntry.
       rewrite pairEq_eq_true. intros.
       eapply tEnv_split_add_vis...
       eauto. eauto.

     ****

       destruct H5 as [q [REPL [INCL NE4EQ]]].
       assert (NEEQ: ne4 = newEntries g4 (secLabs (dep_relabel q (domain g4) nd_pf4)) (max (domain g4))).
       eapply lts_un_input_action_newEntries_2...
       eapply typeCheck_no_dup with (pf := pf4)...
          eapply disjoint_commute,disjoint_iff.
     eapply disjoint_commute...
     intros. rewrite <- in_removeEntry_cons_iff;
       try tauto; try subst g4'...
       
       
       erewrite identif_seclabs_of_dep_relabel in NEEQ.
       assert (MAX: max (domain g4') = max (domain (g4))).
       eapply max_same_domain...
       erewrite <-MAX in NEEQ.
       erewrite <-identif_seclabs_of_dep_relabel with (pf := nd_pf4')in NEEQ.
       assert (NENIL: ne = nil).
       subst ne; eapply newEntries_nil with (g := g4).
       eauto.
       eauto. subst...

       revert dependent pfk1.
       rewrite NENIL. intros.
       remember (b1, b2) as b.
       assert (nd_pfn : NoDup (domain (((b, vis, s0) :: removeEntry b (((b, hid, s0) :: removeEntry b ((b, vis, s0) :: removeEntry b g4'))))))).
       eapply no_dup_cons_removeEntry,no_dup_cons_removeEntry, no_dup_cons_removeEntry...
       eapply no_dup_isMap in nd_pfn as pfn.
       assert (EQ1: fst b = b1). subst...
       assert (EQ2: snd b = b2). subst...
       rewrite <-EQ1, <-EQ2.
       eapply TNew with  (pf1 := pfn).
       eauto.
       revert dependent nd_pfn.
       revert dependent pfn.
       subst b.
       unfold removeEntry; fold removeEntry.
       rewrite pairEq_eq_true.
       subst g4'.
       unfold removeEntry; fold removeEntry.
       rewrite pairEq_eq_true. intros.
       
       eapply TPar with (pf1 := pfk3) (pf2 := pfk4).
       subst. 
       revert dependent pfk1.
       unfold removeEntry. fold removeEntry.
       rewrite pairEq_eq_true. intros.
       eapply tEnv_split_add_vis...
       eauto. eauto.
       
       (* REPLICATED INPUT *)
     ****
       destruct H5 as  [rp' [RP' [INRP' EQNE']]].
       destruct H9 as  [rp [RP [INRP EQNE4]]].
       assert (rp = rp').
       eapply replication_unique...
       subst rp'. clear RP'.
       revert dependent pfk4. rewrite K4EQ. intros.
       move Heqg4' at bottom.
       revert dependent pfk1.
       rewrite Heqg4'.
       unfold removeEntry; fold removeEntry; rewrite pairEq_eq_true. intros.

        remember ( newEntries g3 (secLabs (dep_relabel rp (domain g3) nd_pf3)) (max (domain g3))) as ne3.
       remember ( newEntries g1 (secLabs (dep_relabel rp (domain g1) nd_pf1)) (max (domain g1))) as ne1.
       assert (nd_pfne4: NoDup(domain ne4)).
       subst. eapply newEntries_no_dup...
       eapply wf_rewrite,prop27,incl_incl2.
       eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf4)...
       eauto.
       eapply incl_tran with (m := secLabs q1)...
       eapply typeCheck_no_dup with (pf := pf4)...
       assert (nd_pfne3: NoDup(domain ne3)).
       subst. eapply newEntries_no_dup...
       eapply wf_rewrite,prop27,incl_incl2.
       eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf4)...
       eauto.
       eapply incl_tran with (m := secLabs q1)...
       assert ( incl (secLabs q1) (domain g4)).
       eapply typeCheck_no_dup with (pf := pf4)...
       eapply incl_iff with (m1 := domain g4);
         try eassumption.
       intros; eapply split_domain_m.
       eapply split_comm...
       assert (nd_pfne1: NoDup(domain ne1)).
       subst. eapply newEntries_no_dup...
       eapply wf_rewrite,prop27,incl_incl2.
       eapply replication_no_dup;eauto; eapply typeCheck_no_dup with (pf := pf4)...
       eauto.
       eapply incl_tran with (m := secLabs q1)...
       assert ( incl (secLabs q1) (domain g4)).
       eapply typeCheck_no_dup with (pf := pf4)...
       eapply incl_iff with (m1 := domain g4);
         try eassumption.
       intros; eapply split_domain_r...
       eapply no_dup_isMap in nd_pfne4 as pfne4.
       eapply no_dup_isMap in nd_pfne3 as pfne3.
       eapply no_dup_isMap in nd_pfne1 as pfne1.
       
       assert (ne1 = ne).
       subst.
       assert (MAX: (max (domain g1) = max (domain ((b1, b2, ill, s2) :: removeEntry (b1, b2) g1)))).
       eapply max_same_domain,in_removeEntry_cons_iff,in_g_in_domain...
       erewrite identif_seclabs_of_dep_relabel, identif_seclabs_of_dep_relabel,<-MAX,<-identif_seclabs_of_dep_relabel.
       eapply newEntries_removeEntry.
       eauto.
        assert (SLPQ1: sl_pos q1). 
      eapply sl_pos_par_l in SLP...
      unfold sl_pos,pos; intros.
      move INRP at bottom.
      unfold incl in INRP; specialize INRP with (x1, x2).
      apply INRP in H5; unfold sl_pos, pos in SLPQ1;
        specialize SLPQ1  with x1 x2...
       intros ABS. unfold incl in INRP; specialize INRP with (b1, b2); eapply INRP in ABS.
       assert (ABS2: exists t, In (b1, b2, hid, t ) g4).
       eapply typeCheck_hid...
       destruct ABS2 as [tt ABS2].
       assert (hid = ill).
       eapply flag_of_map with (g := g4)...
       discriminate.
       subst ne.

       remember (b1, b2) as b.
       remember ((b, hid, s0)
                   :: removeEntry b (ne1 ++ (b, vis, s0) :: removeEntry b g1)) as gnu.
       assert (nd_pfneapp: NoDup(domain (ne1 ++ (b, vis, s0) :: removeEntry b g1))).
        erewrite domain_distr.
       eapply distr_no_dup.
       eauto.
       eapply no_dup_cons_removeEntry.
       eauto. 
       subst ne1. eapply disjoint_commute.
       eapply disjoint_iff with (l1 := domain g1).
       eapply new_entries_disjoint.
        unfold sl_pos, pos in *; intros.
        specialize SLP with x1 x2;
                   unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INRP; specialize INRP with (x1,x2); intuition.
        assert (MAX: max(domain g1) >= max (secLabs rp)).
        eapply incl_preserves_max, incl_tran with (m := secLabs q1)... assert(  incl (secLabs q1) (domain g4)).
        eapply typeCheck_no_dup with (pf := pf4)...
        eapply incl_iff with (m1 := domain g4);
          try eassumption.
        eapply split_domain_l_2, split_comm...
        lia.
        subst b; eapply in_removeEntry_cons_iff...
         assert (nd_pfgnu : NoDup (domain gnu)).
       subst gnu.
       eapply no_dup_cons_removeEntry...
        assert (nd_pfn : NoDup (domain ((b, vis, s0) :: removeEntry b gnu))).
        eapply no_dup_cons_removeEntry...       
        eapply no_dup_isMap in nd_pfn as pfn.

        
       assert (EQ1: fst b = b1). subst...
       assert (EQ2: snd b = b2). subst...
       rewrite <-EQ1, <-EQ2.
       revert dependent pfk1.
       rewrite <-H5, <-Heqgnu.
       intros.
       eapply TNew with  (pf1 := pfn).
       subst...

       
      
       
       assert (TSNE: tEnv_split ne3 ne4 ne1 pfne3 pfne4 pfne1).
       subst. eapply split_newEntries...
       
       subst b.
       assert (nd_pfnek3:
                           NoDup
                             (domain
                                (ne3 ++
                                     ((b1, b2, vis, s03)
                                        :: removeEntry (b1, b2) g3)))).
        erewrite domain_distr, no_dup_iff.
        split. assumption.
        split. eapply no_dup_cons_removeEntry...
        erewrite disjoint_commute. subst ne3.
        assert (DIS: disjoint (domain g3)
    (domain
       (newEntries g3 (secLabs (dep_relabel rp (domain g3) nd_pf3))
          (max (domain g3))))).
        eapply new_entries_disjoint.
        unfold sl_pos, pos in *; intros.
        specialize SLP with x1 x2;
                   unfold secLabs in SLP; fold secLabs in SLP; move SLP at bottom; unfold incl in INRP; specialize INRP with (x1,x2); intuition.
        assert (MAX: max(domain g3) >= max (secLabs rp)).
        eapply incl_preserves_max, incl_tran with (m := secLabs q1)... assert(  incl (secLabs q1) (domain g4)).
        eapply typeCheck_no_dup with (pf := pf4)...
        eapply incl_iff with (m1 := domain g4);
          try eassumption.
        intros; eapply split_domain_m,split_comm... 
        lia.
        eapply disjoint_iff with (l1  := domain g3),in_removeEntry_cons_iff,in_g_in_domain... 
        eapply no_dup_isMap in nd_pfnek3 as pfnek3.

        assert (TC' :
                  typeCheck ( ne3 ++ (b1, b2, vis, s03) :: removeEntry (b1, b2) g3) pfnek3 p2).
        eapply typeCheck_weak2 with (pfk := pfne3).
        erewrite <-domain_distr...
        eauto. 
        (* cons ne3 pfne3 *)
        assert (INVNE: forall c1 c2 ff tt,
                   In (c1, c2, ff, tt) ne3 ->
                   In (c1, c2 - max (domain g3)) (secLabs rp) /\ In (c1, c2 - max (domain g3), ff, tt) g3).
        intros.
        eapply inverse_newEntries.
        eauto.
          (* sl_pos rp *)
          unfold sl_pos in SL2;
          unfold sl_pos.
        eapply incl_pos with (l2 :=(secLabs q1))...
        (* incl (secLabs rp) (domain g3) *)
        eapply incl_tran with (m := secLabs q1).
        assumption.
        eapply incl_iff with (m1 := domain g4).
        eapply typeCheck_no_dup with (pf := pf4)...
        intros. eapply split_domain_m,split_comm...
        (*In (c1, c2, ff, tt)
    (newEntries g3
       (map (fun x : name * name => (fst x, snd x + max (domain g3))) (secLabs rp))
       (max (domain g3)))*)
        subst. erewrite <-identif_seclabs_of_dep_relabel...
        eapply cons_char.
        destruct ne3. left...
        right. intros.
        specialize INVNE with c1 c2 ff tt.
        apply INVNE in H9; clear INVNE.
        destruct H9 as [INSL IN3'].
        remember (c2 - max (domain g3)) as c''.
        assert (ff = ill).
        assert (IN1: In (c1, c'') (secLabs q1)).
        eapply INRP...
        assert (NOTINSL: ~In (c1, c'') (secLabs p1)).
        intros ABS.
        assert (ND: NoDup (secLabs (dPar p1 q1))).
        eapply typeCheck_no_dup with (pf := pf1)...
        unfold secLabs in ND. fold secLabs in ND.
        erewrite no_dup_iff in ND; destruct ND as [ND1 [ND2 DIS]].
        eapply disjoint_absurd...
        assert (NOTINFN: ~ In (c1, c'') (fn p1)).
        intros ABS.
        assert (DIS: disjoint (fn (dPar p1 q1)) (secLabs (dPar p1 q1))).
        eapply fn_disjoint_sl with (pf := pf1)...
        unfold fn, secLabs in DIS;
          fold fn in DIS; fold secLabs  in DIS.
        eapply disjoint_absurd with (x:= (c1, c'')) (l := (fn p1 ++ fn q1)) (m := (secLabs q1 ++ secLabs p1)).
        eauto. eapply in_app_iff; left...
        eapply in_app_iff; left...
        assert (IN0: exists tt, In (c1, c'', hid, tt) g4).
        eapply typeCheck_hid...
        destruct IN0 as [ttt F0].
        assert (F1: In (c1, c'') (domain g1)).
        eapply split_domain_l_2 with (x := (c1, c'')) in H6 as K.  eapply in_g_in_domain in IN3' as K1; eapply K in K1...
        eapply in_domain_in_g in F1.
        destruct F1 as [f1 [tt1 F1]].
        assert (FP: exists f3, flagOf g3 (c1, c'') f3 /\ flag_plus hid f3 f1).
        eapply split_flag_plus with (pf1 := pf4) (pf2 := pf3) (pf := pf1), split_comm...
        destruct FP as [f3' [F3 FP]].
        assert (ff = f3').
        eapply flag_of_map with (g := g3) (x := (c1, c''))...
        subst ff.
        assert (F1': flagOf g1 (c1, c'')  hid).
        eapply fsub_hid,split_comm...
        inversion F1'. subst g5 n f0.
        assert (f1 = hid).
        eapply flag_of_map with (g := g1) (x := (c1, c''))...
        subst f1.
        inversion FP...

        subst.
        eapply typeCheck_ill with (p := p1)...

        subst ne3;
          rewrite identif_seclabs_of_dep_relabel in *;
          eapply Peirce; intros ABS;
          eapply not_disjoint in ABS as ([x1 x2] &ABS1 &ABS2);
          eapply in_bv_lt_max with (pf := pfk3) in ABS1;
          eapply in_domain_in_g in ABS2 as (ff &tt &ABS2);
          eapply newEntries_gte_max in ABS2;
          try lia;
          try eassumption.
        rewrite max_same_domain with (l := domain g3) in ABS1;
          try lia.
        intros. rewrite <-in_removeEntry_cons_iff; try tauto.
        eauto.
        
        eapply TPar with
            (pf1 := pfnek3) (pf2 := pfk4).
                 (*  tEnv_split (ne3 ++ (b1, b2, vis, s03) :: removeEntry (b1, b2) g3)
    (ne4 ++ (b1, b2, vis, s04) :: removeEntry (b1, b2) g4)
    ((b1, b2, vis, s0) :: removeEntry (b1, b2) gnu) pfnek3 pfk4 pfn*)
        subst gnu.
        revert dependent pfn.
        unfold removeEntry; fold removeEntry.
        rewrite pairEq_eq_true.
        intros.
        
        revert dependent pfn.
        erewrite removeEntry_app. intros.

        eapply split_iff with
            (g := ne1 ++ (b1, b2, vis, s0) ::  removeEntry (b1, b2) g1).
        eauto.
        unfold domain; fold domain; eapply NoDup_cons.
        intros ABS. erewrite domain_distr,in_app_iff in ABS; destruct ABS as [ABS | ABS].
        erewrite domain_distr, no_dup_iff in nd_pfneapp.
        unfold domain in nd_pfneapp; fold domain in nd_pfneapp; destruct nd_pfneapp as [_ [_ ABS2]].
        eapply disjoint_r_cons in ABS2. intuition.
        eapply in_domain_in_g in ABS; destruct ABS as [ff [tt ABS]]; eapply no_dup_not_in_removeEntry in ABS...
        erewrite domain_distr, no_dup_iff in nd_pfneapp.
        move nd_pfneapp at bottom. destruct nd_pfneapp as [K1 [K2 K3]].
        erewrite domain_distr, no_dup_iff.
        split. assumption.
        split.  unfold domain in K2; fold domain in K2; inversion K2...
        eapply disjoint_r_cons in K3. intuition.

        eapply split_distr.
        eauto.
        eapply tEnv_split_add_vis...
        intuition. rewrite in_app_iff in H9; destruct H9 as [K1 | K2].
        right. eapply in_app_iff; left...
        inversion K2. inversion H9; subst...
        right. eapply in_app_iff; right...
        assert (EQ : (b1, b2, vis, s0) :: ne1 ++ removeEntry (b1, b2) g1 = ((b1, b2, vis, s0) :: ne1) ++ removeEntry (b1, b2) g1). intuition auto.
        rewrite EQ, in_app_iff with (l := (b1, b2, vis, s0) :: ne1) in H9; destruct H9 as [K1 | K2]; clear EQ.
        inversion K1.  inversion H9; subst. eapply in_app_iff; right...
        eapply in_app_iff; left...
        eapply in_app_iff; right. right...
        all:eauto.
     **** eauto.
     **** eauto.
     **** eauto.
     **** eauto.
     **** eauto.
     **** eauto.
     **** eauto.
     ****  try eapply incl_preserves_max, typeCheck_no_dup...
        *  subst g8. econstructor. right. eapply removeEntry_in...
        * eauto.
        * eapply type_plus_comm...
        * eauto.
        * subst g8.
          erewrite <-max_removeEntry_cons; try eassumption.
          erewrite <-split_max with (g := g1) (g1 := g4);
            try eassumption.
          try eapply incl_preserves_max, typeCheck_no_dup...
          eapply split_comm...
          eauto.
        * eauto.
        * eauto.
        * eauto.
        * eapply tsuper_payload with (pf1 := pf3) in IN1a as K.
          destruct K as [pp3 TYP3].
          inversion TYP3; subst.
          eapply fsuper_vis with (pf1 := pf3) in IN1a as K.
          destruct K as [FYP3 _].
          eapply tsub_un with (pf := pf1) in H4 .
          inversion TYP3; inversion FYP3; subst.
          assert (Chan un pp3 t0 = Chan un io t0).
          eapply type_of_map with (g := g1)...
          rewrite <-H9.
           assert (f1 = vis).
          eapply flag_of_map with (g := g3)...
          subst...
          all:eauto.
        * eauto.
        * eauto.
        * eapply typeCheck_no_dup with (pf := pf3)...
        * (*incl (secLabs p1) (domain (hid_proj g3))*)
          eapply typeCheck_hid_proj...

          
    - Case open.
      intros.
      inversion AFT; subst.
      assert (IN1b := H8).
      assert (LTSSUB := H9).
      assert (INb := H).
      remember pf0 as nd_pf. remember pf1 as nd_pfh. subst pf0 pf1. remember pf3 as pf1.
      remember pf5 as nd_pfh1. subst pf3 pf5.
      clear H H8 H9.
      inversion TYP. 
      erewrite surjective_pairing with (p := n),H,H0 in H1.
      revert dependent pf0.
      erewrite surjective_pairing with (p := n),H,H0.
      intros.
      assert (t0 = t1).
      eapply type_of_map with (g := g1)...
      subst t0.
      assert (TC1 := H3).
      remember pf0 as pf1'. subst pf0.
      clear H H0 H1 H2 H3.
      assert (nd_pf2: NoDup (domain g2)).
      eapply no_dup_split_no_dup_r...
      
      assert (IN2b: exists t2, In (b1, b2, ill, t2) g2).
      eapply fsuper_hid with (pf1 := pf1) (pf2 := pf2) in INb as [[K1 K2] | [ABS _]].
      inversion K2...
      assert (hid = ill). eapply flag_of_map with (g := g1)... discriminate. eauto.
      destruct IN2b as [t2 IN2b].
      
      assert (nd_pfh2 : NoDup (domain ((b1, b2, vis, t2) :: removeEntry (b1, b2) g2))).
      eapply no_dup_cons_removeEntry...
      eapply no_dup_isMap in nd_pfh2 as pfh2.
      eapply no_dup_isMap in nd_pfh1 as pfh1.
      eapply no_dup_isMap in nd_pfh as pfh.

      assert (TSH: tEnv_split ((b1, b2, vis, t1) :: removeEntry (b1, b2) g1) ((b1, b2, vis, t2) :: removeEntry (b1, b2) g2)
                         ((b1, b2, vis, t) :: removeEntry (b1, b2) g)
                         pfh1 pfh2 pfh).
      eapply tEnv_split_add_vis.
      eauto.
      assert (EXT: exists t2 : piType, typeOf g2 (b1, b2) t2 /\ type_plus t1 t2 t).
      eapply split_type_plus...
      destruct EXT as (t2' &TYP2b &TP2).
      assert (t2' = t2).
      eapply type_of_map with (g := g2)...
      subst...
      intros ISUN.
      destruct ISUN as (pp &tt &ISUN); subst t.
      eapply tsuper_payload with (pf1 := pf1) in INb as K.
      eapply tsuper_payload_r with (pf2 := pf2) in INb as K1.
      destruct K as (pp1 &TYPP1).
      destruct K1 as (pp2 &TYPP2).
      assert (t1 = Chan un pp1 tt).
      eapply type_of_map with (g := g1)...
      assert (t2 = Chan un pp2 tt).
      eapply type_of_map with (g := g2)...
      subst t1 t2.
      assert (pp1 = pp2 /\ pp2 = pp).
      eapply split_plus_un...
      destruct H; subst; split...
      eauto. eauto. eauto.
      
      specialize IHLTS with
          (pf := pfh) (pf2 := pfh2) (pf1 := pfh1) (pfk1 := pfk1) (nd_pf1 := nd_pfh1).
      eapply sl_pos_nu in SLP as K.
      eapply IHLTS in K...

      simpl in H8; intuition.

       
      - Case hide. 
        introv TC1 TS1 LTS1; assert (TC' := TC1);inv TC'.
        assert (TC := H5); clear H5.
        destruct n as [n1 n2]; simpl in *.
        assert (LTS' := LTS1). inv LTS'.
        + simpl in H; intuition.
        + assert (LTS' := H7). clear H7.
          assert (t0=t1).
          assert (PF := nd_pf1).
          rewrite domain_distr in PF;
            eapply no_dup_iff in PF as (ND1 &ND2 &DIS);
            simpl in *.
          assert (IN := H3).

          eapply in_app_iff in IN as [ABS1 | [EQ | ABS2]];
            try inv ABS1;
            try inv EQ;
            try inv ABS2;
            try tauto.
          try eapply disjoint_absurd...
          inv ND2.
          eapply in_g_in_domain in ABS2; try contradiction.
          subst t0.

         

          
          assert (LTS'' := LTS').
         (* assert (LTS_IFF: forall g1 p a k1 p' pf1 g2 pf2,
                   lts g1 p a k1 p' pf1 ->
                   (forall x, In x g1 <-> In x g2) ->
                    exists k2 ,
                      lts g2 p a k2 p' pf2 /\
                        (forall x, In x k1 <-> In x k2)).
          *)
          assert (SLP2 := SLP).
          eapply sl_pos_nu in SLP2.
          
          
          eapply lts_iff in LTS' as (k' &LTS' &LTSN &IFF1);
            try eassumption.
         
          assert (TP1:
                   exists t2 : piType, typeOf g2 (n1, n2) t2 /\ type_plus t1 t2 t).
          eapply split_type_plus with (g1 := (h0 ++ (n1, n2, hid, t1) :: h3)) (g := (h1 ++ (n1, n2, hid, t) :: h2))...
          econstructor; eapply in_app_iff; right...

         

          destruct TP1 as (t2 &TYP2 &TP1).
          (*destruct FP1 as (f2 &FYP2 &FP1).*)
          
           assert (TC' := TC).
           eapply IHLTS in TC; try eassumption.
          

          eapply TNew with (n := (n1,n2)).
          eapply in_app_iff; right...

          assert (ND2: forall t1,
                   NoDup (domain ((n1, n2, vis, t1) :: removeEntry (n1, n2) (h0 ++ (n1, n2, hid, t1) :: h3)))).
          simpl; econstructor; try intros ABS;
            try eapply in_domain_in_g in ABS as (ff &tt &ABS).
          assert (~ In (n1, n2, ff, tt) (removeEntry (n1, n2) (h0 ++ (n1, n2, hid, t0) :: h3))).
          eapply no_dup_not_in_removeEntry.
          assert (pf7 := pf6).
          rewrite domain_distr in *; simpl in *...
          contradiction.
          eapply no_dup_removeEntry_no_dup.
          assert (pf7 := pf6).
          rewrite domain_distr in *; simpl in *...

          eapply typeCheck_no_dup with (pf := pf4)
            in TC' as (INCL &ND).

          
          assert (ND3:  NoDup
    (domain ((n1, n2, vis, t'0) :: removeEntry (n1, n2) (h'0 ++ (n1, n2, hid, t'0) :: h''0)))).
          eapply lts_no_dup in LTS''.
          simpl; econstructor;try intros ABS;
            try eapply in_domain_in_g in ABS as (ff &tt &ABS).
          assert (~ In (n1, n2, ff, tt) (removeEntry (n1, n2) (h'0 ++ (n1, n2, hid, t'0) :: h''0))).
          eapply no_dup_not_in_removeEntry.
          assert (pf7 := pf6).
          rewrite domain_distr in *; simpl in *...
          contradiction.
          eapply no_dup_removeEntry_no_dup.
          assert (pf7 := pf6).
          rewrite domain_distr in *; simpl in *...
          eapply incl_incl2...
          simpl in *...
          (*incl (secLabs p) (domain (h0 ++ (n1, n2, vis, t1) :: h3))*)
          rewrite removeEntry_app_shift in INCL;
            simpl in INCL; try rewrite pairEq_eq_true,domain_distr in INCL; try rewrite domain_distr; simpl.
          eapply incl_iff; try eassumption.
          eapply Permutation_iff, Permutation.Permutation_middle.
          intros ABS.
            assert (PF := nd_pf1).
          rewrite domain_distr in PF.
            try eapply no_dup_iff in PF as (NDA &NDB &DISS);
            simpl in *.
          try eapply disjoint_absurd...
          eauto.
          eauto.
          eapply incl_preserves_max...
           (*incl (secLabs p) (domain (h0 ++ (n1, n2, vis, t1) :: h3))*)
          rewrite removeEntry_app_shift in INCL;
            simpl in INCL; try rewrite pairEq_eq_true,domain_distr in INCL; try rewrite domain_distr; simpl.
          eapply incl_iff; try eassumption.
          eapply Permutation_iff, Permutation.Permutation_middle.
          intros ABS.
            assert (PF := nd_pf1).
          rewrite domain_distr in PF.
            try eapply no_dup_iff in PF as (NDA &NDB &DISS);
            simpl in *.
          try eapply disjoint_absurd...
          
          eapply typeCheck_impl with (g1 := k').
          eapply lts_no_dup; try eassumption.
          eapply incl_incl2...
          eapply incl_preserves_max...
          assumption.
          eauto.

          intros.
          rewrite <-IFF1.
          (*  In x (h'0 ++ (n1, n2, vis, t'0) :: h''0) <->
  In x ((n1, n2, vis, t'0) :: removeEntry (n1, n2) (h'0 ++ (n1, n2, hid, t'0) :: h''0)) *)
          rewrite removeEntry_app_shift;
            unfold removeEntry; fold removeEntry;
            try rewrite pairEq_eq_true.
          eapply Permutation_iff, Permutation.Permutation_sym, Permutation.Permutation_middle.
          intros ABS.
          erewrite removeEntry_app_shift2 in ND3;
            try eassumption.
          simpl in ND3. inv ND3.
            assert (In (n1, n2) (domain (removeEntry (n1, n2) h'0 ++ (n1, n2, hid, t'0) :: h''0))). 
            try rewrite domain_distr,in_app_iff; simpl; try right...
            contradiction.
            eauto.

          instantiate (3 := (n1, n2, vis, t2)
                              :: removeEntry (n1, n2) g2).
          eapply split_iff
            with (g := (n1, n2, vis, t)
                         :: removeEntry (n1, n2) (h1 ++ (n1, n2, hid, t) :: h2)). 
          eauto.
          eauto.
          eapply tEnv_split_add_vis.
          eauto.
          eauto.
          introv (q &t'' &ISUN); subst t;
            inv TP1.
          assert (EQ2: p1 = p2 /\ p2 = pol_cup p1 p2).
          inv TYP2; eapply split_plus_un with (pf1 := pf3) (pf2 := pf2) (pf3 := pf)...
          eapply in_app_iff; right...
          destruct EQ2 as[EQ1 EQ2]; subst; rewrite <-EQ2; intuition.
          eauto.

          (*forall x : name * name * flag * piType,
  In x ((n1, n2, vis, t) :: removeEntry (n1, n2) (h1 ++ (n1, n2, hid, t) :: h2)) <->
  In x (h1 ++ (n1, n2, vis, t) :: h2)*)
          rewrite removeEntry_app_shift;
            unfold removeEntry; fold removeEntry;
            try rewrite pairEq_eq_true.
          eapply Permutation_iff, Permutation.Permutation_middle.
          intros ABS.
          assert (ND3 := pf0).
          rewrite domain_distr in ND3;
            eapply no_dup_iff in ND3 as (_&_&DIS);
            simpl in DIS;
            try eapply disjoint_absurd...


          eapply lts_no_dup; try eassumption.
          eapply incl_incl2; try eassumption.
          inv TC1.
          eapply typeCheck_no_dup with (pf := pf5)...
          eapply incl_iff with (m1  := domain (((n1, n2, vis, t1) :: removeEntry (n1, n2) (h0 ++ (n1, n2, hid, t1) :: h3)))).
          eapply typeCheck_no_dup with (pf := pf4)...
          intros.
          assert (DOMEQ: domain (h0 ++ (n1, n2, vis, t1) :: h3) =
                           domain (h0 ++ (n1, n2, hid, t1) :: h3)).
          repeat rewrite domain_distr; simpl...
          rewrite DOMEQ.
          rewrite <-in_removeEntry_cons_iff.
          tauto.
          eauto.
          rewrite domain_distr,in_app_iff;simpl...
           eapply typeCheck_no_dup with (pf := pf4)...
           eapply incl_preserves_max.
           assert (DOMEQ: domain (h0 ++ (n1, n2, vis, t1) :: h3) =
                           domain (h0 ++ (n1, n2, hid, t1) :: h3)).
          repeat rewrite domain_distr; simpl...
          rewrite DOMEQ.
           eapply incl_iff with (m1  := domain (((n1, n2, vis, t1) :: removeEntry (n1, n2) (h0 ++ (n1, n2, hid, t1) :: h3)))).
          eapply typeCheck_no_dup with (pf := pf4)...
          intros.
          rewrite <-in_removeEntry_cons_iff.
          tauto.
          eauto.
           rewrite domain_distr,in_app_iff;simpl...
          
          rewrite removeEntry_app_shift;
            unfold removeEntry; fold removeEntry;
            try rewrite pairEq_eq_true;
            repeat rewrite in_app_iff.
          eapply Permutation_iff,Permutation.Permutation_sym.
          eapply Permutation.Permutation_middle.
          
          intros ABS. assert (PF := pf6).
          rewrite domain_distr,no_dup_iff in PF;
            destruct PF as (_ &_&DIS).
          try eapply disjoint_absurd...

          eapply typeCheck_no_dup with (pf := pf4)...

           eapply incl_iff with (m1  := domain (((n1, n2, vis, t1) :: removeEntry (n1, n2) (h0 ++ (n1, n2, hid, t1) :: h3)))).
          eapply typeCheck_no_dup with (pf := pf4)...
          intros.
          rewrite <-in_removeEntry_cons_iff.
          repeat rewrite domain_distr; simpl...
          tauto.
          eauto.
          rewrite domain_distr,in_app_iff;simpl...
          
           eapply incl_preserves_max.
           assert (DOMEQ: domain (h0 ++ (n1, n2, vis, t1) :: h3) =
                           domain (h0 ++ (n1, n2, hid, t1) :: h3)).
          repeat rewrite domain_distr; simpl...
          rewrite DOMEQ.
           eapply incl_iff with (m1  := domain (((n1, n2, vis, t1) :: removeEntry (n1, n2) (h0 ++ (n1, n2, hid, t1) :: h3)))).
          eapply typeCheck_no_dup with (pf := pf4)...
          intros.

           intros.
           rewrite <-in_removeEntry_cons_iff.
           tauto.
           eauto.
           rewrite domain_distr,in_app_iff;simpl...

       
          Unshelve.
      
      
      
      
      eauto. eauto. eauto. eauto. eauto. eauto. eauto.

      (* MATCHING REMAINING GOALS *)

      
      
      all: 
        try match goal with
      | [ PF : isMap (?g ++ ?h) |- isMap ?g]
          =>
          assert (PF2 := PF);
          eapply isMap_distr in PF2 as [K _];
          try eassumption
      | [ PF : isMap (?g ++ ?h) |- isMap ?h] =>
        assert (PF2 := PF);
            eapply isMap_distr in PF2 as [_ K];
        try eassumption
          | [ _ : _ |-  NoDup (domain (ill_proj _))] =>
              eapply no_dup_ill_proj;
            try eassumption
      | [_ : _ |- NoDup (domain _)] =>
        eauto
      | [ _ : _ |-
            isMap ((?b1, ?b2, _, _) :: removeEntry (?b1, ?b2) _)] =>
          eapply no_dup_split_no_dup.cons_removeEntry;
          try eassumption
     | [ _ : _ |-
          isMap (vis_proj ((?b1, ?b2, _, _) :: removeEntry (?b1, ?b2) _))] =>
         eapply isMap_vis_proj_removeEntry;
         try eassumption
     | [ _ : _ |-
          isMap (ill_proj ((?b1, ?b2, _, _) :: removeEntry (?b1, ?b2) _))] =>
         eapply isMap_illProj_removeEntry;
         try eassumption
     | [ _ : _ |- isMap (illECast _)] =>
        eapply no_dup_isMap;
          erewrite illEC_eq_domain;
          try eassumption
     | [nd_pf : NoDup(domain ?k),
        keq : ?k = _ :: ?g |-
             isMap (vis_proj ?g ++ ill_proj ?g)]=>
        eapply no_dup_isMap;
        erewrite domain_distr;
        eapply distr_no_dup;
        try eapply no_dup_vis_proj;
        subst; assert(K:= nd_pf); inv K;
          try eapply disjoint_projections;
        try eassumption
      |[ _ : _ |- _ ]=>
                   try eassumption                      
          end.

      eapply no_dup_ill_proj;
            try eassumption.
      eapply no_dup_isMap;
        erewrite removeEntry_shift; simpl in *...
      eauto.
      eauto.
      eauto.
      
      eapply no_dup_split_no_dup_r in TS1; try eassumption.
      inv TC1.
      assert (NDINCL:incl (secLabs p) (domain ((n, vis, t0) :: removeEntry n (h0 ++ (fst n, snd n, hid, t1) :: h3))) /\ NoDup (secLabs p)).
      eapply typeCheck_no_dup with (pf := pf5)...
      destruct NDINCL as (INCL &ND).
      assert (INCL2: incl (secLabs p) (domain h0 ++ (fst n, snd n) :: domain h3)).
       assert (PF := pf6).
      try rewrite domain_distr in *; simpl in *;
        try eassumption.
      destruct n as [n1 n2]; simpl in *.
      rewrite removeEntry_app_shift in INCL;
        simpl in INCL; try rewrite pairEq_eq_true,domain_distr in INCL.
      eapply incl_iff; try eassumption.
      eapply Permutation_iff, Permutation.Permutation_middle.
      intros ABS;
       try rewrite domain_distr in *; simpl in *;
        eapply no_dup_iff in PF as (PF1 &Pf2 &DIS);
        try eapply disjoint_absurd...
      eapply lts_no_dup in LTS'';
        rewrite domain_distr in *; simpl in *;
        try eassumption.
      eapply incl_incl2; try eassumption.
      assert (PF := pf6).
      try rewrite domain_distr in *; simpl in *;
        try eassumption.
      eapply incl_preserves_max...
      eapply no_dup_isMap...
   Qed.

      Theorem sr :
    forall g p a g' p' nd_pf pf pf',
      sl_pos p ->
      typeCheck g pf p ->  
      lts g p a g' p' nd_pf -> 
      typeCheck g' pf' p'.
  Proof.
    intros.
    assert (K := nd_pf).
    apply split_exists_neutral with g pf in K.
    destruct K as [neutral [pfn [nd_pfn TS]]].
    eapply sr_strong in H.
    all:eauto.
  Qed. 

  End SubjectReduction.
