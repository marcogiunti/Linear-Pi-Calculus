Require Import
  Bool List Omega PeanoNat Program.Equality Classical
  ListAddOns Max RemoveEntry Domain Replication
  pairEq
  sne_premises
  header
  operations pi_syntax 
  pairEq type_system
  semantics
  type_system_rules
  proposition27
  (*disjoint_newEntries
        type_operations_1
        no_dup_split_no_dup
        split_cons_remove*)
  split_not_exists
  tc_prelim
  split_operations_4
  split_existential
  type_operations_1
  substitution_prelim
  lts_payload_un_inp
  no_dup_split_no_dup
  disjoint_newEntries
  lts_no_dup
  type_checking_0
  type_checking_1
  split_cons_remove
  tc_dep_relabel_premises
  split_exists_neutral
  Permutation
  split_operations_2
  tc_premises_4.


Require Import CpdtTactics LibTactics.

Hint Constructors Permutation.

Hint Resolve in_removeEntry_cons_iff
  in_removeEntry_cons_iff_2.

Hint Constructors NoDup.
Hint Resolve in_hid_proj.
Hint Resolve isMap_not_in incl_cons inB_implies_In_2.
Hint Resolve in_g_in_domain.
Hint Resolve split_pf.
Hint Constructors tEnv_split.

(* github *)
Lemma Permutation_app_swap_app: forall A (l1 l2 l3: list A),
    Permutation (l1 ++ l2 ++ l3) (l2 ++ l1 ++ l3).
Proof.
  intros.
  rewrite 2 app_assoc.
  apply Permutation_app_tail, Permutation_app_comm.
Qed.

Lemma Permutation_iff {A} (l1 l2 : list A):
  Permutation l1 l2  ->
  forall x, In x l1 <-> In x l2.
Proof with eauto.
  introv PERM; intros; induction PERM; split; introv IN; try inv IN...
  rewrite IHPERM in H; right...
  rewrite <-IHPERM in H; right...
  inv H...
  repeat right...
  inv H...
  repeat right...
  rewrite  IHPERM1, IHPERM2 in IN...
  rewrite  <-IHPERM2, <-IHPERM1 in IN...
Qed.



Lemma type_remove_pol_cup pol1 pol2 t t1 t2:
  type_remove (Chan un pol1 t) t1 t2 ->
  type_remove (Chan un (pol_cup pol1 pol2) t) t1 (Chan un (pol_cup pol1 pol2) t).
Proof with eauto.
  intros TREM;
    try inv TREM as (TS &TP &ISUN).
  assert (t2 = Chan un pol1 t).
  eapply ISUN; try econstructor...
  subst.
  econstructor;repeat split...
  (*  type_sub t0 (Chan un pol1 t) ->
      type_sub t0 (Chan un (pol_cup pol1 pol2) t) *)
  inv TS; inv TP;
    try eapply pol_cup_type_sub...
  instantiate (1 := io)...
  instantiate (1 := io)...
  inverts TP as TP1; try rewrite TP1...
  assert (EQ: Chan un (pol_cup pol1 pol2) t =
                Chan un (pol_cup p1 (pol_cup pol1 pol2)) t).
  destruct p1,pol1,pol2; compute; try tauto; try inv TP1.
  rewrite EQ at 2. econstructor...
Qed.




Lemma typeCheck_weak_is_un : forall g p a1 a2 f pol1 pol2 t pf1 pf2 (nd_pf : NoDup (domain g)),
    typeCheck g pf1 p ->
    In (a1, a2, f, Chan un pol1 t) g ->
    typeCheck
      ((a1, a2, f, Chan un (pol_cup pol1 pol2) t)
         :: removeEntry (a1, a2) g) pf2 p.
Proof with eauto using gcons_removeEntry.
  introv ND TC IN.
  gen f.
  
  dependent induction TC.
  - econstructor.
    assert (prf :isMap (removeEntry (a1, a2)
                          ((a1, a2, f, Chan un (pol_cup pol1 pol2) t) :: removeEntry (a1, a2) g))).
    simpl; try rewrite pairEq_eq_true...
    eapply Co_un with (n := (a1, a2)) (pf' := prf).
    econstructor...
    gen prf; simpl; try rewrite pairEq_eq_true; introv...
  - Case TNew.
    introv IN; destruct n as [n1 n2].
    case_eq (pair_eq (n1, n2) (a1, a2)); introv PEQ;
      try rewrite <-pairEq_eq in PEQ; try inv PEQ.
    assert (prf1: isMap ((a1, a2, vis,  Chan un (pol_cup pol1 pol2) t)
                           :: removeEntry (a1, a2)
                           ((a1, a2, f, Chan un (pol_cup pol1 pol2) t) :: removeEntry (a1, a2) g))).
    eapply no_dup_isMap, no_dup_cons_removeEntry,no_dup_cons_removeEntry...
    assert (EQ: hid = f/\ t0 = Chan un pol1 t).
    eapply in_isMap with (g := g) (x := (a1, a2))...
    destruct EQ; subst.
    eapply TNew with (pf1 := prf1)...

    gen prf1.
    simpl; rewrite pairEq_eq_true; introv.
    
    assert (IH : NoDup (domain ((a1, a2, vis, Chan un pol1 t) :: removeEntry (a1, a2) g))).
    eapply no_dup_cons_removeEntry...

    simpl in IHTC; rewrite pairEq_eq_true in IHTC;
      try eapply IHTC...

    eapply TNew with (t := t0)...
    repeat right; eapply removeEntry_in;
      try eapply pairEq_neq...

    assert (PNEQ := H1).
    assert (IH:  NoDup (domain ((n1, n2, vis, t0) :: removeEntry (n1, n2) g))).
    eapply no_dup_cons_removeEntry...
    eapply IHTC in IH;
      repeat right;
      try eapply removeEntry_in;
      try eapply pairEq_neq in H1...

    
    assert (PNEQ2: pair_eq (a1, a2) (n1, n2) = false).
    eapply pairEq_neq...

    eapply typeCheck_impl with (g1 := ((a1, a2, f, Chan un (pol_cup pol1 pol2) t)
                                         :: removeEntry (a1, a2) ((n1, n2, vis, t0) :: removeEntry (n1, n2) g)) ).
    unfold removeEntry; fold removeEntry; rewrite PNEQ;
      try eapply no_dup_cons_removeEntry_app...
    unfold removeEntry; fold removeEntry; try rewrite PNEQ2;
      try eapply no_dup_cons_removeEntry_app...

    eauto.

    unfold removeEntry; fold removeEntry;
      try rewrite PNEQ;
      try rewrite PNEQ2;
      try rewrite removeEntry_swap;
      try eapply Permutation_iff,perm_swap...
    Unshelve.
    all:eapply no_dup_isMap,no_dup_cons_removeEntry,no_dup_cons_removeEntry...

  - introv IN.
    assert (IND := IN).
    eapply in_g_in_domain,split_domain_l_2
      with (pf1 := pf1) in IND;
      eapply in_domain_in_g in IND as (ff1 &tt1 &IND).
    assert (FYP1: flagOf g1 (a1, a2) ff1)...
    eapply split_operations_3.split_flag_plus
      with (pf2 := pf2) (t := f)
      in FYP1
        as (ff2 &FYP2 &FP).

    eapply TPar with
      (g1 := (a1, a2, ff1, Chan un (pol_cup pol1 pol2) t) :: removeEntry (a1, a2) g1)
      (g2 := (a1, a2, ff2, Chan un (pol_cup pol1 pol2) t) :: removeEntry (a1, a2) g2);
      try eassumption.
    eapply tEnv_split_add_fp...
    rewrite <-pol_cup_id at 3... 

    eapply IHTC1;
      try eapply no_dup_split_no_dup_l...
    assert (IN1 := IN).
    eapply sub_split.tsuper_payload with (g1 := g1)
      in IN1 as (pp &IN1);
      try inverts IN1 as IN1.
    assert (IN' := IN1).
    eapply sub_split.tsub_un with (g := g) in IN'.
    assert (EQ: Chan un pp t = Chan un pol1 t).
    eapply type_of_map with (g := g)...
    inv EQ...
    assert (EQ: tt1 = Chan un pol1 t).
    eapply type_of_map with (g := g1)...
    subst...

    eauto.
    eauto.

    eapply IHTC2;
      try eapply no_dup_split_no_dup_r...
    assert (IN1 := IN).
    eapply sub_split.tsuper_payload_r with (g2 := g2)
      in IN1 as (pp &IN1);
      try inverts IN1 as IN1.
    assert (IN' := IN1).
    eapply sub_split.tsub_un_r with (g := g) in IN'.
    assert (EQ: Chan un pp t = Chan un pol1 t).
    eapply type_of_map with (g := g)...
    inv EQ...
    assert (EQ: ff2 = f0).
    eapply flag_of_map with (g := g2)...
    subst...

    eauto.
    eauto.
    eauto.
    eauto.
    eauto.

    Unshelve.
    all:eapply no_dup_split_no_dup.cons_removeEntry;
      try eapply no_dup_split_no_dup_l;
      try eassumption;
      try eapply split_comm...

  - Case TOutL.
    introv IN.

    assert (TCH :   typeCheck g pf (dOut (fst u) (snd u) (fst v) (snd v) q)).
    eauto.
    
    assert (NR: nonRec_typable (dOut (fst u) (snd u) (fst v) (snd v) q)).
    eapply typeCheck_object_neq_subject with (pf := pf)...
    destruct NR as (NR &_);
      repeat rewrite <-surjective_pairing in NR.
    
    assert (IH:
             NoDup (domain ((u, vis, t1) :: (v, vis, t2) :: removeEntry v (removeEntry u g)))).
    erewrite removeEntry_swap.
    eapply no_dup_cons_removeEntry_app...
    intuition.

    assert (prf2:
             isMap
               ((a1, a2, f, Chan un (pol_cup pol1 pol2) t)
                  :: removeEntry (a1, a2)
                  ((u, vis, t1) :: (v, vis, t2) :: removeEntry v (removeEntry u g)))).
    eapply no_dup_isMap,no_dup_cons_removeEntry;
      try eapply no_dup_cons_removeEntry_app...

    eapply IHTC with  (pf2 := prf2)in IH; clear IHTC...
    
    destruct u as [u1 u2], v as [v1 v2];
      unfold fst, snd in *.
    case_eq (pair_eq (u1, u2) (a1, a2)); intros PEQ;
      try rewrite <-pairEq_eq in PEQ; inv PEQ.
    assert (ABS: Chan lin p t0 = Chan un pol1 t).
    eapply type_of_map with (g := g)...
    inv ABS...
    case_eq (pair_eq (v1, v2) (a1, a2)); intros PEQ;
      try rewrite <-pairEq_eq in PEQ; inv PEQ.

    assert (EQ: vis = f /\ t' = Chan un pol1 t).
    eapply in_isMap with (g := g)...
    destruct EQ; subst.

    +  eapply TOutL with (u := (u1,u2)) (v := (a1,a2))
                         (t' := Chan un (pol_cup pol1 pol2) t),
           typeCheck_impl with (pf1 := prf2);
         try eassumption.
       eapply type_remove_pol_cup...
       right. eapply removeEntry_in...
       eauto.
       assert (EQ: forall l,
                  removeEntry (a1, a2)
                    ((u1, u2, vis, t1)
                       :: (a1, a2, vis, t2) :: l) =
                    (u1, u2, vis, t1) ::  l).
       simpl. try rewrite H4;
         try rewrite pairEq_eq_true...
       rewrite EQ.
       eapply no_dup_cons_removeEntry_app...
       rewrite removeEntry_swap.
       unfold removeEntry at 2; fold removeEntry;
         try rewrite pairEq_eq_true.
       eapply no_dup_cons_removeEntry_app...
       intuition.
       unfold removeEntry at 1; fold removeEntry.
       try rewrite H4;
         try rewrite pairEq_eq_true.
       assert (EQ: forall l,
                  removeEntry (a1, a2)
                    (removeEntry (u1, u2)
                       ((a1, a2, vis, Chan un (pol_cup pol1 pol2) t) ::l)) =
                    removeEntry (u1, u2) l).
       try rewrite removeEntry_swap; simpl.
       assert (PNEQ: pair_eq (a1, a2) (u1, u2) = false).
       assert ( (a1, a2) <> (u1, u2)). intuition.
       eapply pairEq_neq...
       rewrite PNEQ;
         try rewrite pairEq_eq_true...
       rewrite EQ...
       rewrite removeEntry_swap.
       eapply Permutation_iff, perm_swap...
       intuition.

       
    + eapply TOutL with  (u := (u1,u2)) (v := (v1,v2)),
          (*t' := Chan un (pol_cup pol1 pol2) t*)
          typeCheck_impl with (pf1 := prf2);
        try eassumption.
      right; eapply removeEntry_in; try eapply pairEq_neq...
      right; eapply removeEntry_in; try eapply pairEq_neq...
      eapply no_dup_cons_removeEntry;
        try erewrite removeEntry_swap;
        try eapply no_dup_cons_removeEntry_app...
      try erewrite removeEntry_swap;
        try eapply no_dup_cons_removeEntry_app;
        try  eapply no_dup_cons_removeEntry...

      
      unfold removeEntry at 1; fold removeEntry;
        rewrite H4; rewrite H5.
      assert (EQ: forall l,
                 removeEntry (v1, v2)
                   (removeEntry (u1, u2)
                      ((a1, a2, f, Chan un (pol_cup pol1 pol2) t) :: l))=(a1, a2, f, Chan un (pol_cup pol1 pol2) t) ::
                                                                           removeEntry ( v1, v2) (removeEntry (u1, u2)  l)).                     
      unfold removeEntry at 2; fold removeEntry.
      assert (PNEQ: (a1, a2) <> (u1, u2)). eapply pairEq_neq in H4...
      eapply pairEq_neq in PNEQ;
        rewrite PNEQ.
      unfold removeEntry at 1; fold removeEntry.
      assert (PNEQ2: (a1, a2) <> (v1, v2)). eapply pairEq_neq in H5...
      eapply pairEq_neq in PNEQ2;
        rewrite PNEQ2...
      rewrite EQ;
        try rewrite removeEntry_swap;
        clear EQ...
      assert (EQ: removeEntry (a1, a2) (removeEntry (u1, u2) g) =
                    removeEntry (u1, u2) (removeEntry (a1, a2) g)).
      eapply removeEntry_swap...
      rewrite <-pairEq_neq in H4; intuition.
      rewrite EQ.
      eapply Permutation_iff.
      eapply Permutation_middle with
        (l1 := (u1, u2, vis, t1)
                 :: (v1, v2, vis, t2) :: nil)...
      rewrite <-pairEq_neq in H5; intuition.

    +  right. destruct v as [v1 v2].
       case_eq (pair_eq (a1, a2) (v1,v2)); intros PEQ;
         try rewrite <-pairEq_eq in PEQ; inv PEQ.
       assert (EQ: f = vis /\ Chan un pol1 t = t').
       eapply in_isMap with (g := g)...
       destruct EQ; subst.
       inv H0 as (_ &_ &ISUN);
         try erewrite  ISUN; econstructor...
       right;
         eapply removeEntry_in, removeEntry_in...
       try eapply pairEq_neq...
       intros ABS; subst...
       assert (ABS: Chan lin p t0 = Chan un pol1 t).
       eapply type_of_map with (g := g)...
       inv ABS.

         Unshelve.
       all:try assumption.
       rewrite removeEntry_swap.
       eapply no_dup_isMap, no_dup_cons_removeEntry_app;
         try eapply no_dup_cons_removeEntry...
       try eapply pairEq_neq in H4...
     
        rewrite removeEntry_swap.
       eapply no_dup_isMap, no_dup_cons_removeEntry_app;
         try eapply no_dup_cons_removeEntry...
       try eapply pairEq_neq in H4...
       
  -  Case TOutUn.
     introv IN.

     assert (TCH :   typeCheck g pf (dOut (fst u) (snd u) (fst v) (snd v) q)).
     eauto.
     
     assert (NR: nonRec_typable (dOut (fst u) (snd u) (fst v) (snd v) q)).
     eapply typeCheck_object_neq_subject with (pf := pf)...
     destruct NR as (NR &_);
       repeat rewrite <-surjective_pairing in NR.
     
     assert (IH:
              NoDup (domain ( (v, vis, t2) :: removeEntry v g))).
     eapply no_dup_cons_removeEntry...

     assert (prf2:
              isMap
                ((a1, a2, f, Chan un (pol_cup pol1 pol2) t)
                   :: removeEntry (a1, a2)
                   ( (v, vis, t2) :: removeEntry v g))).
     eapply no_dup_isMap,no_dup_cons_removeEntry;
       try eapply no_dup_cons_removeEntry_app...

     eapply IHTC with  (pf2 := prf2)in IH; clear IHTC...
     
     destruct u as [u1 u2], v as [v1 v2];
       unfold fst, snd in *.
     case_eq (pair_eq (u1, u2) (a1, a2)); intros PEQ;
       try rewrite <-pairEq_eq in PEQ; inv PEQ.
     assert (EQ: vis = f /\ Chan un p t0 = Chan un pol1 t).
     eapply in_isMap with (g := g)...
    destruct EQ as [EQ1 EQ2]; inv EQ2; subst.

      destruct H; subst.
        assert (EQ: forall p, pol_cup io p = io).
        destruct p...
        gen prf2 pf2. repeat rewrite EQ. intros.
        eapply TOutUn
          with (u := (a1,a2)) (v := (v1,v2)),
            typeCheck_impl with (pf1 := prf2);
          try eassumption.
        left...
        erewrite EQ...
       right. eapply removeEntry_in...
       eapply no_dup_cons_removeEntry, no_dup_cons_removeEntry...
       eapply no_dup_cons_removeEntry, no_dup_cons_removeEntry...

       assert (PNEQ1: pair_eq (a1,a2)(v1,v2) = false).
       eapply pairEq_neq...
       assert (PNEQ2: pair_eq (v1,v2)(a1,a2) = false).
       eapply pairEq_neq...
       unfold removeEntry; fold removeEntry;
         try erewrite PNEQ1;
         try erewrite PNEQ2.
       rewrite removeEntry_swap.
       eapply Permutation_iff...
       assumption.
       
       eapply TOutUn
          with (u := (a1,a2)) (v := (v1,v2)),
            typeCheck_impl with (pf1 := prf2);
          try eassumption.
        destruct pol2. right...
        eauto. eauto. eauto. eauto.
        right. eapply removeEntry_in...
        eapply no_dup_cons_removeEntry, no_dup_cons_removeEntry...
       eapply no_dup_cons_removeEntry, no_dup_cons_removeEntry...

       assert (PNEQ1: pair_eq (a1,a2)(v1,v2) = false).
       eapply pairEq_neq...
       assert (PNEQ2: pair_eq (v1,v2)(a1,a2) = false).
       eapply pairEq_neq...
       unfold removeEntry; fold removeEntry;
         try erewrite PNEQ1;
         try erewrite PNEQ2.
       rewrite removeEntry_swap.
       eapply Permutation_iff...
       assumption.
       
     case_eq (pair_eq (v1, v2) (a1, a2)); intros PEQ;
          try rewrite <-pairEq_eq in PEQ; inv PEQ.

        assert (EQ: vis = f /\ t' = Chan un pol1 t).
        eapply in_isMap with (g := g)...
        destruct EQ; subst.

     +  eapply TOutUn with (u := (u1,u2)) (v := (a1,a2))
                          (t' := Chan un (pol_cup pol1 pol2) t),
            typeCheck_impl with (pf1 := prf2);
          try eassumption.
        eapply type_remove_pol_cup...
        
        right. eapply removeEntry_in...
        eauto.
         eapply no_dup_cons_removeEntry, no_dup_cons_removeEntry...
       eapply no_dup_cons_removeEntry, no_dup_cons_removeEntry...
       unfold removeEntry; fold removeEntry;  try rewrite pairEq_eq_true...
       tauto.


     + eapply TOutUn with  (u := (u1,u2)) (v := (v1,v2)),
           (*t' := Chan un (pol_cup pol1 pol2) t*)
           typeCheck_impl with (pf1 := prf2);
         try eassumption.
       right; eapply removeEntry_in; try eapply pairEq_neq...
       right; eapply removeEntry_in; try eapply pairEq_neq...
       eapply no_dup_cons_removeEntry,no_dup_cons_removeEntry...
       eapply no_dup_cons_removeEntry,no_dup_cons_removeEntry...

       
       assert (DIFF  := H5).
       eapply pairEq_neq in H5.
       unfold removeEntry at 1; fold removeEntry;
         rewrite DIFF.
       assert (PNEQ: pair_eq (a1, a2) (v1, v2) = false).
       eapply pairEq_neq...
       unfold removeEntry; fold removeEntry;
         try rewrite PNEQ.
       rewrite removeEntry_swap.
       eapply Permutation_iff,perm_swap...
       intuition.

          
     +  destruct v as [v1 v2].
        case_eq (pair_eq (a1, a2) (v1,v2)); intros PEQ;
          try rewrite <-pairEq_eq in PEQ; inv PEQ.
        assert (EQ: f = vis /\ Chan un pol1 t = t').
        eapply in_isMap with (g := g)...
        destruct EQ; subst.
        assert (t2 = Chan un pol1 t).
        destruct pol1; eapply type_remove_un...
        subst...
        right. eapply removeEntry_in;
          try eapply pairEq_neq...

        Unshelve.
       all: try assumption.
       all: try eapply no_dup_isMap;
         try eapply no_dup_cons_removeEntry;
         try eapply no_dup_cons_removeEntry...
   

  - Case TInL.

    introv IN.

    assert (TCH :   typeCheck g pf (dInp (fst u) (snd u) (fst x) (snd x) q)).
    eauto.
    
    assert (NR: nonRec_typable (dInp (fst u) (snd u) (fst x) (snd x) q)).
    eapply typeCheck_object_neq_subject with (pf := pf)...
    destruct NR as (NR &_);
      repeat rewrite <-surjective_pairing in NR.
    
    assert (IH:
             NoDup (domain ((u, vis, t1) :: (x, vis, t0) :: removeEntry u g))).
    eapply no_dup_cons_removeEntry_app_1... 

    assert (prf2:
             isMap
               ((a1, a2, f, Chan un (pol_cup pol1 pol2) t)
                  :: removeEntry (a1, a2)
                  ((u, vis, t1) :: (x, vis, t0) :: removeEntry u g))).
    eapply no_dup_isMap;
      try eapply no_dup_cons_removeEntry...

    eapply IHTC with  (pf2 := prf2)in IH; clear IHTC...
    
    destruct u as [u1 u2], x as [x1 x2];
      unfold fst, snd in *.
    case_eq (pair_eq (u1, u2) (a1, a2)); intros PEQ;
      try rewrite <-pairEq_eq in PEQ; inv PEQ.
    assert (ABS: Chan lin p t0 = Chan un pol1 t).
    eapply type_of_map with (g := g)...
    inv ABS...
    case_eq (pair_eq (x1, x2) (a1, a2)); intros PEQ;
      try rewrite <-pairEq_eq in PEQ; inv PEQ.
    eapply in_g_in_domain in IN; try contradiction.

    eapply TInL
          with (u := (u1,u2)) (x := (x1,x2)),
            typeCheck_impl with (pf1 := prf2);
          try eassumption.
    right; eapply removeEntry_in;
      try eapply pairEq_neq...

    intros ABS; erewrite <-in_removeEntry_cons_iff with (g := g) in ABS;
      try contradiction;
      try eapply in_g_in_domain...

    unfold snd;
      rewrite <-max_same_domain with (m := domain g);
      try eapply in_removeEntry_cons_iff;
    try eapply in_g_in_domain...

    eapply no_dup_cons_removeEntry,no_dup_cons_removeEntry_app_1...
    eapply no_dup_cons_removeEntry_app_1;
      try eapply no_dup_cons_removeEntry...
     intros ABS; erewrite <-in_removeEntry_cons_iff with (g := g) in ABS;
      try contradiction;
       try eapply in_g_in_domain...

     assert (PNEQ:  pair_eq (a1, a2) (u1, u2) = false).
     rewrite <-pairEq_neq in H4; eapply pairEq_neq...
     unfold removeEntry;
       fold removeEntry;
       try rewrite H4;
       try rewrite PNEQ;
       try rewrite H5.
     erewrite removeEntry_swap.
     eapply Permutation_iff;
     try eapply Permutation_middle with
        (l1 := (u1, u2, vis, t1)
                 :: (x1, x2, vis, t0) :: nil)...
     try eapply pairEq_neq...
     repeat right; eapply removeEntry_in...
     intros ABS; subst.
     assert (ABS:
              Chan lin p t0 =  Chan un pol1 t).
     eapply type_of_map with (g := g)...
     inv ABS.

     Unshelve.
     all:try assumption.
     eapply no_dup_isMap,no_dup_cons_removeEntry_app_1;
       try eapply no_dup_cons_removeEntry; try intros ABS;
       try erewrite <-in_removeEntry_cons_iff with (g := g) in ABS;
      try contradiction;
      try eapply in_g_in_domain...
     
  - Case TInUn.

     introv IN.

    assert (TCH :   typeCheck g pf (dInp (fst u) (snd u) (fst x) (snd x) q)).
    eauto.
    
    assert (NR: nonRec_typable (dInp (fst u) (snd u) (fst x) (snd x) q)).
    eapply typeCheck_object_neq_subject with (pf := pf)...
    destruct NR as (NR &_);
      repeat rewrite <-surjective_pairing in NR.

    assert (DIFF: (a1, a2) <> x).
    intros ABS; destruct x; try inv ABS;
      try eapply in_g_in_domain in IN;
      try contradiction...
    

    
    assert (IH:
             NoDup (domain ((x, vis, t0) :: g))).
    simpl; econstructor; try intros ABS;
      try eapply in_domain_in_g in ABS as (ff &tt &ABS);
      try eapply in_g_in_domain in ABS;
      try contradiction...
    assert (ND2 := IH).

    assert (prf2:
             isMap
               ((a1, a2, f, Chan un (pol_cup pol1 pol2) t)
                  :: removeEntry (a1, a2)
                  ((x, vis, t0) ::g))).
    eapply no_dup_isMap;
      try eapply no_dup_cons_removeEntry...

    eapply IHTC with  (pf2 := prf2)in IH; clear IHTC...
    
    destruct u as [u1 u2], x as [x1 x2];
      unfold fst, snd in *.
    case_eq (pair_eq (u1, u2) (a1, a2)); intros PEQ;
      try rewrite <-pairEq_eq in PEQ; inv PEQ.
    assert (EQ: vis = f /\ Chan un p t0 = Chan un pol1 t).
    eapply in_isMap with (g := g)...
    destruct EQ as [EQ1 EQ2]; subst; inv EQ2.

    

    
    assert (PNEQ: pair_eq (x1, x2) (a1, a2) =false).
    eapply pairEq_neq...

    destruct H; subst.
    assert (EQ: forall p, pol_cup io p = io).
    destruct p...
    gen prf2 pf2. repeat rewrite EQ. intros.

    eapply TInUn
          with (u := (a1,a2)) (x := (x1,x2)),
            typeCheck_impl with (pf1 := prf2);
      try eassumption.
    left...
    rewrite EQ...
     intros ABS; erewrite <-in_removeEntry_cons_iff with (g := g) in ABS;
      try contradiction;
       try eapply in_g_in_domain...

      unfold snd;
      rewrite <-max_same_domain with (m := domain g);
      try eapply in_removeEntry_cons_iff;
        try eapply in_g_in_domain...

      eapply no_dup_cons_removeEntry...

      simpl; econstructor;
        try intros ABS;
      try erewrite in_removeEntry_cons_iff with (g := g) (f := ill) (t := Top) in H1;
        try eapply in_g_in_domain...
      eapply no_dup_cons_removeEntry with (f1 := ill) (t1 := Top)...
      unfold removeEntry; fold removeEntry;
        try rewrite PNEQ.
      eapply Permutation_iff...
      
    
    eapply TInUn
          with (u := (a1,a2)) (x := (x1,x2)),
            typeCheck_impl with (pf1 := prf2);
      try eassumption.
    destruct pol2. right...
    eauto.  eauto. eauto. eauto.
    intros ABS; erewrite <-in_removeEntry_cons_iff with (g := g) in ABS;
      try contradiction;
      try eapply in_g_in_domain...

    unfold snd;
      rewrite <-max_same_domain with (m := domain g);
      try eapply in_removeEntry_cons_iff;
    try eapply in_g_in_domain...

    eapply no_dup_cons_removeEntry...
    simpl;  econstructor;  try intros ABS;
      try erewrite in_removeEntry_cons_iff with (g := g)  (f := ill) (t := Top) in H1;
      try contradiction;
      try eapply in_g_in_domain...

     eapply no_dup_cons_removeEntry with (f1 := ill) (t1 := Top)...
      unfold removeEntry; fold removeEntry;
        try rewrite PNEQ.
      eapply Permutation_iff...


     assert (PNEQ:  pair_eq (a1, a2) (u1, u2) = false).
     rewrite <-pairEq_neq in H4; eapply pairEq_neq...

      eapply TInUn
          with (u := (u1,u2)) (x := (x1,x2)),
            typeCheck_impl with (pf1 := prf2);
      try eassumption.

      right; eapply removeEntry_in;
        try eapply pairEq_neq...

        try intros ABS;
      try erewrite in_removeEntry_cons_iff with (g := g) (f := ill) (t := Top) in H1;
          try eapply in_g_in_domain...

         unfold snd;
      rewrite <-max_same_domain with (m := domain g);
      try eapply in_removeEntry_cons_iff;
    try eapply in_g_in_domain...

    eapply no_dup_cons_removeEntry...
    simpl;  econstructor;  try intros ABS;
      try erewrite in_removeEntry_cons_iff with (g := g) (f := ill) (t := Top) in H1;
      try contradiction;
      try eapply in_g_in_domain...

    eapply no_dup_cons_removeEntry with (f1 := ill) (t1 := Top)...

    assert (PNEQ2: pair_eq (x1,x2) (a1, a2) = false).
    try eapply pairEq_neq...
    unfold removeEntry; fold removeEntry;
        try rewrite PNEQ2.
    eapply Permutation_iff...

    right...

    Unshelve.
    all:try assumption.

    all:try eapply no_dup_isMap; simpl; econstructor;
      try intros ABS;
       try erewrite in_removeEntry_cons_iff with (g := g) (f := ill) (t := Top) in H1;
      try contradiction;
      try eapply in_g_in_domain;
    try eapply no_dup_cons_removeEntry with (f1 := ill) (t1 := Top)...

  - Case TInU.

     introv IN.

    assert (TCH :   typeCheck g pf (dBang (fst u) (snd u) (fst x) (snd x) q)).
    eauto.
    
    assert (NR: nonRec_typable (dBang (fst u) (snd u) (fst x) (snd x) q)).
    eapply typeCheck_object_neq_subject with (pf := pf)...
    destruct NR as (NR &_);
      repeat rewrite <-surjective_pairing in NR.

    assert (DIFF: (a1, a2) <> x).
    intros ABS; destruct x; try inv ABS;
      try eapply in_g_in_domain in IN;
      try contradiction...
    

    
    assert (IH:
             NoDup (domain ((x, vis, t0) :: g))).
    simpl; econstructor; try intros ABS;
      try eapply in_domain_in_g in ABS as (ff &tt &ABS);
      try eapply in_g_in_domain in ABS;
      try contradiction...
    assert (ND2 := IH).

    assert (prf2:
             isMap
               ((a1, a2, f, Chan un (pol_cup pol1 pol2) t)
                  :: removeEntry (a1, a2)
                  ((x, vis, t0) ::g))).
    eapply no_dup_isMap;
      try eapply no_dup_cons_removeEntry...

    eapply IHTC with  (pf2 := prf2)in IH; clear IHTC...

    assert (prf3 := ND).
    eapply no_dup_vis_ill_proj  with a1 a2 (Chan un (pol_cup pol1 pol2) t) g,no_dup_isMap in prf3. 
    
    destruct u as [u1 u2], x as [x1 x2];
      unfold fst, snd in *.
    case_eq (pair_eq (u1, u2) (a1, a2)); intros PEQ;
      try rewrite <-pairEq_eq in PEQ; inv PEQ.
    assert (EQ: vis = f /\ Chan un p t0 = Chan un pol1 t).
    eapply in_isMap with (g := g)...
    destruct EQ as [EQ1 EQ2]; subst; inv EQ2.

    

    
    assert (PNEQ: pair_eq (x1, x2) (a1, a2) =false).
    eapply pairEq_neq...

    destruct H; subst.
    assert (EQ: forall p, pol_cup io p = io).
    destruct p...
    gen prf2 pf2. repeat rewrite EQ. intros.


    eapply TInU
          with (u := (a1,a2)) (x := (x1,x2)),
            typeCheck_impl with (pf1 := prf2);
      try eassumption.
    left...
    rewrite EQ...
     intros ABS; erewrite <-in_removeEntry_cons_iff with (g := g) in ABS;
      try contradiction;
       try eapply in_g_in_domain...

      unfold snd;
      rewrite <-max_same_domain with (m := domain g);
      try eapply in_removeEntry_cons_iff;
        try eapply in_g_in_domain...

      instantiate (1 := prf3).
      eapply cons_distr in H3 as (C1 &C2);
        eapply cons_distr;
        split.
      eapply gcons_vis_proj_add...
      eapply gcons_ill_proj_add...    
      
      eapply no_dup_cons_removeEntry...

      simpl; econstructor;
        try intros ABS;
      try erewrite in_removeEntry_cons_iff with (g := g) (f := ill) (t := Top) in H1;
        try eapply in_g_in_domain...
      eapply no_dup_cons_removeEntry with (f1 := ill) (t1 := Top)...
      unfold removeEntry; fold removeEntry;
        try rewrite PNEQ.
      eapply Permutation_iff...
      
    
    eapply TInU
          with (u := (a1,a2)) (x := (x1,x2)),
            typeCheck_impl with (pf1 := prf2);
      try eassumption.
    destruct pol2. right...
    eauto.  eauto. eauto. eauto.
    intros ABS; erewrite <-in_removeEntry_cons_iff with (g := g) in ABS;
      try contradiction;
      try eapply in_g_in_domain...

    unfold snd;
      rewrite <-max_same_domain with (m := domain g);
      try eapply in_removeEntry_cons_iff;
      try eapply in_g_in_domain...

     instantiate (1 := prf3).
      eapply cons_distr in H3 as (C1 &C2);
        eapply cons_distr;
        split.
      eapply gcons_vis_proj_add...
      eapply gcons_ill_proj_add...    
     

    eapply no_dup_cons_removeEntry...
    simpl;  econstructor;  try intros ABS;
      try erewrite in_removeEntry_cons_iff with (g := g)  (f := ill) (t := Top) in H1;
      try contradiction;
      try eapply in_g_in_domain...

     eapply no_dup_cons_removeEntry with (f1 := ill) (t1 := Top)...
      unfold removeEntry; fold removeEntry;
        try rewrite PNEQ.
      eapply Permutation_iff...


     assert (PNEQ:  pair_eq (a1, a2) (u1, u2) = false).
     rewrite <-pairEq_neq in H5; eapply pairEq_neq...

      eapply TInU
          with (u := (u1,u2)) (x := (x1,x2)),
            typeCheck_impl with (pf1 := prf2);
      try eassumption.

      right; eapply removeEntry_in;
        try eapply pairEq_neq...

        try intros ABS;
      try erewrite in_removeEntry_cons_iff with (g := g) (f := ill) (t := Top) in H1;
          try eapply in_g_in_domain...

         unfold snd;
      rewrite <-max_same_domain with (m := domain g);
      try eapply in_removeEntry_cons_iff;
    try eapply in_g_in_domain...

      eapply cons_distr in H3 as (C1 &C2);
        eapply cons_distr;
        split.
      eapply gcons_vis_proj_add...
      eapply gcons_ill_proj_add...    
     
    eapply no_dup_cons_removeEntry...
    simpl;  econstructor;  try intros ABS;
      try erewrite in_removeEntry_cons_iff with (g := g) (f := ill) (t := Top) in H1;
      try contradiction;
      try eapply in_g_in_domain...

    eapply no_dup_cons_removeEntry with (f1 := ill) (t1 := Top)...

    assert (PNEQ2: pair_eq (x1,x2) (a1, a2) = false).
    try eapply pairEq_neq...
    unfold removeEntry; fold removeEntry;
        try rewrite PNEQ2.
    eapply Permutation_iff...

    right...

    Unshelve.
    
    all:
      match goal with
       |  [ _ : _ |- isMap (vis_proj _)] =>
            try eapply proj_isMap;
            eauto
      |  [ _ : _ |- isMap (ill_proj _)] =>
           try eapply proj_isMap;
           eauto
      |  [ _ : _ |- isMap ( _ :: _)] =>
            try eapply no_dup_isMap; simpl; econstructor;
      try intros ABS;
       try erewrite in_removeEntry_cons_iff with (g := g) (f := ill) (t := Top) in H1;
      try contradiction;
      try eapply in_g_in_domain;
    try eapply no_dup_cons_removeEntry with (f1 := ill) (t1 := Top); eauto
      | _ => 
          try eassumption
      end. 

    eapply no_dup_isMap; rewrite domain_distr, no_dup_iff;
      repeat split; try eapply no_dup_vis_proj;
      try eapply no_dup_ill_proj;
      try eapply no_dup_cons_removeEntry;
      try eapply disjoint_projections;
      try eapply no_dup_cons_removeEntry...


    
Qed.

            
