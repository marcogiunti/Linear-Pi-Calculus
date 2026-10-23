Require Import
  Bool List Lia PeanoNat Program.Equality
  ListAddOns Max Domain RemoveEntry NewEntries Replication
  header
  operations pi_syntax 
  pairEq type_system
  semantics
  tc_dep_relabel_premises
  type_system_rules
  split_not_exists
  tc_prelim
  split_operations_4
  split_existential
  type_operations_1
  no_dup_split_no_dup
  proposition27
  disjoint_newEntries
  lts_payload_un_inp
  tc_premises_4
  lts_no_dup
  sne_premises
  split_cons_remove
  split_operations
  tc_premises_5.
 
Require Import CpdtTactics LibTactics.
Import ListNotations.

#[global] Hint Resolve
  lts_operations.lts_lin_output_action
  lts_operations.lts_lin_input_action
  lts_operations.lts_un_output_action
  lts_un_input_action.

#[global] Hint Constructors replication.

Lemma lts_after_tau_linh: forall g  p1 p2 a1 a2 t g' nd_pf,
    lts g p1 (aTau a1 a2) g' p2 nd_pf ->
    In (a1, a2, hid, Chan lin io t) g ->
    exists b1 b2 f tb,
      (a1, a2) <> (b1, b2) /\  
        In (b1, b2, f, tb) g /\
        f <> ill /\
        g' =  (a1, a2, hid, Chan lin empty t)
                :: (b1, b2, f, tb)
                :: removeEntry (a1, a2) (removeEntry (b1, b2) g).
Proof with eauto.
  intros g  p1 p2 a1 a2 t g' nd_pf LTS IN.
  dependent induction LTS...
  - 
    assert (EQ0: vis = hid).
    eapply flag_of_map with (g := g) (x := (a1,a2));
      try eapply no_dup_isMap;
      try eassumption...
    discriminate.
  -   assert (EQ0: vis = hid).
      eapply flag_of_map with (g := g) (x := (a1,a2));
        try eapply no_dup_isMap;
        try eassumption...
      discriminate.
  -  assert (EQ0: vis = hid).
     eapply flag_of_map with (g := g) (x := (a1,a2));
       try eapply no_dup_isMap;
       try eassumption...
     discriminate.

  -  assert (EQ0: vis = hid).
     eapply flag_of_map with (g := g) (x := (a1,a2));
       try eapply no_dup_isMap;
       try eassumption...
     discriminate.

  - Case hide.
    assert (HIDE: lts (h1 ++ (b1, b2, hid, t0) :: h2) (dNu b1 b2 p) (aTau a1 a2) (h' ++ (b1, b2, hid, t') :: h'')(dNu b1 b2 p') pf)...
    remember b1 as c1. remember b2 as c2. subst b1 b2.

    assert (PF := pf).

    
 case_eq (pair_eq (a1, a2) (c1, c2)); intros PEQ;
      try rewrite <-pairEq_eq in PEQ; inv PEQ.
    assert (NIN1: ~In (c1, c2) (domain h1)).
    intros ABS; rewrite domain_distr in PF;
      eapply no_dup_iff in PF as (_ &_ &DIS);
      simpl in DIS;
      try eapply disjoint_absurd...
    assert (NIN2: ~In (c1, c2) (domain h2)).
     intros ABS; rewrite domain_distr in PF;
       eapply no_dup_iff in PF as (_ &ND2 &_);
       try inv ND2; try contradiction.
    assert (LTS2 := LTS).
    eapply lts_after_tau_lin with (t :=t)in LTS
        as (b1 &b2 &ff1 &tt &DIFF1 &IN3 &NILL3 &AFT).
    exists b1 b2 ff1 tt; repeat split...
     eapply in_app_iff in IN3 as [HD | CONT];
      eapply in_app_iff;
      try inverts CONT as EQ; try inv EQ;
      try contradiction...
    repeat right...
    
    rewrite removeEntry_swap,removeEntry_app_shift in *;
      try eassumption.
    simpl in *; try rewrite pairEq_eq_true in *.
    eapply typeEnv_eq_change_flag with (k1 := nil).
    try simpl ...
    intros ABS; inv ABS.
    intros ABS; simpl in ABS; destruct ABS as [ABS | CONT];
      try inv ABS; try contradiction.
    eapply in_domain_in_g in CONT as (ff2 &tt2 &CONT);
      eapply in_removeEntry,in_app_iff in CONT;
      destruct CONT as [ABS1 | ABS1];
      try eapply in_g_in_domain in ABS1;
      try contradiction.
    eapply in_app_iff in IN as  [ABS1 | CONT];
      try destruct CONT as [EQ | ABS2];
      try eapply in_g_in_domain in ABS1;
      try contradiction;
      try inv EQ;
      eapply in_app_iff; try right; eauto;
      try eapply in_g_in_domain in ABS2;
      try contradiction.


    assert (DIFF3: (a1, a2) <> (c1, c2)).
    eapply pairEq_neq...

    assert (IH: aTau a1 a2 = aTau a1 a2)...
    eapply IHLTS in IH
        as (d1 & d2 &ff &tb & DIFF &IN2 &NILL &IH); clear IHLTS...

    
    
   
    
    eapply in_app_iff in IN2 as [IN2 | CONT]...

    exists d1 d2  ff tb; intuition...
    eapply typeEnv_eq_change_flag_removeEntry_app...
    intros ABS; inv ABS.
    rewrite domain_distr in PF;
      eapply no_dup_iff in PF as (ND1 &ND2 &DIS);
      eapply disjoint_absurd with (x := (c1, c2));
      try eapply in_g_in_domain...
    inverts CONT as EQ; try inv EQ.
    exists d1 d2 hid tb; intuition; try discriminate.
    assert (NIN1: In (d1, d2) (domain h1)-> False). intros ABS.
    rewrite domain_distr in PF;
      eapply no_dup_iff in PF as (ND1 &_ &DIS).
    simpl in DIS;
      eapply disjoint_absurd with (x := (d1, d2))...
    assert (NIN2: In (d1, d2) (domain h2)-> False). intros ABS.
    rewrite domain_distr in PF;
      eapply no_dup_iff in PF as (_ &ND2 &_);
      simpl in ND2; eapply NoDup_cons_iff in ND2; intuition.
    rewrite removeEntry_app_shift in *...
    simpl in *; rewrite pairEq_eq_true in *...
    assert (EQ: forall f1 f2,
               (a1, a2, f1, Chan lin empty t) :: (d1, d2, f2, tb) :: removeEntry (a1, a2) (h1 ++ h2) =
                 [(a1, a2, f1, Chan lin empty t)] ++
                   (d1, d2, f2, tb) :: removeEntry (a1, a2) (h1 ++ h2))...
    
    erewrite EQ in IH;
      eapply typeEnv_eq_change_flag in IH as (_ &EQ2 &EQ3);
      try inv EQ2.
    erewrite EQ...
    simpl; intros ABS; inv ABS...
    intros ABS; eapply in_domain_in_g in ABS as (ff &tt&ABS);
      eapply in_removeEntry,in_app_iff in ABS;
      destruct ABS as [ABS | ABS].
    eapply in_g_in_domain in ABS; try contradiction.
    eapply in_g_in_domain in ABS; try contradiction.

    exists d1 d2 ff tb; intuition; try discriminate.
    eapply typeEnv_eq_change_flag_removeEntry_app...
     intros ABS; inv ABS.
    rewrite domain_distr in PF;
      eapply no_dup_iff in PF as (ND1 &ND2 &DIS);
      simpl in ND2; try inv ND2;
      try eapply in_g_in_domain in EQ;
      try contradiction.
   
    eapply in_app_iff in IN as [HD | CONT];
      eapply in_app_iff;
      try inverts CONT as EQ; try inv EQ;
      try contradiction...
    repeat right...
    Unshelve.

    all: rewrite domain_distr in *;
      simpl in *...
Qed.




Lemma lts_after_tau_unh: forall g  p1 p2 a1 a2 t g' nd_pf nd_pf1,
    sl_pos p1 ->
    incl (secLabs p1) (domain (hid_proj g)) ->
    NoDup (secLabs p1) ->
    lts g p1 (aTau a1 a2) g' p2 nd_pf ->
    In (a1, a2, hid, Chan un io t) g ->
    exists b1 b2 f tb ne,
      (a1, a2) <> (b1, b2) /\  
        In (b1, b2, f, tb) g /\
        (((g' =  ne ++ 
                  (b1, b2, f, tb)
                  ::  (removeEntry (b1, b2) g)) /\ f <> ill) \/
           (g' =  ((b1, b2), f, tb) ::
                    removeEntry (b1, b2)
                    (ne ++
                       (b1, b2, vis, tb)
                       ::  (removeEntry (b1, b2) g))) /\ f = hid) /\
        (ne = nil \/
           exists q : dproc,
             replication p1 p2 q /\
               incl (secLabs q) (secLabs p1) /\
               ne = newEntries g 
                      (secLabs (dep_relabel q (domain g) nd_pf1)) 
                      (max (domain g))).
Proof with eauto using no_dup_app_shift,iff_shift.
  intros g  p1 p2 a1 a2 t g' nd_pf nd_pf1 SLP SL ND LTS IN.

   
  dependent induction LTS...
  - eapply sl_pos_par_l,IHLTS in SLP as
        (b1 &b2 &f & tt &ne &DIFF &IN3 &NILEQ &[NIL | (qq& REPL& INCL &NEEQ)]);
      try exists b1 b2 f tt ne;
                 try repeat split...
                 right; exists qq; try repeat split...
                 simpl; eapply incl_appr...
                 simpl in SL; eapply incl_distr in SL; intuition.
                 simpl in ND; eapply no_dup_iff in ND; intuition.
  -  assert (EQ0: vis = hid).
    eapply flag_of_map with (g := g) (x := (a1,a2));
      try eapply no_dup_isMap;
      try eassumption...
    discriminate.
    -  assert (EQ0: vis = hid).
    eapply flag_of_map with (g := g) (x := (a1,a2));
      try eapply no_dup_isMap;
      try eassumption...
    discriminate.
    -  assert (EQ0: vis = hid).
    eapply flag_of_map with (g := g) (x := (a1,a2));
      try eapply no_dup_isMap;
      try eassumption...
    discriminate.
    -  assert (EQ0: vis = hid).
    eapply flag_of_map with (g := g) (x := (a1,a2));
      try eapply no_dup_isMap;
      try eassumption...
    discriminate.



    - Case hide.

      assert (pfh := pf).

      assert (HIDE:
               lts (h1 ++ (b1, b2, hid, t0) :: h2) (dNu b1 b2 p)
                 (aTau a1 a2) (h' ++ (b1, b2, hid, t') :: h'')
                 (dNu b1 b2 p')
                 pfh)...

       assert (DOMEQ:
             (domain (h1 ++ (b1, b2, vis, t0) :: h2) =
                (domain (h1 ++ (b1, b2, hid, t0) :: h2)))).
    repeat rewrite domain_distr; simpl...


      assert (PF := pf1).
      assert (nd_pf' :
               NoDup (domain (h1 ++ (b1, b2, hid, t0) :: h2))).
      rewrite domain_distr in *; simpl in *...

    assert (SL2 := SL).
        simpl in SL2; eapply incl_distr in SL2 as [INCL' _].
      assert (INCL'':  incl (secLabs p) (domain (h1 ++ (b1, b2, hid, t0) :: h2))).
      eapply incl_tran,hid_proj_incl...
      rewrite hid_proj_app,domain_distr in INCL';
        simpl in INCL'.
      rewrite domain_distr in INCL''; simpl in INCL''.
    
   case_eq (pair_eq (a1, a2) (b1, b2)); intros PEQ;
     try rewrite <-pairEq_eq in PEQ; inv PEQ.
    assert (NIN1: ~In (b1, b2) (domain h1)).
     intros ABS; rewrite domain_distr in PF;
       eapply no_dup_iff in PF as (_ &_ &DIS);
       simpl in DIS;
       try eapply disjoint_absurd...
     assert (NIN2: ~In (b1, b2) (domain h2)).
     intros ABS; rewrite domain_distr in PF;
       eapply no_dup_iff in PF as (_ &ND2 &_);
       try inv ND2; try contradiction.
     assert (LTS2 := LTS).
     eapply lts_after_tau_un with (t :=t)in LTS
         as (d1 &d2 &ff1 &tt  &ne1 &DIFF1 &IN3 &NILL3 &AFT);
       try eassumption.

    
     
     exists d1 d2 ff1 tt ne1; repeat split...
     eapply in_app_iff in IN3 as [HD | CONT];
       eapply in_app_iff;
       try inverts CONT as EQ; try inv EQ;
       try contradiction...
     repeat right...

     destruct NILL3 as [(NILL1 &DIFF') | (NILL2 &EQ1)].
     left; repeat split...
     eapply  typeEnv_eq_change_flag_removeEntry...
     destruct AFT as [NIL | (q &REPL &INCL &NEEQ)];
       subst...
     eapply disjoint_commute.
      rewrite <-DOMEQ.
      eapply new_entries_disjoint...
      eapply sl_pos_repl...
      eapply incl_preserves_max, incl_tran;
        try eapply secLabs_of_repl;
      try rewrite domain_distr; simpl...
      right;  repeat split...

      assert (PNEQ: pair_eq (b1, b2) (d1, d2) = false).
      eapply pairEq_neq...


      assert (ND2:
                 NoDup (domain (ne1 ++ (d1, d2, vis, tt) :: removeEntry (d1, d2) (h1 ++ (b1, b2, hid, t0) :: h2)))).
        rewrite domain_distr,no_dup_iff; repeat split.
         destruct AFT as [NIL | (q &REPL &INCL &NEEQ)];
           subst; simpl.
         eauto.
         eapply newEntries_no_dup;
           try eapply prop27,incl_incl2;
           try eapply replication_no_dup...
         eapply incl_tran; try eapply secLabs_of_repl;
           try rewrite domain_distr; simpl...
         eapply no_dup_cons_removeEntry...
         destruct AFT as [NIL | (q &REPL &INCL &NEEQ)];
           subst ne1...
         try eapply disjoint_commute,disjoint_iff;
           try eapply new_entries_disjoint.
            eapply sl_pos_repl...
            eapply incl_preserves_max, incl_tran;
              try eapply secLabs_of_repl;
              try rewrite domain_distr; simpl...
            rewrite DOMEQ; intros;
              rewrite cons_removeEntry_iff; try tauto.
            assert (TYP: typeOf (h1 ++ (b1, b2, hid, t0) :: h2) (d1, d2) tt).
            eapply typeOf_hide_app...
            inv TYP; eapply in_g_in_domain...
            
            
            
         eapply in_app_iff in IN3 as [HD | CONT];
       try inverts CONT as EQ; try inv EQ;
        try contradiction...

      assert (EQ: forall f,
                 removeEntry (d1, d2) (h1 ++ (b1, b2, f, t0) :: h2) =
                 removeEntry (d1, d2) h1 ++ (b1, b2, f, t0) ::  h2).
      intros; rewrite removeEntry_app_shift2...
        assert (EQ2: forall l,
              ne1 ++ (d1, d2, vis, tt) :: removeEntry (d1, d2) h1 ++ l =
                (ne1 ++ (d1, d2, vis, tt) :: removeEntry (d1, d2) h1) ++ l).
        intros; rewrite <-app_assoc...
         
      rewrite EQ,EQ2 in *.
      eapply  typeEnv_eq_change_flag_removeEntry
        with  (h := nil) (h1 := ne1 ++ (d1, d2, vis, tt) :: removeEntry (d1, d2) h1); try eassumption...

      assert (~In (d1, d2) (domain h1)).
      intros ABS; eapply in_g_in_domain in EQ.
      assert (PF1 := nd_pf').
      rewrite domain_distr in PF1; 
        try eapply no_dup_iff in PF1 as ( _&_ &DIS);
        simpl in DIS; 
        try eapply disjoint_absurd...
      right...
      
       assert (EQ2: forall f,
                 removeEntry (d1, d2) (h1 ++ (b1, b2, f, t0) :: h2) =
                 h1 ++ (b1, b2, f, t0) ::   removeEntry (d1, d2) h2).
       intros; rewrite removeEntry_app_shift; simpl; try rewrite PNEQ...
       rewrite EQ2.
        assert (EQ3: forall  l,
              ne1 ++ (d1, d2, vis, tt) :: h1 ++ l =
                (ne1 ++ (d1, d2, vis, tt) :: h1) ++ l).
        intros; rewrite <-app_assoc...
         rewrite EQ2,EQ3 in *.
      eapply  typeEnv_eq_change_flag_removeEntry
        with  (h := nil) (h1 := ne1 ++ (d1, d2, vis, tt) ::  h1); try eassumption...

      clear NILL3.
      destruct AFT as [NIL | (q &REPL &INCL &NEEQ)];
        subst ne1...
      right; exists q; repeat split...
      simpl; eapply incl_appl...

      instantiate (1 := pf1).
      remember (newEntries (h1 ++ (b1, b2, vis, t0) :: h2)
    (secLabs (dep_relabel q (domain (h1 ++ (b1, b2, vis, t0) :: h2)) pf1))
    (max (domain (h1 ++ (b1, b2, vis, t0) :: h2)))) as ne.
      assert (NEEQ := Heqne).
       erewrite newEntries_iff with (g2 := (b1, b2, hid, t0) :: h1 ++ h2);
       try eapply iff_shift;
       try eassumption.
     erewrite newEntries_iff with (g2 := (b1, b2, vis, t0) :: h1 ++ h2) in NEEQ;
       try eapply incl_pos;
       try eapply iff_shift;
       try eassumption.
     clear Heqne.
     erewrite identif_seclabs_of_dep_relabel,newEntries_remove_var with (x1 := b1) (x2 := b2)in *;
       try eassumption.
     rewrite domain_distr in *; simpl in *...
     eapply incl_pos; try eapply sl_pos_nu... 
     eapply min_max; rewrite domain_distr;simpl;
       erewrite in_app_iff...
     intros ABS; eapply secLabs_of_repl in ABS;
       simpl in ND;
       try eapply no_dup_iff in ND as (_&_&DIS);
       try eapply disjoint_absurd...
     eauto.
     simpl in *; rewrite domain_distr in *; eapply no_dup_app_shift...
     eapply incl_pos; try eapply sl_pos_nu... 
     eapply min_max; rewrite domain_distr;simpl;
         erewrite in_app_iff...
       intros ABS; eapply secLabs_of_repl in ABS;
       simpl in ND;
       try eapply no_dup_iff in ND as (_&_&DIS);
         try eapply disjoint_absurd...
       eauto.
       simpl in *; rewrite domain_distr in *;
         try eapply no_dup_app_shift...
       simpl in *; rewrite domain_distr in *;
         try eapply no_dup_app_shift...
       simpl in *; rewrite domain_distr in *;
         try eapply no_dup_app_shift...
      

      eauto.
      rewrite hid_proj_app in *;simpl in *;
        rewrite domain_distr in *;
        unfold incl in *;
        try introv IN';
        assert (INSL := IN');
        try eapply INCL' in IN';
        try eapply in_app_iff in IN' as [IN' | CONT];
        try inv CONT as [ABS2 | CONT2];
        try eapply in_app_iff...
      eapply no_dup_iff in ND as (_&_&DIS);
        try eapply disjoint_absurd...
      simpl in ND; eapply no_dup_iff in ND; intuition.
      
      assert (t0 = Chan un io t).
      eapply in_app_iff in IN as [ABS | CONT];
        try inversion CONT as [EQ | ABS];
        try eapply in_g_in_domain in ABS;
        try contradiction;
        try inv EQ;
        try eapply in_g_in_domain in ABS;
        try contradiction...

      subst; eapply in_app_iff; right...
    

    assert (DIFF3: (a1, a2) <> (b1, b2)).
    eapply pairEq_neq...

    (* OLD *)
      assert (nd_pf'' := pf1); 
     eapply sl_pos_nu in SLP;
       assert (SLP2 := SLP);
       try eapply IHLTS with (nd_pf1 := nd_pf'') in SLP 
      as 
      (d1 &d2 &ff &tt &ne
       &DIFF &IN2 &EQ &IH); clear IHLTS...

 
   
     eapply in_app_iff in IN2 as [IN2|CONT].
     
    exists d1 d2 ff tt ne.
    split...
    split; try eapply in_app_iff...
    split...
    (* h' ++ (b1, b2, hid, t') :: h'' = ne ++ (d1, d2, ff, tt) :: removeEntry (d1, d2) (h1 ++ (b1, b2, hid, t0) :: h2) \/
  h' ++ (b1, b2, hid, t') :: h'' =
  (d1, d2, ff, tt) :: removeEntry (d1, d2) (ne ++ (d1, d2, vis, tt) :: removeEntry (d1, d2) (h1 ++ (b1, b2, hid, t0) :: h2)) /\
  ff = hid*)
    destruct EQ as [(OPT1 &NILL) | OPT2].

    left.
    split... eapply typeEnv_eq_change_flag_removeEntry...
    intros ABS; inv ABS.
    rewrite domain_distr in pf; simpl in pf;
      rewrite no_dup_iff in pf; destruct pf as (_ &_ &DIS).
    eapply disjoint_absurd,in_g_in_domain...
    eapply disjoint_commute...
    destruct IH as [EQ | (q &REPL &INCL &NEEQ)]; subst...
    gen nd_pf'.
    assert (EQD: domain ((h1 ++ (b1, b2, vis, t0) :: h2)) = domain ((h1 ++ (b1, b2, hid, t0) :: h2))).
    repeat rewrite domain_distr; simpl...
    repeat rewrite <-EQD; intros.
    eapply disjoint_commute,new_entries_disjoint...
    eapply sl_pos_repl...
    eapply incl_preserves_max,incl_tran...
    simpl in SL; eapply incl_distr in SL as (SL &_).
    assert (INCL2: incl (domain (hid_proj (h1 ++ (b1, b2, hid, t0) :: h2))) (domain ((h1 ++ (b1, b2, hid, t0) :: h2)))).
    eapply hid_proj_incl...
    rewrite EQD; eapply incl_tran...
    
    right.
    destruct OPT2 as (OPT2 &EQ); subst ff; split; try tauto;
      move OPT2 at bottom.
    assert (EQ: forall f,
               removeEntry (d1, d2) (h1 ++ (b1, b2, f, t0) :: h2) =  removeEntry (d1, d2) h1 ++ (b1, b2, f, t0) :: h2).
    intros; rewrite removeEntry_app_shift2; try tauto;
      try eapply in_g_in_domain...
    rewrite EQ in OPT2. rewrite EQ.
      assert (EQ2: forall f l,
                (ne ++ (d1, d2, f, tt) :: removeEntry (d1, d2) h1) ++ l =
                  ne ++ (d1, d2, f, tt) :: removeEntry (d1, d2) h1 ++ l).
      introv; repeat rewrite <-app_assoc...
    
     erewrite typeEnv_eq_change_flag_removeEntry with (b1 := d1) (b2 := d2) (h := nil) (h1 := ne ++ (d1, d2, vis, tt) :: removeEntry (d1, d2) h1) (f1 := vis);
       repeat erewrite app_nil_l.
    
     rewrite EQ2...
     intros ABS; try inv ABS;
          assert (NDD := pf1);
       erewrite domain_distr in NDD;
       eapply no_dup_iff in NDD as (ND11 &ND22 &DISS);
       eapply disjoint_absurd...

     rewrite EQ2,<-EQ,domain_distr,no_dup_iff.
     destruct IH as [NIL | (qq & REPL &INCLL &NEEQ)]; subst; try rewrite EQ2;
       try erewrite app_nil_l.
     split. simpl...
     split.  eapply no_dup_cons_removeEntry...
     simpl...
     split. eapply newEntries_no_dup;
       try erewrite identif_seclabs_of_dep_relabel...
     eapply Finite.Injective_map_NoDup;
       unfold Finite.Injective;
       try intros [x1 x2] [y1 y2] INJ;
       try simpl in INJ; try inv INJ;
     try assert (x2 = y2); try   lia;
       try subst...
     eapply replication_no_dup...

     split.  eapply no_dup_cons_removeEntry...
      gen nd_pf'.
    assert (EQD: domain ((h1 ++ (b1, b2, vis, t0) :: h2)) = domain ((h1 ++ (b1, b2, hid, t0) :: h2))).
    repeat rewrite domain_distr; simpl...
    repeat rewrite <-EQD; intros.
    eapply disjoint_commute, disjoint_iff with (m := domain _);  try eapply new_entries_disjoint.
    eapply sl_pos_repl...
    eapply incl_preserves_max,incl_tran...
    simpl in SL; eapply incl_distr in SL as (SL &_).
    assert (INCL2: incl (domain (hid_proj (h1 ++ (b1, b2, hid, t0) :: h2))) (domain ((h1 ++ (b1, b2, hid, t0) :: h2)))).
    eapply hid_proj_incl...
    rewrite EQD; eapply incl_tran...
    rewrite EQ,domain_distr.
    assert (EQ3:
             (d1, d2, vis, tt) :: removeEntry (d1, d2) h1 ++ (b1, b2, hid, t0) :: h2 =
               ((d1, d2, vis, tt) :: removeEntry (d1, d2) h1) ++ (b1, b2, hid, t0) :: h2)...
    rewrite EQ3,domain_distr.
    intros; split; try introv INA;
      try eapply in_app_iff in INA as [INA1 | INA2];
      try eapply in_app_iff...
    left.
    case_eq (pair_eq x (d1, d2)); introv PEQ;
      try rewrite <-pairEq_eq in PEQ; try rewrite PEQ;
      simpl...
    right; eapply in_domain_in_g in INA1 as (ff &tt2 &INA1);
      try eapply in_g_in_domain,removeEntry_in;
      try eapply pairEq_neq...
    inv INA1 as [INA2 | CONT]. left...
    eapply in_domain_in_g  in CONT as (ff &tt2 &CONT);
      try eapply in_removeEntry in CONT.
    left; try eapply in_g_in_domain...
     simpl...
     erewrite EQ2 in *... 
    
          
    (*  ne = [] \/
  (exists q : dproc,
     replication (dNu b1 b2 p) (dNu b1 b2 p') q /\
     incl (secLabs q) (secLabs (dNu b1 b2 p)) /\
     ne =
     newEntries (h1 ++ (b1, b2, hid, t0) :: h2) (secLabs (dep_relabel q (domain (h1 ++ (b1, b2, hid, t0) :: h2)) pf))
       (max (domain (h1 ++ (b1, b2, hid, t0) :: h2))))*)
     destruct IH as [NIL | (qq & REPL &INCL &NEEQ)]...
     right; exists qq;repeat split...
     simpl; try eapply incl_appl...

     
     assert (POS2 : pos (secLabs qq)).
     eapply incl_pos...

     (*
 newEntries (h1 ++ (b1, b2, vis, t0) :: h2)
    (secLabs (dep_relabel qq (domain (h1 ++ (b1, b2, vis, t0) :: h2)) nd_pf'))
    (max (domain (h1 ++ (b1, b2, vis, t0) :: h2))) =
  newEntries (h1 ++ (b1, b2, hid, t0) :: h2)
    (secLabs (dep_relabel qq (domain (h1 ++ (b1, b2, hid, t0) :: h2)) nd_pf1))
    (max (domain (h1 ++ (b1, b2, hid, t0) :: h2)))
      *)
     
     erewrite newEntries_iff with (g2 := (b1, b2, hid, t0) :: h1 ++ h2);
       try eapply iff_shift;
       try eassumption.
     erewrite newEntries_iff with (g2 := (b1, b2, vis, t0) :: h1 ++ h2) in NEEQ;
       try eapply incl_pos;
       try eapply iff_shift;
       try eassumption.
     erewrite identif_seclabs_of_dep_relabel,newEntries_remove_var with (x1 := b1) (x2 := b2) (g1 := h1 ++h2)in *;
       try eassumption.
     rewrite domain_distr in *; simpl in *...
     eapply min_max; rewrite domain_distr;simpl;
       erewrite in_app_iff...
     intros ABS; eapply secLabs_of_repl in ABS;
       simpl in ND;
       try eapply no_dup_iff in ND as (_&_&DIS);
       try eapply disjoint_absurd...
     eauto.
     simpl in *; rewrite domain_distr in *; eapply no_dup_app_shift...
       eapply min_max; rewrite domain_distr;simpl;
         erewrite in_app_iff...
       intros ABS; eapply secLabs_of_repl in ABS;
       simpl in ND;
       try eapply no_dup_iff in ND as (_&_&DIS);
         try eapply disjoint_absurd...
       eauto.
       simpl in *; rewrite domain_distr in *;
         try eapply no_dup_app_shift...
       simpl in *; rewrite domain_distr in *;
         try eapply no_dup_app_shift...
       simpl in *; rewrite domain_distr in *;
         try eapply no_dup_app_shift...


    + inverts CONT as EQ2; try inv EQ2.

      * exists d1 d2 hid tt ne.
        split...
        split. try eapply in_app_iff; try right...

        split.
        left...
        destruct EQ as [(EQ &_) | ABS]...

        (*  h' ++ (d1, d2, hid, t') :: h'' = ne ++ (d1, d2, hid, tt) :: removeEntry (d1, d2) (h1 ++ (d1, d2, hid, tt) :: h2) *)
        split; try discriminate.
        eapply typeEnv_eq_change_flag;
          try rewrite removeEntry_app in *;
          try intros ABS...
        destruct IH as [NIL | (qq &REPL &INCL &NEEQ)].
        subst; try inv ABS...

        assert (~In (d1, d2) (domain ne)).
        subst; eapply not_in_newEntries;
          try intros ABS2;
          try rewrite identif_seclabs_of_dep_relabel,in_map_iff in ABS2;
          try destruct ABS2 as ([x1 x2] &EQ2 &ABS2);
          try inv EQ2; 
          unfold fst,snd in *.
       assert (d2 <= max (domain (h1 ++ (d1, d2, vis, tt) :: h2))).
       eapply min_max; rewrite domain_distr;
         rewrite in_app_iff; right...
       assert (x2 = 0). lia.
       subst.
       eapply INCL, SLP2 in ABS2...
       lia.
       lia.

       contradiction.

       rewrite domain_distr in ABS,nd_pf1;
         eapply in_app_iff in ABS as [ABS1 | ABS2].
      simpl in nd_pf1; eapply no_dup_iff in nd_pf1 as (_ &_ &DIS);try eapply disjoint_absurd...
       simpl in nd_pf1; eapply no_dup_iff in nd_pf1 as (_ &ND2 &_); inv ND2...
      
        intuition; try discriminate.

        destruct IH as [EQ2 | (q &REPL &INCL &NEEQ)]...
        right. exists q.
        split...
        split. simpl; eapply incl_appl...

         (*  newEntries (h1 ++ (d1, d2, vis, tt) :: h2) (secLabs (dep_relabel q (domain (h1 ++ (d1, d2, vis, tt) :: h2)) pf1))
    (max (domain (h1 ++ (d1, d2, vis, tt) :: h2))) =
  newEntries (h1 ++ (d1, d2, hid, tt) :: h2) (secLabs (dep_relabel q (domain (h1 ++ (d1, d2, hid, tt) :: h2)) pf))
    (max (domain (h1 ++ (d1, d2, hid, tt) :: h2)))*)
        assert (POS2 : pos (secLabs q)).
         eapply incl_pos...
    
          erewrite newEntries_iff with (g2 := (d1, d2, hid, tt) :: h1 ++ h2);
       try eapply iff_shift;
       try eassumption.
     erewrite newEntries_iff with (g2 := (d1, d2, vis, tt) :: h1 ++ h2) in NEEQ;
       try eapply incl_pos;
       try eapply iff_shift;
       try eassumption.
     erewrite identif_seclabs_of_dep_relabel,newEntries_remove_var with (x1 := d1) (x2 := d2) (g1 := h1 ++h2)in *;
       try eassumption.
     rewrite domain_distr in *; simpl in *...
     eapply min_max; rewrite domain_distr;simpl;
       erewrite in_app_iff...
     intros ABS; eapply secLabs_of_repl in ABS;
       simpl in ND;
       try eapply no_dup_iff in ND as (_&_&DIS);
       try eapply disjoint_absurd...
     eauto.
     simpl in *; rewrite domain_distr in *; eapply no_dup_app_shift...
       eapply min_max; rewrite domain_distr;simpl;
         erewrite in_app_iff...
       intros ABS; eapply secLabs_of_repl in ABS;
       simpl in ND;
       try eapply no_dup_iff in ND as (_&_&DIS);
         try eapply disjoint_absurd...
       eauto.
       simpl in *; rewrite domain_distr in *;
         try eapply no_dup_app_shift...
       simpl in *; rewrite domain_distr in *;
         try eapply no_dup_app_shift...
       simpl in *; rewrite domain_distr in *;
         try eapply no_dup_app_shift...

      * exists d1 d2 ff tt ne.
        split...
        split. try eapply in_app_iff; repeat right...
        split...
       
        (* continue as above *)
         destruct EQ as [(OPT1 &NILL) | OPT2].
        

        left; split...
        eapply typeEnv_eq_change_flag_removeEntry...
    intros ABS; inv ABS.
    rewrite domain_distr in pf; simpl in pf;
      rewrite no_dup_iff in pf; destruct pf as (_ &ND2 &_);
      try inv ND2; try eapply in_g_in_domain in EQ2;
      try contradiction.
    destruct IH as [EQ | (q &REPL &INCL &NEEQ)]; subst...
    gen nd_pf'.
    assert (EQD: domain ((h1 ++ (b1, b2, vis, t0) :: h2)) = domain ((h1 ++ (b1, b2, hid, t0) :: h2))).
    repeat rewrite domain_distr; simpl...
    repeat rewrite <-EQD; intros.
    eapply disjoint_commute,new_entries_disjoint...
    eapply sl_pos_repl...
    eapply incl_preserves_max,incl_tran...
    simpl in SL; eapply incl_distr in SL as (SL &_).
    assert (INCL2: incl (domain (hid_proj (h1 ++ (b1, b2, hid, t0) :: h2))) (domain ((h1 ++ (b1, b2, hid, t0) :: h2)))).
    eapply hid_proj_incl...
    rewrite EQD; eapply incl_tran...
    
    right.
    destruct OPT2 as (OPT2 &EQ); subst ff; split; try tauto;
      move OPT2 at bottom.
    assert (DIFF2: (b1, b2) <> (d1, d2)).
    intros ABS; inv ABS;
      erewrite domain_distr in nd_pf1;
      eapply no_dup_iff in nd_pf1 as (_&ND2&_);
      simpl in ND2; inv ND2;
      eapply in_g_in_domain in EQ2; try contradiction.
    assert (EQ: forall f,
               removeEntry (d1, d2) (h1 ++ (b1, b2, f, t0) :: h2) =  h1 ++ (b1, b2, f, t0) :: removeEntry (d1, d2) h2).
    intros; rewrite removeEntry_app_shift; try tauto;
      try eapply in_g_in_domain;simpl;
      eapply pairEq_neq in DIFF2; try rewrite DIFF2...
    intros ABS;
       erewrite domain_distr in nd_pf1;
      eapply no_dup_iff in nd_pf1 as (_&_ &DIS);
      simpl in DIS;
      try eapply disjoint_absurd...
    try right; try eapply in_g_in_domain in EQ2...
    rewrite EQ in OPT2. rewrite EQ.
    assert (EQ3: forall f l,
                (ne ++ (d1, d2, f, tt) :: h1)++ l =
                  ne ++ (d1, d2, f, tt) :: h1 ++ l).
      introv; repeat rewrite <-app_assoc...
    
     erewrite typeEnv_eq_change_flag_removeEntry with (b1 := d1) (b2 := d2) (h := nil) (h1 := ne ++ (d1, d2, vis, tt) ::  h1) (f1 := vis);
       repeat erewrite app_nil_l.
     try erewrite EQ3...
    
     intuition.
     
     rewrite EQ3,<-EQ,domain_distr,no_dup_iff.
     destruct IH as [NIL | (qq & REPL &INCLL &NEEQ)]; subst; try rewrite EQ2;
       try erewrite app_nil_l.
     split. simpl...
     split.  eapply no_dup_cons_removeEntry...
     simpl...
     split. eapply newEntries_no_dup;
       try erewrite identif_seclabs_of_dep_relabel...
     eapply Finite.Injective_map_NoDup;
       unfold Finite.Injective;
       try intros [x1 x2] [y1 y2] INJ;
       try simpl in INJ; try inv INJ;
     try assert (x2 = y2); try   lia;
       try subst...
     eapply replication_no_dup...

     split.  eapply no_dup_cons_removeEntry...
      gen nd_pf'.
    assert (EQD: domain ((h1 ++ (b1, b2, vis, t0) :: h2)) = domain ((h1 ++ (b1, b2, hid, t0) :: h2))).
    repeat rewrite domain_distr; simpl...
    repeat rewrite <-EQD; intros.
    eapply disjoint_commute, disjoint_iff with (m := domain _);  try eapply new_entries_disjoint.
    eapply sl_pos_repl...
    eapply incl_preserves_max,incl_tran...
    simpl in SL; eapply incl_distr in SL as (SL &_).
    assert (INCL2: incl (domain (hid_proj (h1 ++ (b1, b2, hid, t0) :: h2))) (domain ((h1 ++ (b1, b2, hid, t0) :: h2)))).
    eapply hid_proj_incl...
    rewrite EQD; eapply incl_tran...
    assert (DOMEQ2:
             (domain (h1 ++ (b1, b2, vis, t0) :: h2) =
                (domain (h1 ++ (b1, b2, hid, t0) :: h2)))).
    repeat rewrite domain_distr; simpl...
    rewrite DOMEQ2; eapply in_removeEntry_cons_iff.
    rewrite domain_distr in *; simpl in *...
    simpl; try rewrite domain_distr;
      try eapply in_app_iff; repeat right; eapply in_g_in_domain...
    simpl...
    
     erewrite EQ3 in *... 
    
          
    (*  ne = [] \/
  (exists q : dproc,
     replication (dNu b1 b2 p) (dNu b1 b2 p') q /\
     incl (secLabs q) (secLabs (dNu b1 b2 p)) /\
     ne =
     newEntries (h1 ++ (b1, b2, hid, t0) :: h2) (secLabs (dep_relabel q (domain (h1 ++ (b1, b2, hid, t0) :: h2)) pf))
       (max (domain (h1 ++ (b1, b2, hid, t0) :: h2))))*)
     destruct IH as [NIL | (qq & REPL &INCL &NEEQ)]...
     right; exists qq;repeat split...
     simpl; try eapply incl_appl...

     
     assert (POS2 : pos (secLabs qq)).
     eapply incl_pos...

     (*
 newEntries (h1 ++ (b1, b2, vis, t0) :: h2)
    (secLabs (dep_relabel qq (domain (h1 ++ (b1, b2, vis, t0) :: h2)) nd_pf'))
    (max (domain (h1 ++ (b1, b2, vis, t0) :: h2))) =
  newEntries (h1 ++ (b1, b2, hid, t0) :: h2)
    (secLabs (dep_relabel qq (domain (h1 ++ (b1, b2, hid, t0) :: h2)) nd_pf1))
    (max (domain (h1 ++ (b1, b2, hid, t0) :: h2)))
*)
     erewrite newEntries_iff with (g2 := (b1, b2, hid, t0) :: h1 ++ h2);
       try eapply iff_shift;
       try eassumption.
     erewrite newEntries_iff with (g2 := (b1, b2, vis, t0) :: h1 ++ h2) in NEEQ;
       try eapply incl_pos;
       try eapply iff_shift;
       try eassumption.
     erewrite identif_seclabs_of_dep_relabel,newEntries_remove_var with (x1 := b1) (x2 := b2) (g1 := h1 ++h2)in *;
       try eassumption.
     rewrite domain_distr in *; simpl in *...
     eapply min_max; rewrite domain_distr;simpl;
       erewrite in_app_iff...
     intros ABS; eapply secLabs_of_repl in ABS;
       simpl in ND;
       try eapply no_dup_iff in ND as (_&_&DIS);
       try eapply disjoint_absurd...
     eauto.
     simpl in *; rewrite domain_distr in *; eapply no_dup_app_shift...
       eapply min_max; rewrite domain_distr;simpl;
         erewrite in_app_iff...
       intros ABS; eapply secLabs_of_repl in ABS;
       simpl in ND;
       try eapply no_dup_iff in ND as (_&_&DIS);
         try eapply disjoint_absurd...
       eauto.
       simpl in *; rewrite domain_distr in *;
         try eapply no_dup_app_shift...
       simpl in *; rewrite domain_distr in *;
         try eapply no_dup_app_shift...
       simpl in *; rewrite domain_distr in *;
         try eapply no_dup_app_shift...
        
        
    + (*  incl (secLabs p) (domain (hid_proj (h1 ++ (b1, b2, vis, t0) :: h2)))*)
      simpl in SL; rewrite hid_proj_app in *; simpl in *;
        rewrite domain_distr in *; simpl in SL.
      eapply incl_Add_inv with (a := (b1, b2))
                               (v := domain (hid_proj h1) ++ (b1, b2) :: domain (hid_proj h2)).
      try introv ABS;
        eapply no_dup_iff in ND as (_ &_ &DIS);
        try eapply disjoint_absurd...
      eapply incl_app_inv in SL as (I1 &I2).
      assert (EQ: (b1, b2) :: secLabs p =
                    [(b1, b2)] ++ secLabs p)...
      rewrite EQ.
      erewrite incl_distr; split...
      eapply Add_app...
    + (*  NoDup (secLabs (dNu b1 b2 p))*)
     simpl in ND; eapply no_dup_iff in ND as (nd &_&_)... 
    + (* In (a1, a2, vis, Chan un io t) (h1 ++ (b1, b2, vis, t0) :: h2) *)
      assert ((a1, a2) <> (b1, b2)).
      erewrite domain_distr in nd_pf1;
        eapply no_dup_iff in nd_pf1 as (ND1 &ND2 &DIS);
        simpl in DIS.
      intros ABS; inv ABS; eapply in_app_iff in IN as [ABS1 | [ABS | ABS2]].
      eapply in_g_in_domain in ABS1;
        try eapply disjoint_absurd...
      inv ABS...
      simpl in ND2; inv ND2...
      
      assert (TYP: typeOf (h1 ++ (b1, b2, vis, t0) :: h2) (a1, a2) (Chan un io t)).
      eapply typeOf_hide_app...
      assert (FYP: flagOf (h1 ++ (b1, b2, vis, t0) :: h2) (a1, a2) hid).
      eapply flagOf_hide_app...
      inv TYP; inv FYP.
      assert (f = hid).
      eapply flag_of_map with (g := h1 ++ (b1, b2, vis, t0) :: h2)...
      subst...
      Unshelve.
      all:eauto.

  
Qed.

(*Lemma lts_un_input_action_newEntries_secLabsh:
  forall (*g p a1 a2 b1 b2 r g1 p1 nd_pf k pol t rp,*)
    g p a1 a2 b1 b2 g1 p1 nd_pf pol t rp,
    In (a1, a2, hid, Chan un pol t) g ->
    lts g p (aIn a1 a2 b1 b2) g1 p1 nd_pf ->
    (*g1 = k ++ (b1, b2, vis, r) :: removeEntry (b1, b2) g ->*)
    replication p p1 rp ->
    incl (secLabs rp) (secLabs p).
Proof with eauto.
  intros
    g p a1 a2 b1 b2 g1 p1 nd_pf pol t rp IN LTS REPL.
  generalize dependent rp.
  dependent induction LTS...
  - intros. simpl. eapply incl_appr,IHLTS...
    inversion REPL; subst...
    assert (False); try eapply replication_diff;eauto; try contradiction.
  - assert (ABS: Chan lin inp t0 =  Chan un pol t).
    eapply type_of_map with (g := g)...
    inversion ABS.
  - intros. 
    inversion REPL.
  - intros. inversion REPL; subst.
    simpl...
  - introv REPL; inv REPL; simpl; eapply incl_appl.
      try eapply IHLTS; try eapply in_app_iff in IN as [IN | CONT];
      try eapply in_app_iff... try inv CONT; try inv H0; try discriminate...
    repeat right...
Qed.
 *)

Lemma typeOf_hide_app2 h1 h2 c1 c2 f1 f2 t1 a1 a2 t:
  typeOf (h1 ++ (c1, c2, f1, t1) :: h2) (a1, a2) t ->
  typeOf (h1 ++ (c1, c2, f2, t1) :: h2) (a1, a2) t.
Proof with eauto.
  introv TYP; try inverts TYP as IN;
    try eapply in_app_iff in IN as [IN1 | [ABS | IN2]];
    try econstructor; try eapply in_app_iff;
    try inv ABS; try contradiction...
  repeat right...
Qed.

Lemma lts_un_tau_action_newEntries_secLabsh:
  forall g p a1 a2 g1 p1 nd_pf pol t rp,
    typeOf g (a1,a2) (Chan un pol t) ->
    lts g p (aTau a1 a2) g1 p1 nd_pf ->
    replication p p1 rp ->
    incl (secLabs rp) (secLabs p).
Proof with eauto.
  intros g p a1 a2 g1 p1 nd_pf pol t rp
    IN LTS REPL.
  generalize dependent rp.
  dependent induction LTS...
  - intros. simpl. eapply incl_appr,IHLTS...
    inversion REPL; subst...
    assert (False); try eapply replication_diff;eauto; try contradiction.
  - assert (ABS: Chan lin io t0 =  Chan un pol t).
    eapply type_of_map with (g := g)...
    inversion ABS.
  - assert (ABS: Chan lin io t0 =  Chan un pol t).
    eapply type_of_map with (g := g)...
    inversion ABS.
  - intros. clear IHLTS1 IHLTS2.
    inversion REPL; subst.
    eapply replication_not_out in H9...
    contradiction.
    eapply lts_un_input_action_newEntries_secLabs with (rp := rp) in LTS2. simpl; eapply incl_appl...
    subst g' g0. right. eapply removeEntry_in...
    assumption.
  - intros. inversion REPL; subst.
    eapply lts_un_input_action_newEntries_secLabs with (rp := rp) in LTS2. simpl; eapply incl_appl...
    subst g' g0. right. eapply removeEntry_in...
    assumption.
  - Case hide.
    assert (HIDE:
             lts (h1 ++ (b1, b2, hid, t0) :: h2) (dNu b1 b2 p) (aTau a1 a2) (h' ++ (b1, b2, hid, t') :: h'') (dNu b1 b2 p')
               pf)...

    introv REPL; inv REPL; simpl; eapply incl_appl.

  
   eapply IHLTS; try eassumption; try tauto.
   eapply typeOf_hide_app2...
   Unshelve.
   all:eauto.
Qed.

Lemma lts_un_tau_action_newEntries_1k p g a1 a2 c1 c2 t r p1 pf q:
   sl_pos p ->
    incl (secLabs p) (domain (hid_proj g)) ->
    NoDup (secLabs p) ->
    (a1, a2) <> (c1, c2) ->
   typeOf g (a1, a2) (Chan un io t)->
    In (c1, c2) (domain g) -> 
    lts g p (aTau a1 a2) (nil ++ (c1, c2, vis, r) :: removeEntry (c1, c2) g) p1 pf ->
    replication p p1 q ->
    secLabs (dep_relabel q (domain g) pf) = nil.
 Proof with eauto.
    introv SLP INCL ND  DIFF INa INb LTS REPL.
    generalize dependent q.
    dependent induction LTS.
    - intros; eapply IHLTS... simpl in ND. eapply no_dup_distr in ND; intuition.
      simpl in INCL. eapply incl_distr in INCL; intuition.
      inversion REPL; subst... assert (False); try eapply replication_diff;eauto; try contradiction.
    - intros; clear IHLTS1 IHLTS2.
      assert (ABS: Chan lin io t0 = Chan un io t).
      eapply type_of_map with (g  := g)...
      inversion ABS.
    - 
      
      intros; clear IHLTS1 IHLTS2.
      assert (ABS: Chan lin io t0 = Chan un io t).
      eapply type_of_map with (g := g)...
      inversion ABS.
    -   intros; clear IHLTS1 IHLTS2.
        assert (nd_pf: NoDup (domain g')).   
        subst g' g0; eapply no_dup_cons_removeEntry...

        case_eq (pair_eq (b1, b2) (c1, c2)); intros EQ;
          try rewrite <-pairEq_eq in EQ.
   
        inversion EQ; subst c1 c2.

        assert (REPL1: replication q1 q2 q).
        inversion REPL; subst...
        assert (False). eapply replication_not_out... contradiction.
        eapply lts_un_input_action_newEntries_secLabs  with (rp := q) in LTS2 as INCLRP; try eassumption.
        assert (SLP2: sl_pos q).
        unfold sl_pos, pos in *; intros x1 x2; simpl in SLP; specialize
                                                               SLP with x1 x2; intuition.
        assert (INCL1: incl (secLabs q1) (domain g)).
        assert (incl (domain (hid_proj g)) (domain g)) by eapply hid_proj_incl...
        simpl in INCL. eapply incl_distr in INCL as (INCL1 & INCL2); eapply incl_tran...
        
       
        
        subst g'.
        eapply lts_un_input_action_newEntries_2 with (k := nil) (q := q) (pf := nd_pf)in LTS2 as K; try eassumption.
        subst g0.
        assert (SLNIL: (secLabs (dep_relabel q (domain ((b1, b2, vis, s1) :: removeEntry (b1, b2) g)) nd_pf)) = nil). eapply secLabs_nil...
        erewrite identif_seclabs_of_dep_relabel,max_same_domain with (l := domain g),<-identif_seclabs_of_dep_relabel in SLNIL...
        
        
        subst g0; simpl; rewrite pairEq_eq_true...
        eauto.
        simpl in ND; eapply no_dup_iff in ND; intuition.
        simpl...
        subst g' g0; right; eapply removeEntry_in...

        rewrite <-pairEq_neq in EQ.
        assert (False).
        inv H as (TS &TP &ISUN).
        eapply lts_un_input_action in LTS2 as (k &DIS &ABS).
        destruct k. inv ABS; try contradiction.
        inv ABS; subst g'.
        eapply disjoint_absurd...
        simpl...
        eapply in_domain_in_g in INb as (ff &tt &INb);
          simpl; right; subst g0; eapply in_g_in_domain,removeEntry_in...
        subst g' g0; econstructor; right;
          eapply removeEntry_in.
        eapply nonRecActions1...
        eauto.
        subst g' g0; econstructor...
        assert (EQ2: Chan un io t = Chan un io t0).
        eapply type_of_map with (g := g)...
        inv EQ2.
        eapply type_plus_comm...
        eauto.
        eapply incl_preserves_max; subst g' g0.
        assert (incl (secLabs q1) (domain g)).
        eapply incl_tran,hid_proj_incl...
        simpl in INCL; eapply incl_app_inv in INCL; intuition.
        eapply incl_iff...
        contradiction.
        

    - Case hide.
      assert (HIDE: lts (h1 ++ (b1, b2, hid, t0) :: h2) (dNu b1 b2 p) (aTau a1 a2) (h' ++ (b1, b2, hid, t') :: h'')(dNu b1 b2 p') pf).
      eapply hide...

      introv REPL.
      assert (REPL2: replication p p' q).
      inv REPL...

      assert (EQD: domain (h1 ++ (b1, b2, vis, t0) :: h2) =
                        domain (h1 ++ (b1, b2, hid , t0) :: h2)).
      repeat (simpl; try  rewrite domain_distr)...
      
      case_eq (pair_eq (b1,b2) (c1,c2)); intros PEQ;
        try rewrite <-pairEq_eq in PEQ; inversion PEQ;
        try subst c1 c2.

      assert (hid = vis).
      assert (ABS: In (b1,b2,hid,t')( (b1, b2, vis, r) :: removeEntry (b1, b2) (h1 ++ (b1, b2, hid, t0) :: h2))).
      simpl in x; rewrite <-x; eapply in_app_iff; try right...
      inv ABS as[OK | ABS2]; try inv OK; try tauto.
      assert (~ In (b1, b2, hid, t') (removeEntry (b1, b2) (h1 ++ (b1, b2, hid, t0) :: h2))).
      eapply no_dup_not_in_removeEntry...
      contradiction.

      discriminate.
      (*
*   assert (ND2 := ND).
          simpl in ND; eapply no_dup_iff in ND as (IH &_ &_); eapply IHLTS with  (r := t')in IH; clear IHLTS;
            try eassumption.
          assert (pf' := pf1).
     eapply lts_rewrite_pf with (pf1 := pf') in LTS.
     gen pf1; rewrite EQD; intros.
     erewrite dep_relabel_rewrite_pf...
(*  incl (secLabs p) (domain (hid_proj (h1 ++ (b1, b2, vis, t0) :: h2)))*)
     rewrite hid_proj_app in *; simpl in *.
     eapply incl_distr in INCL as (INCL &_).
     unfold incl in*; intros a IN; assert (IN2 := IN);
       try eapply INCL in IN;
       rewrite domain_distr in *;
       try eapply in_app_iff in IN as [EQ | CONT];
       try eapply in_app_iff...
     unfold domain in CONT; fold domain in CONT;
       inversion CONT;subst...
     assert (False).
     eapply disjoint_absurd...
     contradiction.
     eauto.
(*   In (c1, c2) (domain (h1 ++ (b1, b2, vis, t0) :: h2))
 *)
     simpl in *; rewrite domain_distr in *...
     eapply typeOf_hide_app2; try eassumption...
     try tauto...
     eapply type_of_hideapp2...
     (*  In (a1, a2, vis, Chan un io t) (h1 ++ (b1, b2, vis, t0) :: h2)*)
     eapply in_app_iff in INa as [IN | CONT]; eapply in_app_iff...
     inversion CONT as [ABS3|CONT3]; try inv ABS3; try discriminate.
     repeat right...

      (*  h' ++ (b1, b2, vis, t') :: h'' ~= [] ++ (b1, b2, vis, ?r) :: removeEntry (b1, b2) (h1 ++ (b1, b2, vis, t0) :: h2)*)
     assert ( ~ In (b1, b2) (domain h1)).
     intros ABS.
     assert (ABS2 := ABS).
     eapply in_domain_in_g in ABS2 as (ff &tt &ABS2).
     rewrite domain_distr in pf; eapply no_dup_disjoint in pf; eapply disjoint_absurd; try eapply in_g_in_domain...


     destruct h'.
     

     inv x; repeat rewrite removeEntry_app_shift;simpl;
       try rewrite pairEq_eq_true...

     inv x.
     eapply lts_no_dup in LTS...
     rewrite domain_distr in LTS;
       eapply no_dup_disjoint in LTS;
       try eapply disjoint_absurd with (x := (b1,b2));
     simpl...
     simpl...
     simpl...
     eapply incl_incl2...
     simpl in *; repeat rewrite domain_distr in *;
       simpl...
     assert (INCL2: incl (secLabs p) (domain ((h1 ++ (b1, b2, hid, t0) :: h2)))).
     eapply incl_tran. eapply incl_distr in INCL as [INCL _]...
     try eapply hid_proj_incl...
     rewrite domain_distr in *; simpl in *...

     eapply incl_preserves_max.
      assert (INCL2: incl (secLabs p) (domain ((h1 ++ (b1, b2, hid, t0) :: h2)))).
     eapply incl_tran. eapply incl_distr in INCL as [INCL _]...
     try eapply hid_proj_incl...
     rewrite domain_distr in *; simpl in *...
       *)

      
      * assert (ND2 := ND).
      simpl in ND; eapply no_dup_iff in ND as (IH &_ &_); eapply IHLTS in IH; clear IHLTS; try eassumption.

      (* secLabs (dep_relabel q (domain (h1 ++ (b1, b2, hid, t0) :: h2)) pf) = []*)
      assert (pf' := pf1).
      eapply lts_rewrite_pf with (pf1 := pf') in LTS;
        try eassumption.
     gen pf1; rewrite EQD; intros.
     erewrite dep_relabel_rewrite_pf...
(*  incl (secLabs p) (domain (hid_proj (h1 ++ (b1, b2, vis, t0) :: h2)))*)
     rewrite hid_proj_app in *; simpl in *.
     eapply incl_distr in INCL as (INCL &_).
     unfold incl in*; intros a IN; assert (IN2 := IN);
       try eapply INCL in IN;
       rewrite domain_distr in *;
       try eapply in_app_iff in IN as [EQ | CONT];
       try eapply in_app_iff...
     unfold domain in CONT; fold domain in CONT;
       inversion CONT;subst...
     assert (False).
     eapply disjoint_absurd...
     contradiction.
     eauto.
(*   In (c1, c2) (domain (h1 ++ (b1, b2, vis, t0) :: h2))
 *)
     simpl in *; rewrite domain_distr in *...
     eapply typeOf_hide_app2...
     tauto.
     
     (*  h' ++ (b1, b2, vis, t') :: h'' ~= [] ++ (c1, c2, f, ?r) :: removeEntry (c1, c2) (h1 ++ (b1, b2, vis, t0) :: h2)*)
     rewrite <-pairEq_neq in PEQ;
       try erewrite typeEnv_eq_change_flag_removeEntry...
 Qed.
 #[global] Hint Resolve removeEntry_length_01.
 
#[global] Hint Resolve removeEntry_length_02.
  Lemma lts_un_tau_action_newEntries_1hk:
  forall (g : typeEnv) (p : dproc) (a1 a2 c1 c2 : name) (r t : piType) 
    (g1 : typeEnv) (p1 : dproc) (pf : NoDup (domain g)) (q : dproc)
    (k : list (name * name * flag * piType)),
   sl_pos p ->
    incl (secLabs p) (domain (hid_proj g)) ->
    NoDup (secLabs p) ->
    (a1, a2) <> (c1, c2) ->
    typeOf g (a1, a2) (Chan un io t) ->
    In (c1, c2) (domain g) ->
    lts g p (aTau a1 a2) ( (c1, c2, hid, r) :: removeEntry (c1, c2) (nil ++ (c1, c2, vis, r) :: removeEntry (c1, c2) g)) p1 pf ->
    replication p p1 q ->
    secLabs (dep_relabel q (domain g) pf) = nil.
 Proof with eauto.
    intros g p a1 a2 c1 c2 r t g1 p1 pf q k
           SLP INCL ND  DIFF INa INb LTS REPL.
    generalize dependent q.
    dependent induction LTS.
    - intros; eapply IHLTS... simpl in ND. eapply no_dup_distr in ND; intuition.
      simpl in INCL. eapply incl_distr in INCL; intuition.
      inversion REPL; subst... assert (False); try eapply replication_diff;eauto; try contradiction.
     -   intros; clear IHLTS1 IHLTS2.
        assert (nd_pf: NoDup (domain g')).   
        subst g' g0; eapply no_dup_cons_removeEntry...

        case_eq (pair_eq (b1, b2) (c1, c2)); introv EQ;
          try rewrite <-pairEq_eq in EQ.
            inversion EQ; subst c1 c2.
        inversion H3. inversion H4.
        simpl in H4; rewrite pairEq_eq_true in H4.
        eapply no_dup_not_in_removeEntry with (a := (b1, b2)) (f := vis) (t := s) in  pf as ABS.
        contradiction.
        
        rewrite <-pairEq_neq in EQ.
        assert (REPL1:  replication q1 q2 q).
        inv REPL...
        assert (False).
        try eapply replication_not_out...
        contradiction.
        move LTS2 at bottom.
        simpl in LTS2; rewrite pairEq_eq_true in LTS2.
        inv H as (TS &TP &ISUN).
        
        assert (ABS:
                 exists k,
                   disjoint (domain k) (domain g') /\
                     ((c1, c2, hid, r) :: removeEntry (c1, c2) g) = k ++ (b1, b2, vis, s) :: removeEntry (b1, b2) g').
        eapply lts_un_input_action with (t := t0); subst g' g0; try econstructor.
        eauto.
        right; eapply removeEntry_in...
        eauto.
        eapply type_plus_comm...
        assert (SLP2:=SLP);
       eapply sl_pos_par_l in SLP;
         eapply sl_pos_par_r in SLP2; unfold sl_pos; simpl;introv IN; eapply in_app_iff in IN as [IN1 | IN2]...
        eapply incl_preserves_max, incl_tran with (m := domain (hid_proj g))...
        simpl in *; eapply incl_distr in INCL as [INCL1 INCl2]; introv IN; try eapply in_app_iff  in IN as [IN1 | IN2]...
        eapply incl_iff with (m1 := domain g);
          try eapply hid_proj_incl;
          try eapply in_removeEntry_cons_iff,in_g_in_domain...

        destruct ABS as (k' &DIS &EQ').
        subst g' g0; simpl in EQ'; try rewrite pairEq_eq_true in EQ'.
        assert (LEN1: length ((c1, c2, hid, r) :: removeEntry (c1, c2) g) =
                        length(k' ++ (b1, b2, vis, s) :: removeEntry (b1, b2) g)).
        rewrite EQ'...
        assert (LEN2: S(length (removeEntry (c1, c2) g)) =
                       S(length(removeEntry (b1, b2) g))).
        repeat erewrite removeEntry_length_0...
        assert (NIL: length k' = 0).
        rewrite app_length in LEN1; simpl in LEN1; try lia.
        assert (k'=nil). try eapply length_zero_iff_nil...
        subst k'.
        inv EQ'...

     -   intros; clear IHLTS1 IHLTS2.
         rewrite pairEq_eq_true in x.
        assert (nd_pf: NoDup (domain g')).   
        subst g' g0; eapply no_dup_cons_removeEntry...
     
        simpl in INCL. eapply incl_distr in INCL as (INCL1 &INCL2).
        assert (incl (domain (hid_proj g)) (domain g)) by eapply hid_proj_incl...

        assert (REPL1: replication q1 q2 q).
        inversion REPL; subst...
        eapply lts_un_input_action_newEntries_secLabs  with (rp := q) in LTS2 as INCLRP.
        assert (SLP2: sl_pos q).
        unfold sl_pos, pos in *; intros x1 x2; simpl in SLP; specialize
                                                               SLP with x1 x2; intuition.
        assert (INCL3: incl (secLabs q1) (domain g)).    assert (incl (domain (hid_proj g)) (domain g)) by eapply hid_proj_incl... eapply incl_tran...
        
        destruct H as (_ & TP &_). eapply type_plus_comm in TP.
        assert (EQ:  Chan un io t0 =  Chan un io t).
        eapply type_of_map with (g := g)...
        inversion EQ; subst. clear EQ.
        
        eapply lts_un_input_action with (r := r) in LTS2 as KK. destruct KK as (ne & DIS &GEQ).
        simpl in GEQ; rewrite pairEq_eq_true in GEQ.

       
        eapply lts_un_input_action_newEntries_2 with (k := nil) (q := q) (pf := nd_pf) (r := r)in LTS2 as K...
        subst g' g0.
        assert (SLNIL: (secLabs (dep_relabel q (domain ((c1, c2, ill, s1) :: removeEntry (c1, c2) g)) nd_pf)) = nil). eapply secLabs_nil...
        erewrite identif_seclabs_of_dep_relabel,max_same_domain with (l := domain g),<-identif_seclabs_of_dep_relabel in SLNIL...
        subst g' g0; simpl; rewrite pairEq_eq_true...

        assert ( ne = nil).
        subst g3.
        destruct ne as [|[[[d1 d2] f] t2] l]...
        simpl in x.
        case_eq (pair_eq (d1, d2) (c1, c2)).
        intros EQ; rewrite EQ in x.
        assert (LEN : List.length (l ++ (c1, c2, vis, r) :: removeEntry (c1, c2) g) = List.length (removeEntry (c1, c2) g)). rewrite x...
        erewrite app_length  in LEN; simpl in LEN.
        lia.
        intros NEQ;  rewrite NEQ in x.
        assert (LEN : List.length ((d1, d2, f, t2)
                                     :: removeEntry (c1, c2) (l ++ (c1, c2, vis, r) :: removeEntry (c1, c2) g)) = List.length (removeEntry (c1, c2) g)). rewrite x...
        simpl in LEN.  
        assert (LEN2:
                  List.length
                    (removeEntry (c1, c2) (l ++ (c1, c2, vis, r) :: removeEntry (c1, c2) g)) =
                  List.length
                    (removeEntry (c1, c2) l) + List.length( (c1, c2, vis, r) :: removeEntry (c1, c2) g) \/
                  List.length
                    (removeEntry (c1, c2) (l ++ (c1, c2, vis, r) :: removeEntry (c1, c2) g)) =
                  List.length l +
                  List.length( removeEntry (c1, c2)((c1, c2, vis, r) :: removeEntry (c1, c2) g)))...
        destruct LEN2 as [ABS1 | ABS2].
        simpl in ABS1; rewrite ABS1 in LEN.
        lia.
        simpl in ABS2; rewrite ABS2,pairEq_eq_true in LEN.
        lia.
        subst...
        simpl in ND; eapply no_dup_iff in ND; intuition.
        simpl...
        all:subst g' g0|| eauto...
        assert (incl (domain (hid_proj g)) (domain g)) by eapply hid_proj_incl...
        eapply proposition27.incl_preserves_max,incl_tran, incl_iff with (m1 :=domain g)...
        right. eapply removeEntry_in...
     - Case hide.
       assert (HIDE: 
                lts  (h1 ++ (b1, b2, hid, t0) :: h2) (dNu b1 b2 p) (aTau a1 a2) (h' ++ (b1, b2, hid, t') :: h'') (dNu b1 b2 p') pf).
       eapply hide...
       
       introv REPL.
      assert (REPL2: replication p p' q).
      inv REPL...

     
  simpl in INCL; eapply incl_app_inv in INCL as (INCL1 &INCL2).
  simpl in ND; eapply no_dup_iff in ND as (ND1 &ND2 &DIS).

   case_eq (pair_eq (b1,b2) (c1,c2)); intros PEQ;
     try rewrite <-pairEq_eq in PEQ; inv PEQ.

   

    * clear IHLTS.
         
         assert (h' = nil).
         destruct h'...
         inv x; rewrite pairEq_eq_true in *.
         eapply lts_no_dup in LTS...

         rewrite domain_distr in LTS.
       erewrite no_dup_iff with (l1 := domain ((c1, c2, hid, r) :: h')) in LTS. destruct LTS as (_&_&DIS2). 
       try eapply disjoint_absurd with (x := (c1,c2));
         try eapply in_g_in_domain...
     eapply incl_incl2...
     assert (INCL3: incl (secLabs p) (domain ((h1 ++ (c1,c2, hid, t0) :: h2)))).
     eapply incl_tran... 
     try eapply hid_proj_incl...
     rewrite domain_distr in *; simpl in *...

     eapply incl_preserves_max.
     eapply incl_tran... 
     try eapply hid_proj_incl...
     repeat rewrite hid_proj_app;
       repeat rewrite domain_distr; simpl; introv IN;
       eapply in_app_iff in IN as [IN | CONT];
     eapply in_app_iff...
     left; try eapply hid_proj_incl...
     inv CONT; right...
     right;try eapply hid_proj_incl...
       
     subst h'.

     inv x; try rewrite pairEq_eq_true in *.
     assert (IH: secLabs (dep_relabel q (domain (h1 ++ (c1, c2, vis, t0) :: h2)) pf1) = []).
     move LTS at bottom.
     assert (NIN : ~In (c1, c2) (domain h1)).
     introv ABS.
     assert (pf' := pf1);
       rewrite domain_distr,no_dup_iff in pf';
       destruct pf' as (_&_&DIS2);
       simpl in DIS2;
       eapply disjoint_absurd...
     rewrite removeEntry_app_shift in LTS; simpl in LTS;
     try rewrite pairEq_eq_true in LTS...
     erewrite lts_un_tau_action_newEntries_1k with (p := p)
                                                   (p1 := p');
       try assumption; try tauto.
     eauto.
     
     rewrite hid_proj_app,domain_distr in *; simpl in *;
       introv IN; assert (IN2 := IN); eapply INCL1 in IN;
       eapply in_app_iff in IN; inv IN as [IN3 | CONT];
       eapply in_app_iff...
     inv CONT.  try eapply disjoint_absurd...
     right...

     eauto.

     eapply typeOf_hide_app...

     rewrite domain_distr,in_app_iff; simpl...

  
    (*  rewrite domain_distr in *; simpl in *; eapply in_app_iff in INa; inv INa as [INa2 | CONT]; eapply in_app_iff...
     inv CONT; try inv H0; try contradiction.
     repeat right...
     simpl in *; try rewrite pairEq_eq_true in *.
*)
      rewrite removeEntry_app_shift; simpl;
     try rewrite pairEq_eq_true... 

      assert (pff1 := pf1).
      assert (pff := pf).
      erewrite dep_relabel_rewrite_pf with (pf1 := pff).
      erewrite dep_relabel_rewrite_pf 
        with (pf1 := pff1) in IH.
      assert (DOMEQ: domain (h1 ++ (c1, c2, vis, t0) :: h2) = domain (h1 ++ (c1, c2, hid, t0) :: h2)).
       repeat rewrite domain_distr; simpl...
      gen pff pff1. rewrite DOMEQ;
        intros.
      erewrite dep_relabel_rewrite_pf...
      * 
      
    
      assert (IH: secLabs (dep_relabel q (domain (h1 ++ (b1, b2, vis, t0) :: h2)) pf1) = []).
      eapply IHLTS; clear IHLTS; try eassumption.
     rewrite hid_proj_app,domain_distr in *; simpl in *.
     introv IN; assert (IN2 := IN); eapply INCL1,in_app_iff in IN;
       try destruct IN as [IN | CONT]; try eapply in_app_iff...
     inv CONT.
     try eapply disjoint_absurd...
     right...
     eauto.
     rewrite domain_distr in *; simpl in *; eapply in_app_iff in INb; inv INb as [INb2 | CONT]; eapply in_app_iff...
     eapply typeOf_hide_app2; try eassumption.
     tauto.
(*     rewrite domain_distr in *; simpl in *; eapply in_app_iff in INa; inv INa as [INa2 | CONT]; eapply in_app_iff...
     inv CONT; try inv H0; try contradiction.
     repeat right...
*)

     simpl in *; try rewrite pairEq_eq_true in *.
     erewrite typeEnv_eq_change_flag_removeEntry with (h := nil)...
     simpl...
     eapply pairEq_neq in H1...
     
     
      (* secLabs (dep_relabel q (domain (h1 ++ (b1, b2, hid, t0) :: h2)) pf) = []*)
      assert (EQD: domain (h1 ++ (b1, b2, vis, t0) :: h2) =
                        domain (h1 ++ (b1, b2, hid , t0) :: h2)).
      repeat (simpl; try  rewrite domain_distr)...
      assert (pf' := pf1).
     eapply lts_rewrite_pf with (pf1 := pf') in LTS.
     gen pf1; rewrite EQD; intros.
     erewrite dep_relabel_rewrite_pf...
 Qed.
 
 #[global] Hint Resolve lts_un_tau_action_newEntries_1k
   lts_un_tau_action_newEntries_1hk.

  Lemma lts_un_tau_action_newEntries_2h:
  forall (g : typeEnv) (p : dproc) (a1 a2 b1 b2 : name) (r t : piType) 
    (g1 : typeEnv) (p1 : dproc) (pf: NoDup (domain g)) (q : dproc)
    (k : list (name * name * flag * piType)),
   sl_pos p ->
    incl (secLabs p) (domain (hid_proj g)) ->
    NoDup (secLabs p) ->
    In (a1, a2, hid, Chan un io t) g ->
    In (b1, b2) (domain g) -> 
    lts g p (aTau a1 a2) g1 p1 pf ->
  (g1 = k ++ (b1, b2, vis, r) :: removeEntry (b1, b2) g \/
   g1 = (b1, b2, hid, r):: removeEntry (b1, b2) (k ++ (b1, b2, vis, r) :: removeEntry (b1, b2) g))
   ->
  replication p p1 q ->
  k = newEntries g (secLabs (dep_relabel q (domain g) pf)) (max (domain g)).
  Proof with eauto.
    
    introv
      SLP INCL ND  INa INb LTS  EQ REPL.
    
    eapply lts_after_tau_unh with (nd_pf1 := pf) in LTS as K...

    assert (INCL1: incl (secLabs p) (domain g)).    assert (incl (domain (hid_proj g)) (domain g)) by eapply hid_proj_incl... eapply incl_tran...
    assert (MAX: max (secLabs p) <= max (domain g)).
    eapply proposition27.incl_preserves_max in INCL.
    assert (INCL2: incl (domain (hid_proj g)) (domain g)) by eapply hid_proj_incl...
    eapply proposition27.incl_preserves_max in INCL2.
    lia.
    

    
    destruct K as
      [c1 [c2 [f [tb [ne [DIFF [INc [G1EQ NEEQ]]]]]]]].
    assert (HYP: S(length (removeEntry (c1, c2) g)) = S(length (removeEntry (b1, b2) g))).
    
    repeat rewrite removeEntry_length_0; try assumption;
      try eapply in_g_in_domain...

        assert (LEN: length (removeEntry (c1, c2) g) = length (removeEntry (b1, b2) g)) by lia.

    
    destruct EQ as [OPT1 | OPT2].
    destruct G1EQ as [(OPT3 &NILL) | (OPT4 & EQF)].
    rewrite OPT3 in OPT1.
    assert (EQ: (c1, c2, f, tb) = (b1, b2, vis, r) /\ ne = k).
    eapply length_inv_tl...
    destruct EQ as [EQ1 EQ2]; inv EQ1.
    inv NEEQ.
    erewrite lts_un_tau_action_newEntries_1k...
    
    destruct H as (rp &REPL2 &INCLQ &NE).
    assert (q = rp). eapply replication_unique...
    subst; erewrite dep_relabel_rewrite_pf...

    rewrite OPT4 in OPT1; subst f.
    destruct NEEQ as [NENIL | (rp &REPL2 &INCLQ &NE)]; subst.
    simpl in OPT1; rewrite pairEq_eq_true in OPT1.

    assert (k = nil).
    assert (LEN2: (List.length ( (c1, c2, hid, tb) :: removeEntry (c1, c2) g) =
                    List.length (k ++ (b1, b2, vis, r) :: removeEntry (b1, b2) g))).
    assert (OPT' := OPT1).
    rewrite OPT'...
    repeat rewrite app_length in LEN2; simpl in LEN2...
    assert (List.length k = 0) by lia.
    eapply length_zero_iff_nil...
    subst.

    erewrite lts_un_tau_action_newEntries_1hk;
      try eapply in_g_in_domain...

    (* HERE *)
    assert (q = rp).
    eapply replication_unique...
    subst q.

    assert (nd_pf2 : NoDup (domain (((c1, c2, hid, tb)
           :: removeEntry (c1, c2)
                (newEntries g (secLabs (dep_relabel rp (domain g) pf)) (max (domain g)) ++
                            (c1, c2, vis, tb) :: removeEntry (c1, c2) g))))).
    eapply lts_no_dup.lts_no_dup...
    eapply proposition27.incl_incl2...
    
    remember (newEntries g (secLabs (dep_relabel rp (domain g) pf))
                         (max (domain g))) as ne.
    assert (~In (c1,c2) (domain ne)).
    eapply removeEntry_app_notIn...
    erewrite removeEntry_app_shift in OPT1. simpl in OPT1.
    rewrite pairEq_eq_true in OPT1.

    
    
    assert (ABS: (c1, c2, hid, tb) :: ne = k ++ (b1, b2, vis, r):: nil).
    eapply  length_inv_tl_2 with (l3 := removeEntry (c1, c2) g) (l4 := removeEntry (b1, b2) g)...
    erewrite <-app_comm_cons...
    repeat rewrite OPT1,cons_app; intuition.

    assert (L1: S (length (removeEntry (b1, b2) g)) = length g).
    eapply removeEntry_length_0...
    assert (L2: S (length (removeEntry (c1, c2) g)) = length g).
    eapply removeEntry_length_0, in_g_in_domain...

    assert (k = nil).
    destruct k...
    inv ABS.
    assert (DIS:disjoint (domain g) (domain (newEntries g (secLabs (dep_relabel rp (domain g) pf)) (max (domain g))))).
    eapply new_entries_disjoint...
    eapply sl_pos_repl...
    eapply incl_preserves_max, incl_tran;
      try eapply secLabs_of_repl...
    rewrite H2 in DIS.
    eapply disjoint_absurd...
    rewrite domain_distr,in_app_iff; right;simpl...

    subst k.
    assert (ne = nil).
    assert (LEN3 : List.length( (c1, c2, hid, tb) :: ne) =
                    List.length([] ++ [(b1, b2, vis, r)])).
    rewrite ABS...
    simpl in LEN3; try rewrite app_length in LEN3.
    eapply length_zero_iff_nil...
    subst ne...
    assumption.

    
     destruct G1EQ as [(OPT3 & NILL) | (OPT4 & EQF)].
     rewrite OPT3 in OPT2; move OPT2 at bottom.
     assert ( ne = nil).
     destruct NEEQ as [NIL | (qq &RREPL &IINCL &NNEEQ)]...
     
     destruct ne...
     inv OPT2.
     assert (ABS: In (b1,b2) (domain(newEntries g (secLabs (dep_relabel qq (domain g) pf)) (max (domain g))))).
     rewrite <-NNEEQ...
     assert (SLP2: sl_pos qq).
     eapply incl_pos  in IINCL; unfold sl_pos...
     assert (DIS: disjoint (domain g) ((domain (newEntries g (secLabs (dep_relabel qq (domain g) pf)) (max (domain g)))))).
     try eapply new_entries_disjoint...
     assert (M1: max (secLabs qq) <= max (secLabs p)).
     eapply incl_preserves_max...
      transitivity (max (secLabs p))...
      eapply disjoint_absurd...

      rewrite H in *; subst ne. inv OPT2.
      assert (LEN2:
               length (removeEntry (b1, b2) g) =
                 length( removeEntry (b1, b2) (k ++ (b1, b2, vis, r) :: removeEntry (b1, b2) g))).
      rewrite <-H4...
      case_eq (In2 (b1, b2) (domain k)); introv IN2.
      rewrite removeEntry_app_shift2 in LEN2;
        try eapply in2_in...
      rewrite app_length in LEN2; simpl in LEN2.
      lia.
      rewrite removeEntry_app_shift in LEN2;
        try eapply in2_nIn_iff;
        simpl in LEN2; try rewrite pairEq_eq_true in LEN2...
      rewrite app_length in LEN2.
      assert (LEN3: length k = 0) by lia.
      rewrite length_zero_iff_nil in LEN3; subst k.

   
      
    erewrite lts_un_tau_action_newEntries_1hk;
      simpl;try rewrite pairEq_eq_true...
    
    inv NEEQ; inv OPT4; try rewrite pairEq_eq_true in *.
     assert (LEN2:
               length (removeEntry (c1, c2) g) =
                 length( removeEntry (c1, c2) (k ++ (c1, c2, vis, tb) :: removeEntry (c1, c2) g))).
      rewrite H3...
      case_eq (In2 (c1, c2) (domain k)); introv IN2.
      rewrite removeEntry_app_shift2 in LEN2;
        try eapply in2_in...
      rewrite app_length in LEN2; simpl in LEN2.
      lia.
      rewrite removeEntry_app_shift in LEN2;
        try eapply in2_nIn_iff;
        simpl in LEN2; try rewrite pairEq_eq_true in LEN2...
      rewrite app_length in LEN2.
      assert (LEN3: length k = 0) by lia.
      rewrite length_zero_iff_nil in LEN3; subst k.
    erewrite lts_un_tau_action_newEntries_1hk;
    try eapply in_g_in_domain...
    

    destruct H as (rp &REPL2 &INCLQ &NE).
    assert (q = rp). eapply replication_unique...
    subst; erewrite dep_relabel_rewrite_pf...
    
    assert (NEW := H4); clear H4.
    rewrite removeEntry_app_shift in NEW; simpl in NEW;
      try rewrite pairEq_eq_true in NEW.
    rewrite removeEntry_app_shift in NEW; simpl in NEW;
      try rewrite pairEq_eq_true in NEW.
    eapply app_inv_tail...

    (*~
  In (c1, c2)
    (domain (newEntries g (secLabs (dep_relabel rp (domain g) pf)) (max (domain g))))*)
    intros ABS.
    assert (DIS: disjoint (domain g) (
                     (domain (newEntries g (secLabs (dep_relabel rp (domain g) pf)) (max (domain g)))))).
    eapply new_entries_disjoint...
    eapply incl_pos in INCLQ; unfold sl_pos...
    transitivity ( max (secLabs p));
      try eapply incl_preserves_max...
    eapply disjoint_absurd...
    (*  ~ In (c1, c2) (domain k) *)
    intros ABS.
    eapply lts_no_dup in LTS as ND2;try eapply incl_incl2;
      try simpl in ND2;
      try rewrite removeEntry_app_shift2,domain_distr in ND2;
      try inv ND2...
    assert (In (c1, c2)
              (domain (removeEntry (c1, c2) k) ++ (c1, c2) :: domain (removeEntry (c1, c2) g))).
    eapply in_app_iff; right...
    contradiction.
    Unshelve.
    eauto.
Qed. 
