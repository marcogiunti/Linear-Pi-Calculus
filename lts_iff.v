Require Import
  Bool List Omega PeanoNat Program.Equality
  ListAddOns Max RemoveEntry Domain Classical
  Replication
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
  sne_premises
  split_operations_4
  lts_no_dup
  tc_dep_relabel_premises.


  Require Import CpdtTactics LibTactics.
  Import ListNotations.

  Hint Resolve in_g_in_domain
               no_dup_cons_removeEntry.
  
 
  Lemma cons_cons_removeEntry_iff a1 a2 b1 b2 f1 f2 t1 t2 g g2 (nd_pf : NoDup (domain g)) (nd_pf2 : NoDup (domain g2)): 
          (forall x : name * name * flag * piType, In x g <-> In x g2) ->
  (forall x, In x
    ((a1, a2, f1, t1)
     :: (b1, b2, f2, t2) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)) <->
  In x
    ((a1, a2, f1, t1)
       :: (b1, b2, f2, t2) :: removeEntry (a1, a2) (removeEntry (b1, b2) g2))).
  Proof with eauto.
    introv IFF; intros; split; introv IN;
      try inv IN as [IN2 |CONT2];
      try inv CONT2 as [IN3 | CONT3];
      try contradiction...

    assert (NIN1: forall f t,
               ~In (a1,a2,f,t) (removeEntry (a1, a2) (removeEntry (b1, b2) g))).
    intros; eapply no_dup_not_in_removeEntry ...
    assert (NIN2: forall f t,
               ~In (b1,b2,f,t) (removeEntry (b1, b2) g)).
     intros; eapply no_dup_not_in_removeEntry ...
     destruct x as [[[x1 x2]ff1]tt1].
     assert (DIFF1 : (x1, x2) <> (a1, a2)).
     intros ABS; inv ABS; specialize NIN1 with ff1 tt1...
     assert (DIFF2 : (x1, x2) <> (b1, b2)).
     intros ABS; inv ABS; specialize NIN2 with ff1 tt1...
   
     eapply in_removeEntry,in_removeEntry,IFF in CONT3;
       repeat right;
       repeat eapply removeEntry_in...

      assert (NIN1: forall f t,
               ~In (a1,a2,f,t) (removeEntry (a1, a2) (removeEntry (b1, b2) g2))).
    intros; eapply no_dup_not_in_removeEntry ...
    assert (NIN2: forall f t,
               ~In (b1,b2,f,t) (removeEntry (b1, b2) g2)).
     intros; eapply no_dup_not_in_removeEntry ...
     destruct x as [[[x1 x2]ff1]tt1].
     assert (DIFF1 : (x1, x2) <> (a1, a2)).
     intros ABS; inv ABS; specialize NIN1 with ff1 tt1...
     assert (DIFF2 : (x1, x2) <> (b1, b2)).
     intros ABS; inv ABS; specialize NIN2 with ff1 tt1...
   
     eapply in_removeEntry,in_removeEntry,IFF in CONT3;
       repeat right;
     repeat eapply removeEntry_in...
Qed.    
    
  Lemma cons_removeEntry_iff b1 b2 f2 t2 g g2  (nd_pf : NoDup (domain g)) (nd_pf2 : NoDup (domain g2)): 
          (forall x : name * name * flag * piType, In x g <-> In x g2) ->
  (forall x, In x
    ( (b1, b2, f2, t2) :: removeEntry (b1, b2) g) <->
  In x
    ( (b1, b2, f2, t2) :: removeEntry (b1, b2) g2)).
    Proof with eauto.
   introv IFF; intros; split; introv IN;
      try inv IN as [IN2 |CONT2];
      try contradiction...

    assert (NIN1: forall f t,
               ~In (b1,b2,f,t) (removeEntry (b1, b2) g)).
    intros; eapply no_dup_not_in_removeEntry ...
     destruct x as [[[x1 x2]ff1]tt1].
     assert (DIFF1 : (x1, x2) <> (b1, b2)).
     intros ABS; inv ABS; specialize NIN1 with ff1 tt1...
   
     eapply in_removeEntry,IFF in CONT2;
       repeat right;
       repeat eapply removeEntry_in...

      assert (NIN1: forall f t,
               ~In (b1,b2,f,t) (removeEntry (b1, b2) g2)).
    intros; eapply no_dup_not_in_removeEntry ...
    assert (NIN2: forall f t,
               ~In (b1,b2,f,t) (removeEntry (b1, b2) g2)).
     intros; eapply no_dup_not_in_removeEntry ...
     destruct x as [[[x1 x2]ff1]tt1].
     assert (DIFF1 : (x1, x2) <> (b1, b2)).
     intros ABS; inv ABS; specialize NIN1 with ff1 tt1...
     eapply in_removeEntry,IFF in CONT2;
       repeat right;
       repeat eapply removeEntry_in...
    Qed.

    Hint Rewrite cons_removeEntry_iff.

    Lemma app_cons_removeEntry_iff k b1 b2 f2 t2 g g2
      (nd_pf : NoDup (domain g)) (nd_pf2 : NoDup (domain g2)): 
          (forall x : name * name * flag * piType, In x g <-> In x g2) ->
  (forall x, In x
    (k ++  (b1, b2, f2, t2) :: removeEntry (b1, b2) g) <->
  In x
    (k ++ (b1, b2, f2, t2) :: removeEntry (b1, b2) g2)).
   Proof with eauto using cons_removeEntry_iff.
     introv IFF; intros; split; try introv IN;
       try eapply in_app_iff in IN as [IN1 | IN2];
       try eapply in_app_iff...
     right; erewrite cons_removeEntry_iff ...
     right; erewrite cons_removeEntry_iff ...
   Qed.

   Hint Resolve sl_pos_par_l
     sl_pos_par_r sl_pos_repl
     sl_pos_nu
     sl_pos_bang
     sl_pos_out
     sl_pos_inp.

   Hint Resolve in_removeEntry_cons_iff_2.

  Lemma lts_iff a g1 g' g2 p p' pf1 pf2 (pf' : NoDup (domain g')):
    lts g1 p a g' p' pf1 ->
    (forall x, In x g1 <-> In x g2) ->
    sl_pos p ->
    NoDup (secLabs p) ->
    incl (secLabs p ) (domain g1) -> 
    max (secLabs p) <= max (domain g1) ->
    exists g'' (pf'' : NoDup(domain g'')),
      lts g2 p a g'' p' pf2 /\
        (forall x, In x  g' <-> In x g'').
  Proof with eauto using
             cons_cons_removeEntry_iff,
      cons_removeEntry_iff,
      app_cons_removeEntry_iff,
      in_g_in_domain.
  introv LTS IFF SLP NDP INCL MAXD.
  gen g2.
  dependent induction LTS;introv IFF.
  

  -  try eapply IHLTS in IFF as (k1 &pfh &IH &IFF2); 
       try eexists; try econstructor... econstructor...
     econstructor...
     simpl in *; rewrite no_dup_iff in *; intuition.
     simpl in INCL; eapply incl_distr in INCL; intuition.
  - assert (pf'': NoDup
          (domain
             ((a1, a2, vis, Chan lin empty t)
                :: (b1, b2, vis, t2) :: removeEntry (a1, a2) (removeEntry (b1, b2) g2)))).
    eapply no_dup_cons_removeEntry_app,nonRecActions2,lOut ...
    
    eexists; split... split; try eapply lOut;
      try eapply IFF...
  - assert (pf'': NoDup (domain ((b1, b2, vis, t2) :: removeEntry (b1, b2) g2))).
    eapply no_dup_cons_removeEntry...
    eexists;exists pf''; split.  try eapply uOut;
      try eapply IFF...
    try eapply IFF...
  - assert (pf'': NoDup
          (domain
             ((a1, a2, vis, Chan lin empty t)
                :: (b1, b2, vis, t2) :: removeEntry (a1, a2) (removeEntry (b1, b2) g2)))).
    eapply no_dup_cons_removeEntry_app,nonRecActions1,lIn ...
    eexists; split...
     split; try eapply lIn;
      try eapply IFF... 
  - assert (pf'': NoDup (domain ((b1, b2, vis, t2) :: removeEntry (b1, b2) g2))).
    eapply no_dup_cons_removeEntry...
    eexists;exists pf''; split.  try eapply uIn;
      try eapply IFF...
    try eapply IFF...
  - assert (MAX: max (domain g) = max (domain g2)).
    eapply max_same_domain; intros; split; introv IN;
    eapply in_domain_in_g in IN as (ff &tt &IN);
    try eapply IFF in IN; try eapply in_g_in_domain...
    subst q. erewrite max_dep_relabel with (nd_pf1 := pf2).

    assert (pf'': NoDup
          (domain
             (newEntries g2 (secLabs (dep_relabel p (domain g2) pf2)) (max (domain g2)) ++
                (b1, b2, vis, t2) :: removeEntry (b1, b2) g2))).
    rewrite domain_distr; eapply distr_no_dup;
      try eapply newEntries_no_dup...
    try erewrite identif_seclabs_of_dep_relabel;
    eapply FinFun.Injective_map_NoDup...
    introv EQ; destruct x,y; inv EQ.
    assert (n0 = n2) by omega.
    subst...
    
    eapply disjoint_commute,disjoint_iff with (l1 := domain g2); try eapply new_entries_disjoint.
      try eapply sl_pos_bang...
    try rewrite <-MAX; inv MAXD...

    eapply in_removeEntry_cons_iff;
    try eapply in_g_in_domain; try rewrite <-IFF...
    
    
    eexists; exists pf''. split; try eapply uRin;try eapply IFF...
    erewrite MAX,NewEntries.newEntries_iff...
    assumption.
  -
    assert (NDP2 := NDP); simpl in NDP2;
      eapply no_dup_iff in NDP2 as (ND1 &ND2 &DIS).
    assert (IH1:
              (forall x : name * name * flag * piType,
                  In x ((a1, a2, vis, Chan lin out t) :: (b1, b2, vis, s) :: g0) <-> In x ((a1, a2, vis, Chan lin out t) :: (b1, b2, vis, s) :: removeEntry(a1,a2)(removeEntry (b1, b2) g2)))).
    subst g0...
    assert (IH2:
              (forall x : name * name * flag * piType,
                  In x ((a1, a2, vis, Chan lin inp t) :: (b1, b2, vis, s1) :: g0) <-> In x ((a1, a2, vis, Chan lin inp t) :: (b1, b2, vis, s1) ::removeEntry(a1,a2)(removeEntry (b1, b2) g2)))).
    subst g0...

    assert (SLP1 := SLP).
    assert (SLP2 := SLP).
    eapply sl_pos_par_l in SLP1; eapply sl_pos_par_r in SLP2.
    assert (MAXD1 := MAXD).
    assert (MAXD2 := MAXD).
    simpl in MAXD1,MAXD2;
      eapply max_app_l in MAXD1;
      eapply max_app_r in MAXD2.

  eapply IHLTS1 in IH1 as (k1 &pfh1 & IH1 &IFF1); 
    eapply IHLTS2  in IH2 as (k2 &pfh2& IH2 &IFF2);
    clear IHLTS1 IHLTS2;
    try match goal with
      | [ _ : _ |- incl _ _ ] =>
          simpl in INCL;
          eapply incl_distr in INCL as (INCL1 &INCL2);
       eapply incl_tran with (m := domain g),
              incl_iff with (m1 := domain g);
          try eapply incl_refl
      | [ _ : _ |- max _ <= max _] =>
          subst g0;
          erewrite <-max_same_domain with (l := domain _)
      end;
     try match goal with
      | [ _ : _ |- (forall _, In _ (domain _) <-> In _ (domain _))] =>
          try subst g0; intros;
          try erewrite <-in_removeEntry_cons_iff_2;
        try eapply in_g_in_domain;
          try tauto; try eapply nonRecActions2;
          try tauto;
          try eassumption
       end;
    try eassumption.
  

  
  assert (EQ: k1 = (a1, a2, vis, Chan lin empty t)
  :: (b1, b2, vis, s1)
     :: removeEntry (a1, a2) (removeEntry (b1, b2) 
     (((a1, a2, vis, Chan lin out t)
     :: (b1, b2, vis, s)
        :: removeEntry (a1, a2)
             (removeEntry (b1, b2) g2))))).
     eapply lts_lin_output_action...
     subst k1.
     assert (DIFF: (a1, a2) <> (b1, b2)).
     try eapply nonRecActions1...
     erewrite pairEq_neq in DIFF.
    assert (EQ: (a1, a2, vis, Chan lin empty t)
    :: (b1, b2, vis, s1)
       :: removeEntry (a1, a2) (removeEntry (b1, b2) 
       (((a1, a2, vis, Chan lin out t)
       :: (b1, b2, vis, s)
          :: removeEntry (a1, a2)
               (removeEntry (b1, b2) g2)))) =
               (a1, a2, vis, Chan lin empty t)
               :: (b1, b2, vis, s1)  
               :: removeEntry (a1, a2)
               (removeEntry (b1, b2) g2)).
    simpl; repeat rewrite DIFF;  rewrite pairEq_eq_true;
      simpl...
    rewrite pairEq_eq_true...

    rewrite EQ in *; clear EQ. 

    assert (EQ: k2 = (a1, a2, vis, Chan lin empty t)
    :: (b1, b2, vis, s)
       :: removeEntry (a1, a2) (removeEntry (b1, b2) 
       (((a1, a2, vis, Chan lin inp t)
       :: (b1, b2, vis, s1)
          :: removeEntry (a1, a2)
               (removeEntry (b1, b2) g2))))).
       eapply lts_lin_input_action; inverts H as [TP _];
       try eapply type_plus_comm...
      subst k2. 
      
      assert (EQ: (a1, a2, vis, Chan lin empty t)
      :: (b1, b2, vis, s)
         :: removeEntry (a1, a2) (removeEntry (b1, b2) 
         (((a1, a2, vis, Chan lin inp t)
         :: (b1, b2, vis, s1)
            :: removeEntry (a1, a2)
                 (removeEntry (b1, b2) g2)))) =
                 (a1, a2, vis, Chan lin empty t)
                 :: (b1, b2, vis, s)  
                 :: removeEntry (a1, a2)
                 (removeEntry (b1, b2) g2)).
      simpl; repeat rewrite DIFF;  rewrite pairEq_eq_true;
      simpl...
      rewrite pairEq_eq_true...
      
      rewrite EQ in *; clear EQ.     
      
      
      subst g0; eexists; split...
      split; try eapply lcomL; try eapply IFF...

      all:
        intros;
          try erewrite <-in_removeEntry_cons_iff_2;
        try eapply in_g_in_domain;
          try tauto; try eapply nonRecActions2;
          try tauto; try eassumption.
       

  -    (* same as lcomL  *)
      assert (NDP2 := NDP); simpl in NDP2;
      eapply no_dup_iff in NDP2 as (ND1 &ND2 &DIS).
   
    assert (IH1:
             (forall x : name * name * flag * piType,
                 In x ((a1, a2, vis, Chan lin out t) :: (b1, b2, hid, s) :: g0) <-> In x ((a1, a2, vis, Chan lin out t) :: (b1, b2, hid, s) :: removeEntry(a1,a2)(removeEntry (b1, b2) g2)))).
    subst...
    assert (IH2:
             (forall x : name * name * flag * piType,
                 In x ((a1, a2, vis, Chan lin inp t) :: (b1, b2, ill, s1) :: g0) <-> In x ((a1, a2, vis, Chan lin inp t) :: (b1, b2, ill, s1) ::removeEntry(a1,a2)(removeEntry (b1, b2) g2)))).
    subst...

    assert (SLP1 := SLP).
    assert (SLP2 := SLP).
    eapply sl_pos_par_l in SLP1; eapply sl_pos_par_r in SLP2.
    assert (MAXD1 := MAXD).
    assert (MAXD2 := MAXD).
    simpl in MAXD1,MAXD2;
      eapply max_app_l in MAXD1;
      eapply max_app_r in MAXD2.

  eapply IHLTS1 in IH1 as (k1 &pfh1 & IH1 &IFF1); 
    eapply IHLTS2  in IH2 as (k2 &pfh2& IH2 &IFF2);
    clear IHLTS1 IHLTS2;
    try match goal with
      | [ _ : _ |- incl _ _ ] =>
          simpl in INCL;
          eapply incl_distr in INCL as (INCL1 &INCL2);
       eapply incl_tran with (m := domain g),
              incl_iff with (m1 := domain g);
          try eapply incl_refl
      | [ _ : _ |- max _ <= max _] =>
          subst g0;
          erewrite <-max_same_domain with (l := domain _)
      end;
     try match goal with
      | [ _ : _ |- (forall _, In _ (domain _) <-> In _ (domain _))] =>
          try subst g0; intros;
          try erewrite <-in_removeEntry_cons_iff_2;
        try eapply in_g_in_domain;
          try tauto; try eapply nonRecActions2;
          try tauto;
          try eassumption
       end;
    try eassumption.
  
  (*  eapply IHLTS1 in IH1 as (k1 &pfh1 &IH1 &IFF1); 
      eapply IHLTS2  in IH2 as (k2 &pfh2 &IH2 &IFF2);
      clear IHLTS1 IHLTS2;
    
    try match goal with
      | [ _ : _ |- incl _ _ ] =>
          simpl in INCL;
          eapply incl_distr in INCL as (INCL1 &INCL2);
       eapply incl_tran with (m := domain g),
          incl_iff with (m1 := domain g); eauto;
      intros;
          try eapply in_removeEntry_cons_iff_2;
          eauto
      end;
    eauto. 
*)

    assert (EQ: k1 = (a1, a2, vis, Chan lin empty t)
                       :: (b1, b2, vis, s1)
                       :: removeEntry (a1, a2) (removeEntry (b1, b2) 
                                                  (((a1, a2, vis, Chan lin out t)
                                                      :: (b1, b2, hid, s)
                                                      :: removeEntry (a1, a2)
                                                      (removeEntry (b1, b2) g2))))).
    eapply lts_lin_output_action...
    subst k1.
    assert (DIFF: (a1, a2) <> (b1, b2)).
    try eapply nonRecActions1...
    erewrite pairEq_neq in DIFF.
    assert (EQ: (a1, a2, vis, Chan lin empty t)
                  :: (b1, b2, vis, s1)
                  :: removeEntry (a1, a2) (removeEntry (b1, b2) 
                                             (((a1, a2, vis, Chan lin out t)
                                                 :: (b1, b2, hid, s)
                                                 :: removeEntry (a1, a2)
                                                 (removeEntry (b1, b2) g2)))) =
                  (a1, a2, vis, Chan lin empty t)
                    :: (b1, b2, vis, s1)  
               :: removeEntry (a1, a2)
               (removeEntry (b1, b2) g2)).
    simpl; repeat rewrite DIFF;  rewrite pairEq_eq_true;
      simpl...
    rewrite pairEq_eq_true...

    rewrite EQ in *; clear EQ. 

    assert (EQ: k2 = (a1, a2, vis, Chan lin empty t)
    :: (b1, b2, vis, s)
       :: removeEntry (a1, a2) (removeEntry (b1, b2) 
       (((a1, a2, vis, Chan lin inp t)
       :: (b1, b2, ill, s1)
          :: removeEntry (a1, a2)
               (removeEntry (b1, b2) g2))))).
       eapply lts_lin_input_action; inverts H as [TP _];
       try eapply type_plus_comm...
      subst k2. 
      
      assert (EQ: (a1, a2, vis, Chan lin empty t)
      :: (b1, b2, vis, s)
         :: removeEntry (a1, a2) (removeEntry (b1, b2) 
         (((a1, a2, vis, Chan lin inp t)
         :: (b1, b2, ill, s1)
            :: removeEntry (a1, a2)
                 (removeEntry (b1, b2) g2)))) =
                 (a1, a2, vis, Chan lin empty t)
                 :: (b1, b2, vis, s)  
                 :: removeEntry (a1, a2)
                 (removeEntry (b1, b2) g2)).
      simpl; repeat rewrite DIFF;  rewrite pairEq_eq_true;
      simpl...
      rewrite pairEq_eq_true...
      rewrite EQ in *; clear EQ.

     assert (pf'' :
               NoDup (domain ( (a1, a2, vis, Chan lin empty t) :: (b1, b2, hid, s) :: removeEntry (a1, a2)(removeEntry (b1, b2) g2)))).
     eapply no_dup_cons_removeEntry_app,nonRecActions2...
     
      
      

      subst g0; eexists; split...
      split;try eapply lclsL; try eapply IFF...

       all:
        intros;
          try erewrite <-in_removeEntry_cons_iff_2;
        try eapply in_g_in_domain;
          try tauto; try eapply nonRecActions2;
          try tauto; try eassumption.
 
  -  assert (NDP2 := NDP); simpl in NDP2;
       eapply no_dup_iff in NDP2 as (ND1 &ND2 &DIS').
     
     
       assert (IH2 :
              (forall x : name * name * flag * piType,
                  In x  ((b1, b2, vis, s1) :: g0) <-> In x ( (b1, b2, vis, s1) :: removeEntry (b1, b2) g2))).
       subst... 
       assert (IH1 := IFF).

    assert (SLP1 := SLP).
    assert (SLP2 := SLP).
    eapply sl_pos_par_l in SLP1; eapply sl_pos_par_r in SLP2.
    assert (MAXD1 := MAXD).
    assert (MAXD2 := MAXD).
    simpl in MAXD1,MAXD2;
      eapply max_app_l in MAXD1;
      eapply max_app_r in MAXD2.

  eapply IHLTS1 in IH1 as (k1 &pfh1 & IH1 &IFF1); 
    eapply IHLTS2  in IH2 as (k2 &pfh2& IH2 &IFF2);
    clear IHLTS1 IHLTS2;
    try match goal with
      | [ _ : _ |- incl _ _ ] =>
          simpl in INCL;
          eapply incl_distr in INCL as (INCL1 &INCL2);
       eapply incl_tran with (m := domain g),
              incl_iff with (m1 := domain g);
          try eapply incl_refl
      | [ _ : _ |- max _ <= max _] =>
          subst g' g0;
          erewrite <-max_same_domain with (l := domain _)
      end;
     try match goal with
      | [ _ : _ |- (forall _, In _ (domain _) <-> In _ (domain _))] =>
          try subst g' g0;
          try intros;
          try erewrite <-in_removeEntry_cons_iff;
        try eapply in_g_in_domain;
          try tauto; try eapply nonRecActions1;
          try tauto;
          try eassumption
       end;
    try eassumption.

  all:
     try match goal with
      | [ _ : _ |- (forall _, In _ (domain _) <-> In _ (domain _))] =>
          try subst g' g0;
          try intros;
          try erewrite <-in_removeEntry_cons_iff;
        try eapply in_g_in_domain;
          try tauto; try eapply nonRecActions1;
          try tauto;
          try eassumption
       end.

  
  (*eapply IHLTS1 in IH1 as (k1 &pfh1 &IH1 &IFF1); 
    eapply IHLTS2  in IH2 as (k2 &pfh2& IH2 &IFF2);
    clear IHLTS1 IHLTS2;
  
    try match goal with
      | [ _ : _ |- incl _ _ ] =>
          simpl in INCL;
          eapply incl_distr in INCL as (INCL1 &INCL2);
       eapply incl_tran with (m := domain g),
          incl_iff with (m1 := domain g); eauto;
      intros;
          try eapply in_removeEntry_cons_iff_2;
          eauto
      end;
    eauto.
*)
  

  assert (TR := H).
  inv H as (TS &TP &ISUN).

  assert (EQ: k1 = (b1, b2, vis, s1)
                     :: removeEntry (b1, b2) 
                     g2).
   eapply lts_un_output_action; econstructor; try rewrite <-IFF...

     subst k1.
     assert (DIFF: (a1, a2) <> (b1, b2)).
     try eapply nonRecActions1...
     erewrite pairEq_neq in DIFF.

     
     assert (EQ:  exists k : typeEnv,
                disjoint (domain k) (domain ((b1, b2, vis, s1) :: removeEntry (b1, b2) g2)) /\
                  k2 = k ++ (b1, b2, vis, s)
                        ::(removeEntry (b1, b2) 
       ((b1, b2, vis, s1)
          ::   (removeEntry (b1, b2) g2)))).
     
       eapply lts_un_input_action;
         try eapply type_plus_comm; try assumption.
       eauto.
       econstructor; right; eapply removeEntry_in;
         try rewrite <-IFF...
       eauto.
       eauto.
       eauto.
       erewrite <-max_same_domain with (l := domain _);
         try eassumption;
           try intros;
          try erewrite <-in_removeEntry_cons_iff;
        try eapply in_g_in_domain;
          try tauto; try eapply nonRecActions1;
          try tauto;
          try eassumption.
       split; introv IN; eapply in_domain_in_g in IN as (ff &tt&IN);
       try eapply IFF in IN...
       eapply IFF...
       



          
           
       destruct EQ as (k &DIS &EQ).
       exists k2; split...
          split;
            try eapply ucomL; try assumption;
            subst g'; try rewrite <-IFF...
         
          subst; try rewrite in_app_iff; repeat right;
            simpl; try rewrite pairEq_eq_true;
          try eapply removeEntry_in,IFF...
          subst; try rewrite in_app_iff...

  -  (* same as lcomL  *)
     assert (NDP2 := NDP); simpl in NDP2;
      eapply no_dup_iff in NDP2 as (ND1 &ND2 &DIS').
    simpl in INCL; eapply incl_distr in INCL as (INCL1 &INCL2).
    assert (INCL3:  incl (secLabs q1) (domain ((b1, b2, ill, s1) :: removeEntry (b1, b2) g))).
    eapply incl_iff,in_removeEntry_cons_iff...
    assert (ND3: NoDup (domain g3)).
    eapply lts_no_dup in LTS2; subst g' g0;
      simpl in NDP;
      try eapply   no_dup_iff in NDP as (ND1 &ND2 &_);
      try eapply incl_incl2...
    eapply incl_preserves_max...
  
    assert (SLP1 := SLP).
    assert (SLP2 := SLP).
    eapply sl_pos_par_l in SLP1; eapply sl_pos_par_r in SLP2.
    assert (MAXD1 := MAXD).
    assert (MAXD2 := MAXD).
    simpl in MAXD1,MAXD2;
      eapply max_app_l in MAXD1;
      eapply max_app_r in MAXD2.
    
           assert (IH2 :
              (forall x : name * name * flag * piType,
                  In x  ((b1, b2, ill, s1) :: g0) <-> In x ( (b1, b2, ill, s1) :: removeEntry (b1, b2) g2))).
           subst...
    assert (IH1 := IFF).
   eapply IHLTS1 in IH1 as (k1 &pfh1 &IH1 &IFF1); 
     try eapply IHLTS2  in IH2 as (k2 &pfh2 &IH2 &IFF2);
     clear IHLTS1 IHLTS2; try eassumption;
     subst g' g0;
     try erewrite <-max_same_domain with (l := domain _);
     try eassumption;
     try intros;
     try eapply in_removeEntry_cons_iff;
     try eapply in_g_in_domain;
     try eassumption.

  assert (TR := H).
  inv H as (TS &TP &ISUN).

  assert (EQ: k1 = (b1, b2, vis, s1)
                     :: removeEntry (b1, b2) 
                     g2).
   eapply lts_un_output_action; econstructor; try rewrite <-IFF...

     subst k1.
     assert (DIFF: (a1, a2) <> (b1, b2)).
     try eapply nonRecActions1...
     erewrite pairEq_neq in DIFF.


   (*  
    assert (EQ: (a1, a2, vis, Chan lin empty t)
    :: (b1, b2, vis, s1)
       :: removeEntry (a1, a2) (removeEntry (b1, b2) 
       (((a1, a2, vis, Chan lin out t)
       :: (b1, b2, vis, s)
          :: removeEntry (a1, a2)
               (removeEntry (b1, b2) g2)))) =
               (a1, a2, vis, Chan lin empty t)
               :: (b1, b2, vis, s1)  
               :: removeEntry (a1, a2)
               (removeEntry (b1, b2) g2)).
    simpl; repeat rewrite DIFF;  rewrite pairEq_eq_true;
      simpl...
    rewrite pairEq_eq_true...

    rewrite EQ in *; clear EQ. 
*)
     
     assert (EQ:  exists k : typeEnv,
                disjoint (domain k) (domain ((b1, b2, ill, s1) :: removeEntry (b1, b2) g2)) /\
                  k2 = k ++ (b1, b2, vis, s)
                        ::(removeEntry (b1, b2) 
       ((b1, b2, ill, s1)
          ::   (removeEntry (b1, b2) g2)))).
       eapply lts_un_input_action;
         try eapply type_plus_comm; try assumption.
       eauto.
       econstructor; right; eapply removeEntry_in;
         try rewrite <-IFF...
       eauto.
       eauto.
       eauto.

        erewrite <-max_same_domain with (l := domain _);
         try eassumption;
           try intros;
          try erewrite <-in_removeEntry_cons_iff;
        try eapply in_g_in_domain;
          try tauto; try eapply nonRecActions1;
          try tauto;
          try eassumption.
       split; introv IN; eapply in_domain_in_g in IN as (ff &tt&IN);
       try eapply IFF in IN...
       eapply IFF...



          destruct EQ as (ne &DIS &EQ2).
          exists ((b1, b2, hid, s):: removeEntry (b1, b2) k2); split... split; subst k2; try eapply uclsL; try assumption;
            try rewrite <-IFF...
          
          subst; try rewrite in_app_iff; repeat right;
            simpl; try rewrite pairEq_eq_true;
          try eapply removeEntry_in,IFF...
          subst; try rewrite in_app_iff...

  -  assert (IH: forall x, 
  In x ((b1, b2, vis, t) :: removeEntry (b1, b2) g) <->
    In x ( (b1,b2, vis, t) :: removeEntry (b1, b2) g2)).
     
     intros; try erewrite <-IFF.
     eapply cons_removeEntry_iff...

     

     assert (SLP1 := SLP).
    assert (SLP2 := SLP).
    eapply sl_pos_nu in SLP1.
    assert (MAXD1 := MAXD).
    assert (MAXD2 := MAXD).
    simpl in MAXD1,MAXD2;
      eapply max_app_l in MAXD1;
      eapply max_app_r in MAXD2.
     
     eapply IHLTS in IH as (k1 &IH &IFF2); clear IHLTS;
       try eexists; try split;
    try split; try eapply open;
  try eapply IFF;
      try eapply IFF2;
       try eassumption.

    
     simpl in *; rewrite no_dup_iff in *; intuition.

     
    


     simpl in INCL;
          eapply incl_distr in INCL as (INCL1 &INCL2);
       eapply incl_tran with (m := domain g),
          incl_iff with (m1 := domain g); eauto;
       try eapply in_removeEntry_cons_iff...

   
     erewrite <-max_same_domain with (l := domain _);
       try eassumption;
       try eapply in_removeEntry_cons_iff...

     
   Unshelve.
   all:
     try match goal with
       | [_ : _ |-
            NoDup
   (domain (_ :: _ :: removeEntry _ (removeEntry _ _)))] =>
             eapply no_dup_cons_removeEntry_app; eauto
      | [_ : _ |-
            NoDup
              (domain (_ :: removeEntry _ _))] =>
          eapply no_dup_cons_removeEntry; eauto
       | [_ : _ |- (_,_) <> (_, _)] =>
           eapply nonRecActions1; eauto
       | _ =>
           try assumption
       end.

   
    
  - 
    
    subst g.
    assert (PF2 := pf2).
   
  assert (GL: In (b1, b2, hid, t) g2).
  eapply IFF; try eapply in_app_iff; right...
  eapply in_split in GL as (m1 &m2 &EQm); subst.

  assert (IH: (forall x,
                  In x (h1 ++ (b1, b2, vis, t) :: h2) <-> In x (m1 ++ (b1, b2, vis, t) :: m2))).
  intros; split; introv IN; eapply in_app_iff in IN as [IN | CONT].
  
  assert (IFF' : In x (h1 ++ (b1, b2, hid, t) :: h2)).
  eapply in_app_iff...
  eapply IFF,in_app_iff in IFF'.
  destruct IFF' as [IN' | CONT]; try eapply in_app_iff...
  inv CONT as [ABS | CONT2]...
  rewrite domain_distr,no_dup_iff in pf;
    intuition;
    eapply disjoint_absurd...
  repeat right...

  inv CONT as [EQ | CONT2]; eapply in_app_iff...
   assert (IFF' : In x (h1 ++ (b1, b2, hid, t) :: h2)).
  eapply in_app_iff; repeat right...
  eapply IFF,in_app_iff in IFF'.
  destruct IFF' as [IN' | CONT]...
  inv CONT as [ABS | CONT3]...
  rewrite domain_distr,no_dup_iff in pf;
    intuition.
  inv H2; eapply in_g_in_domain in CONT2; try contradiction...
  repeat right...

  assert (IFF' : In x (m1 ++ (b1, b2, hid, t) :: m2)).
  eapply in_app_iff...
  eapply IFF,in_app_iff in IFF'.
  destruct IFF' as [IN' | CONT]; try eapply in_app_iff...
  inv CONT as [ABS | CONT2]...
  rewrite domain_distr,no_dup_iff in pf2;
    intuition;
    eapply disjoint_absurd...
  repeat right...

  inv CONT as [EQ | CONT2]; eapply in_app_iff...
   assert (IFF' : In x (m1 ++ (b1, b2, hid, t) :: m2)).
  eapply in_app_iff; repeat right...
  eapply IFF,in_app_iff in IFF'.
  destruct IFF' as [IN' | CONT]...
  inv CONT as [ABS | CONT3]...
  rewrite domain_distr,no_dup_iff in pf2;
    intuition.
  inv H2; eapply in_g_in_domain in CONT2; try contradiction...
  repeat right...

  assert (PF3:
           NoDup (domain (m1 ++ (b1, b2, vis, t) :: m2))).
  rewrite domain_distr in *; simpl in *...
   eapply sl_pos_nu in SLP;
     eapply IHLTS  with (pf2 := PF3) in IH as (k1 &IH &IFF1); clear IHLTS;
     simpl in NDP;
     eapply no_dup_iff in NDP as (NDP &_ &_);
     try eassumption.


   assert (GL1: In (b1, b2, vis, t') k1).
  eapply IFF1; try eapply in_app_iff; right...
  eapply in_split in GL1 as (m' &m'' &EQm1); subst.

  assert (pf'': NoDup (domain (m' ++ (b1, b2, hid, t') :: m''))).
  rewrite domain_distr in *; simpl in *...

  eexists; split...
  split; try eapply hide; destruct  IFF1 as (LTS1 &IFF1)...
  
  (*forall x : name * name * flag * piType,
In x (h1 ++ (b1, b2, hid, t) :: h2) <->
In x (m1 ++ (b1, b2, hid, t) :: m2)*)
  intros; split; introv IN; eapply in_app_iff in IN as [IN | CONT].
  
 assert (IFF' : In x (h' ++ (b1, b2, vis, t') :: h'')).
  eapply in_app_iff...
  eapply IFF1,in_app_iff in IFF'.
  destruct IFF' as [IN' | CONT]; try eapply in_app_iff...
  inv CONT as [ABS | CONT2]...
  rewrite domain_distr,no_dup_iff in pf';
    intuition;
    eapply disjoint_absurd...
  repeat right...

  inv CONT as [EQ | CONT2]; eapply in_app_iff...
   assert (IFF' : In x (h' ++ (b1, b2, vis, t') :: h'')).
  eapply in_app_iff; repeat right...
  eapply IFF1,in_app_iff in IFF'.
  destruct IFF' as [IN' | CONT]...
  inv CONT as [ABS | CONT3]...
  rewrite domain_distr,no_dup_iff in pf';
    intuition.
  inv H2; eapply in_g_in_domain in CONT2; try contradiction...
  repeat right...

  assert (IFF' : In x (m' ++ (b1, b2, vis, t') :: m'')).
  eapply in_app_iff...
  eapply IFF1,in_app_iff in IFF'.
  destruct IFF' as [IN' | CONT]; try eapply in_app_iff...
  inv CONT as [ABS | CONT2]...
  rewrite domain_distr,no_dup_iff in pf'';
    intuition.
    eapply disjoint_absurd...
  repeat right...

  inv CONT as [EQ | CONT2]; eapply in_app_iff...
   assert (IFF' : In x (m' ++ (b1, b2, vis, t') :: m'')).
  eapply in_app_iff; repeat right...
  eapply IFF1,in_app_iff in IFF'.
  destruct IFF' as [IN' | CONT]...
  inv CONT as [ABS | CONT3]...
  rewrite domain_distr,no_dup_iff in pf'';
    intuition.
  inv H2; eapply in_g_in_domain in CONT2; try contradiction...
  repeat right...

  rewrite domain_distr in *; simpl in *...

  simpl in INCL; eapply incl_app_inv in INCL as (INCL1 &INCL2);
    rewrite domain_distr in *; simpl in *...

     simpl in MAXD;
       eapply max_app_l in MAXD;
       rewrite domain_distr in *; simpl in *...

     
Qed.
    
