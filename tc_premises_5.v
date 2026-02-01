Require Import
  Bool List Omega PeanoNat Program.Equality
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
  split_operations.
 
Require Import CpdtTactics LibTactics.
Import ListNotations.

Lemma type_of_tau_Action: forall g p a1 a2 g' p' pf,
    lts g p (aTau a1 a2) g' p' pf ->
    exists m t,
      In (a1, a2, vis, Chan m io t) g \/
        In (a1, a2, hid, Chan m io t) g.
Proof with eauto.
  introv LTS.
  dependent induction LTS...
  assert (IH : aTau a1 a2 = aTau a1 a2)...
  eapply IHLTS in IH as (mm &tt &[IN1 |IN2]);
    clear IHLTS;
    try eapply in_app_iff in IN1 as [IN1 | CONT];
    try eapply in_app_iff in IN2 as [IN2 | CONT]...
  exists mm tt; left; try eapply in_app_iff...
  try inverts CONT as EQ;
    try inv EQ.
  exists mm tt; right; try eapply in_app_iff...
  exists mm tt; left; try eapply in_app_iff;
    repeat right...
  exists mm tt; right; try eapply in_app_iff...
  try inverts CONT as EQ;
    try inv EQ; try discriminate...
  exists mm tt; right; try eapply in_app_iff;
    repeat right...
  
Qed.

Hint Resolve
  lts_operations.lts_lin_output_action
  lts_operations.lts_lin_input_action
  lts_operations.lts_un_output_action
  lts_un_input_action.

Hint Constructors replication.

Lemma lts_after_tau_lin: forall g  p1 p2 a1 a2 t g' nd_pf,
    lts g p1 (aTau a1 a2) g' p2 nd_pf ->
    In (a1, a2, vis, Chan lin io t) g ->
    exists b1 b2 f tb,
      (a1, a2) <> (b1, b2) /\  
        In (b1, b2, f, tb) g /\
        f <> ill /\
        g' =  (a1, a2, vis, Chan lin empty t)
                :: (b1, b2, f, tb)
                :: removeEntry (a1, a2) (removeEntry (b1, b2) g).
Proof with eauto.
  intros g  p1 p2 a1 a2 t g' nd_pf LTS IN.
  dependent induction LTS...
  - clear IHLTS1 IHLTS2.
    assert (EQ0: Chan lin io t = Chan lin io t0).
    eapply type_of_map with (g := g)...
    inversion EQ0; subst t0.
    eapply lts_operations.lts_lin_output_action with (t := t) (r := s1)in LTS1 as K1.
    eapply  lts_operations.lts_lin_input_action with (t := t) (r := s) (pol := inp)in LTS2 as K2.
    subst g0.
    
    inversion K1. inversion K2.  
    exists b1 b2 vis s...
    split...
    eapply nonRecActions2 in LTS1; intuition.
    discriminate.
    eauto.
    eauto.
    inversion H; intuition; eapply type_plus_comm...
    eauto.
    eauto.
    inversion H; intuition; eapply type_plus_comm...
  -  clear IHLTS1 IHLTS2.
     assert (EQ0: Chan lin io t = Chan lin io t0).
     eapply type_of_map with (g := g)...
     inversion EQ0; subst t0.
     eapply lts_operations.lts_lin_output_action with (t := t) (r := s1)in LTS1 as K1.
     eapply  lts_operations.lts_lin_input_action with (t := t) (r := s) (pol := inp)in LTS2 as K2.
     subst g0.
     
     inversion K1. inversion K2.  
     exists b1 b2 hid s...
     split...
     eapply nonRecActions2 in LTS1; intuition.
     discriminate.
     eauto.
     eauto.
     inversion H; intuition; eapply type_plus_comm...
     eauto.
     eauto.
     inversion H; intuition; eapply type_plus_comm...
  -  assert (ABS: Chan un io t0 = Chan lin io t).
     eapply type_of_map with (g := g)...
     inversion ABS.
  -  assert (ABS: Chan un io t0 = Chan lin io t).
     eapply type_of_map with (g := g)...
     inversion ABS.
  - assert (IH: aTau a1 a2 = aTau a1 a2)...
    eapply IHLTS in IH
        as (d1 & d2 &ff &tb & DIFF &IN2 &NILL &IH); clear IHLTS...
    eapply in_app_iff in IN2 as [IN2 | CONT]...

    exists d1 d2  ff tb; intuition...
    eapply typeEnv_eq_change_flag_removeEntry_app...
    intros ABS; inv ABS.
    assert (ABS: vis = hid /\ Chan lin io t = t0).
    eapply in_isMap...
    try eapply in_app_iff...
    destruct ABS; discriminate.
    intros ABS; inv ABS.
    rewrite domain_distr in pf;
      eapply no_dup_iff in pf as (ND1 &ND2 &DIS);
      eapply disjoint_absurd with (x := (b1, b2));
      try eapply in_g_in_domain...
    inverts CONT as EQ; try inv EQ.
    exists d1 d2 hid tb; intuition; try discriminate.
    assert (NIN1: In (d1, d2) (domain h1)-> False). intros ABS.
    rewrite domain_distr in pf;
      eapply no_dup_iff in pf as (ND1 &_ &DIS).
    simpl in DIS;
      eapply disjoint_absurd with (x := (d1, d2))...
    assert (NIN2: In (d1, d2) (domain h2)-> False). intros ABS.
    rewrite domain_distr in pf;
      eapply no_dup_iff in pf as (_ &ND2 &_);
      simpl in ND2; eapply NoDup_cons_iff in ND2; intuition.
    rewrite removeEntry_app_shift in *...
    simpl in *; rewrite pairEq_eq_true in *...
    assert (EQ: forall f,
               (a1, a2, vis, Chan lin empty t) :: (d1, d2, f, tb) :: removeEntry (a1, a2) (h1 ++ h2) =
                 [(a1, a2, vis, Chan lin empty t)] ++
                   (d1, d2, f, tb) :: removeEntry (a1, a2) (h1 ++ h2))...
    
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
    assert (ABS: vis = hid /\ Chan lin io t = t0).
    eapply in_isMap...
    try eapply in_app_iff...
    destruct ABS; discriminate.
    intros ABS; inv ABS.
    rewrite domain_distr in pf;
      eapply no_dup_iff in pf as (_ &ND2 &_);
      simpl in ND2;
      eapply NoDup_cons_iff in ND2 as [ABS2 _];
      eapply in_g_in_domain in EQ; try contradiction.
    eapply in_app_iff in IN as [HD | CONT];
      eapply in_app_iff;
      try inverts CONT as EQ; try inv EQ;
      try discriminate...
    repeat right...
Qed.





Lemma newEntries_removeEntry :
  forall b1 b2 f0 t0 f1 t1 p g1 nd_pf1,
    In (b1, b2, f0, t0) g1 ->
    sl_pos p ->
    ~In (b1, b2) (secLabs p) ->
    newEntries g1 (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1)) =
      newEntries ((b1, b2, f1, t1) :: removeEntry (b1, b2) g1)
        (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1)).
Proof with eauto.
  intros b1 b2 f0 t0 f1 t1 p g1 nd_pf1 IN SLP NIN.
  eapply in_g_in_domain,proposition27.in_preserves_max in IN. eapply newEntries_cons...
Qed.


Hint Resolve hid_proj_flagOf.

Lemma lts_open_in_secLabs: forall a1 a2 b1 b2 s g1 g2 pf p1 p2,
    In (b1, b2, hid, s) g1 ->
    lts g1 p1 (aOut a1 a2 b1 b2) g2 p2 pf ->
    In (b1, b2) (secLabs p1).
Proof with eauto || simpl.
  intros   a1 a2 b1 b2 s g1 g2 pf p1 p2 IN LTS.
  dependent induction LTS...
  eapply in_app_iff; right...
  assert (vis = hid);
    try eapply flag_of_map with (g := g)... discriminate.
  assert (vis = hid);
    try eapply flag_of_map with (g := g)... discriminate.
  eapply in_app_iff; right...
  remember b0 as c1; remember b3 as c2; subst b0 b3.
  eapply in_app_iff; left; eapply IHLTS;
    eapply in_app_iff in IN as [IN | CONT];
    try eapply in_app_iff;
    try inverts CONT as EQ; 
    try inv EQ; destruct H as [_ ABS];
    try contradiction...
  repeat right...
Qed.

Hint Resolve lts_open_in_secLabs.



Lemma  newEntries_remove_var g g1 l x1 x2 f t M:
  pos l ->
  x2 <= M ->
  ~ In (x1, x2) l ->
  g = (x1, x2, f, t) :: g1 ->
  NoDup (domain g) ->
  newEntries g (map (fun y => (fst y, snd y + M)) l) M =
  newEntries g1 (map (fun y => (fst y, snd y + M)) l) M.
Proof with eauto.
  intros.
  induction l...
  assert (POS := H).
  eapply pos_cons,IHl in H as K...
  remember (fun y : name * name => (fst y, snd y + M)) as ff.
  rewrite map_cons.
  assert (EQ1: ff a :: map ff l = [ff a] ++ map ff l)...
  try rewrite EQ1;
    repeat rewrite newEntries_distr;
    try rewrite K.

  assert (GOAL: newEntries g [ff a] M = newEntries g1 [ff a] M).
  subst g.
  subst ff; simpl.

  case_eq (pair_eq (fst a, snd a + M) (x1, x2) ). intros ABS; rewrite <-pairEq_eq in ABS; inv ABS.
  assert (snd a = 0). omega.
  destruct a as [a1 a2].
  assert (a2 > 0).
  eapply POS...
  simpl in *; omega.
  
  intros PNEQ; destruct a as [a1 a2]; simpl.
  case_eq (InB (a1, a2 + M) g1); introv INB.
  case_eq b; intros; subst; simpl...
  try rewrite INB...
  assert (EQ: a2 + M - M = a2). omega.
  rewrite EQ...

  case_eq (pair_eq (a1, a2) (x1, x2)). intros ABS;
    rewrite <-pairEq_eq in ABS; inv ABS.
  assert (In (x1, x2) ((x1, x2) :: l))...
  contradiction.
  simpl...
  
  rewrite GOAL...
  intros ABS.
  assert (In (x1, x2) (a :: l)). right...
  contradiction.
Qed.

Lemma no_dup_app_shift A (l1 l2 : list A) a:
  NoDup (l1 ++ a :: l2) ->
  NoDup (a :: l1 ++ l2).
Proof with eauto.
  introv ND.
  eapply NoDup_remove in ND as (ND &NIN)...
Qed.

Lemma iff_shift A (l1 l2 : list A) a:
  forall x,
    In x (l1 ++ a :: l2) <->
      In x (a :: l1 ++ l2).
Proof with eauto.
  intros; split; introv IN;
    try eapply in_app_iff in IN as [HD | TAIL];
    try eapply in_app_iff...
  right; eapply in_app_iff...
  inv TAIL...
  right; eapply in_app_iff; repeat right...
  inversion IN as [EQ |CONT]; subst;
    try eapply in_app_iff in CONT as [L |R]...
  repeat right...
Qed.

Lemma removeEntry_app:
  forall b1 b2 f t g ne,
    NoDup (domain (ne ++ (b1, b2, f, t) :: g)) ->
    removeEntry (b1, b2) (ne ++ (b1, b2, f, t) :: g) =
    ne ++ g.
Proof with eauto.
  intros b1 b2 f t g ne nd_pf.
  erewrite removeEntry_app_shift;simpl; try erewrite pairEq_eq_true...
  intros ABS.
  erewrite domain_distr in nd_pf. eapply no_dup_disjoint in nd_pf.
  eapply disjoint_absurd with (x := (b1, b2)), in_g_in_domain...
Qed.

Lemma flagOf_hide_app h1 h2 c1 c2 f1 f2 t1 t2 a1 a2 t:
  (a1,a2) <> (c1, c2) ->
  flagOf (h1 ++ (c1, c2, f1, t1) :: h2) (a1, a2) t ->
  flagOf (h1 ++ (c1, c2, f2, t2) :: h2) (a1, a2) t.
Proof with eauto.
  introv DIFF TYP; try inverts TYP as IN;
    try eapply in_app_iff in IN as [IN1 | [ABS | IN2]];
    try econstructor; try eapply in_app_iff;
    try inv ABS; try contradiction...
  repeat right...
  Unshelve. all:eauto.
Qed.

Lemma incl_distr : forall A (l1 l2 m : list A),
      incl (l1++l2) m <-> incl l1 m /\ incl l2 m.
  Proof with eauto.
    split; introv IN.
    eapply incl_app_inv...
    destruct IN as [INCL1 INCL2]; unfold incl; introv IN;
      try eapply in_app_iff in IN as [IN1 | IN2]...
  Qed.


(*
 G ++ (b,v,_):: (c,v,_) :: (a,v,un _) > P1 | ( *a(x).Q | a!c.Q) -(a)->
    ne ++ (c, v, _) :: remove c  (G ++ (b,v,_):: (c,v,_) :: (a,v,un _)) > P'
    ____________________________________________________________
    G ++ (b,h,_) :: (c,v,_) :: (a,v, un_)  NR b (P1 | ( *a(x).Q | a!c.Q)) -(a)->
    ne ++ (c, v, _) :: remove c  (G ++ (b,h,_):: (c,v,_) :: (a,v,un _)) > NR b P'

                                                                         
    G ++ (b,v,_)::  (a,v,un_) > P1 | ( *a(x).Q | a!b.Q) -->
    ne ++ (b, v, _) :: remove b  (G ++ (b,v,_) :: (a,v,_)) > P'
    ____________________________________________________________
    G ++ (b,h,t) :: (a,v,un_ )  NR b (P1 | ( *a(x).Q | a!b.Q)) -->
    ne ++ (b, h, _) :: remove b  (G ++ (b,v,_) :: (a,v, un_)) > NR b P'

                                                              
    G ++ (b,v,_)::  (c, h, _) :: (a,v, un_) > P1 | (NR c( *a(x).Q | a!b.Q)) -->
    ne ++ (b, v, _) :: remove b  (G ++  (b,v,_) :: (c, h, _):: (a,v,_)) > P'
    ____________________________________________________________
    G ++ (b,h,_) :: (c, h, _) :: (a,v,un_)  NR b (P1 | ( (NR c( *a(x).Q | a!c.Q)))) -->
    ne ++ (b, h, _) :: remove b  (G ++ (b,v,_) :: (c, h, _) :: (a,v,un_)) > NR b P' 
 *)
  
Lemma lts_after_tau_un: forall g  p1 p2 a1 a2 t g' nd_pf nd_pf1,
    sl_pos p1 ->
    incl (secLabs p1) (domain (hid_proj g)) ->
    NoDup (secLabs p1) ->
    lts g p1 (aTau a1 a2) g' p2 nd_pf ->
    In (a1, a2, vis, Chan un io t) g ->
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
  6:{assert (nd_pf' := pf1); 
     eapply sl_pos_nu in SLP;
       assert (SLP2 := SLP);
       try eapply IHLTS with (nd_pf1 := nd_pf') in SLP 
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
     eapply FinFun.Injective_map_NoDup;
       unfold FinFun.Injective;
       try intros [x1 x2] [y1 y2] INJ;
       try simpl in INJ; try inv INJ;
     try assert (x2 = y2); try   omega;
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
       assert (x2 = 0). omega.
       subst.
       eapply INCL, SLP2 in ABS2...
       omega.
       omega.

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
     eapply FinFun.Injective_map_NoDup;
       unfold FinFun.Injective;
       try intros [x1 x2] [y1 y2] INJ;
       try simpl in INJ; try inv INJ;
     try assert (x2 = y2); try   omega;
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
    assert (DOMEQ:
             (domain (h1 ++ (b1, b2, vis, t0) :: h2) =
                (domain (h1 ++ (b1, b2, hid, t0) :: h2)))).
    repeat rewrite domain_distr; simpl...
    rewrite DOMEQ; eapply in_removeEntry_cons_iff.
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
      assert (FYP: flagOf (h1 ++ (b1, b2, vis, t0) :: h2) (a1, a2) vis).
      eapply flagOf_hide_app...
      inv TYP; inv FYP.
      assert (f = vis).
      eapply flag_of_map with (g := h1 ++ (b1, b2, vis, t0) :: h2)...
      subst...
  }
  

  - eapply sl_pos_par_l in SLP as SLP1; eapply sl_pos_par_r in SLP as SLP2; simpl in SL;
      eapply incl_distr in SL as (SL1 &SL2);
      simpl in ND; eapply no_dup_distr in ND as (ND1 &ND2).
    specialize IHLTS with a1 a2 nd_pf1; intuition.
    destruct H as [b1 [b2 [fb [tb [ne [DIFF [INb [K1  K2]]]]]]]].
    exists b1 b2 fb tb ne...
    split...
    split...
    split... destruct K2 as [KA | KB]. left... 
    destruct KB as (rp &REPL &INCL &NEEQ).
    right. exists rp.
    split. eapply replParL...
    split. simpl. eapply incl_appr...
    assumption.
  - assert (ABS: Chan un io t = Chan lin io t0).
    eapply type_of_map with (g := g)...
    inversion ABS.
  -  assert (ABS: Chan un io t = Chan lin io t0).
     eapply type_of_map with (g := g)...
     inversion ABS.
     
  - clear IHLTS1 IHLTS2.
    assert (EQ0: Chan un io t = Chan un io t0).
    eapply type_of_map with (g := g)...
    inversion EQ0; subst t0.
    eapply lts_operations.lts_un_output_action with (t := t) (r := s1)in LTS1 as K1.
    eapply  lts_un_input_action with (t := t) (r := s) (pol := io) (nd_pf := pf2) in LTS2 as K2.
    subst g0.
    subst g'. simpl in K2. rewrite pairEq_eq_true in K2.
    
    clear K1. destruct K2 as (k & K2).  
    exists b1 b2 vis s k...
    split...
    eapply nonRecActions2 in LTS1 as DIFF; intuition.
    
    left; intuition; try discriminate...
    (*    simpl; try rewrite pairEq_eq_true...
    simpl; try rewrite pairEq_eq_true...
    simpl in ND; rewrite no_dup_iff in ND; intuition.
*)
    eapply lts_un_input_action_newEntries with (k:=k) (pf := pf2)in LTS2 as K3...
        destruct K3 as [KA | KB]. left; intuition; try discriminate...
    destruct KB as (rp &REPL &INCL &KEQ).
    right. exists rp. split.
    eapply replCom...
    split.
    simpl. eapply incl_appl...
    erewrite KEQ,identif_seclabs_of_dep_relabel,max_same_domain with (l := domain g),<-identif_seclabs_of_dep_relabel,newEntries_cons...
    eapply proposition27.in_preserves_max,in_g_in_domain...
    eapply sl_pos_par_l in SLP as SLP1; eapply sl_pos_par_r in SLP as SLP2; unfold sl_pos, pos in *;  intros; specialize SLP2 with x1 x2; intuition auto.
    subst g3.
    intros ABS; unfold incl in INCL; specialize INCL with (b1, b2); intuition.
    unfold incl in SL; simpl in SL; specialize SL with (b1, b2); assert (In (b1, b2) (secLabs q1 ++ secLabs p1)); try eapply in_app_iff; try left; intuition.
    assert (FYP: flagOf g (b1, b2) hid)...
    inversion FYP; subst.
    assert (hid = vis).
    eapply flag_of_map with (g := g)...
    discriminate.
    (*intros. unfold iff; split.
    eapply in_removeEntry_cons_iff,in_g_in_domain...
    eapply in_removeEntry_cons_iff,in_g_in_domain...
    simpl; rewrite pairEq_eq_true...
    inversion H as [_ [TP _]].
    eapply type_plus_comm in TP...*)
    simpl; rewrite pairEq_eq_true...
    all:eauto.
     simpl; rewrite pairEq_eq_true...
    simpl in ND; eapply no_dup_iff in ND as (ND1 &ND2 &_)...
    inversion H as [_ [TP _]];
      eapply type_plus_comm...
    simpl in SL; eapply incl_app_inv in SL as (INCL &_);
      eapply incl_preserves_max in INCL...
    specialize hid_proj_incl with g as HID;
      eapply incl_preserves_max in HID.
    assert (MAX : max (domain g) =  max (domain ((b1, b2, vis, s1) :: removeEntry (b1, b2) g))).
    eapply max_same_domain,in_removeEntry_cons_iff,in_g_in_domain...
    rewrite <-MAX; try omega...
  -  clear IHLTS1 IHLTS2.
     assert (EQ0: Chan un io t = Chan un io t0).
     eapply type_of_map with (g := g)...
     inversion EQ0; subst t0.
     subst g'. eapply  lts_un_input_action with (t := t) (r := s) (pol := io)in LTS2 as K. destruct K as (k &DIS &K2).
     assert (K3 := K2).
     eapply lts_un_input_action_newEntries with (k := k) (pf := pf2)in  LTS2 as K.
     exists b1 b2 hid s k...
     split...
     split...
     destruct K as [KA | [rp KB]].
     subst k. split.
     subst g3; simpl; erewrite pairEq_eq_true...
     left...
     
     destruct KB as (REPL &INCL &KEQ).
     split; subst g3;simpl. erewrite pairEq_eq_true...
     right. exists rp; split...
     split. eapply incl_appl... 
     erewrite KEQ,identif_seclabs_of_dep_relabel,max_same_domain with (l := domain g),<-identif_seclabs_of_dep_relabel,newEntries_cons...
     eapply in_preserves_max,in_g_in_domain...
     eapply sl_pos_par_l in SLP as SLP1; eapply sl_pos_par_r in SLP as SLP2; unfold sl_pos, pos in *;  intros; specialize SLP2 with x1 x2; intuition auto.
     intros ABS; unfold incl in INCL; specialize INCL with (b1, b2); intuition.
     assert (OPEN: In (b1, b2) (secLabs p1))...
     simpl in ND; eapply no_dup_disjoint,disjoint_commute in ND; eapply disjoint_absurd with (m := secLabs q1)...
     (*intros. unfold iff; split.
     eapply in_removeEntry_cons_iff,in_g_in_domain...
     eapply in_removeEntry_cons_iff,in_g_in_domain...
*)
     simpl; rewrite pairEq_eq_true...
     inversion H as [_ [TP _]].
     eapply type_plus_comm in TP.
     simpl in K2; erewrite pairEq_eq_true in K2.
     eauto.
     eauto.
     simpl; rewrite pairEq_eq_true...
     eauto.
     simpl in ND; eapply no_dup_iff in ND; intuition. 
     subst g0; eapply T_Entry; right; eapply removeEntry_in...
     eauto.
     inversion H as [_ [TP _]];
       eapply type_plus_comm...
     eauto.
     subst g0.
     simpl in SL; eapply incl_distr in SL as (INCL &_);
       eapply incl_preserves_max in INCL...
     specialize hid_proj_incl with g as HID;
       eapply incl_preserves_max in HID.
     assert (MAX : max (domain g) =  max (domain ((b1, b2, ill, s1) :: removeEntry (b1, b2) g))).
     eapply max_same_domain,in_removeEntry_cons_iff,in_g_in_domain...
     rewrite <-MAX; try omega...

     Unshelve.
     all:eauto.
Qed.

Lemma replication_not_out g p a1 a2 b1 b2 g1 p1 nd_pf q1:
  lts g p (aOut a1 a2 b1 b2) g1 p1 nd_pf -> replication p p1 q1 -> False.
Proof with eauto.
  introv LTS ABS; dependent induction LTS; try inv ABS...
  clear IHLTS.
  inv LTS; try inv H5...
  inverts H9 as [ABS | CONT]; try inv ABS; try discriminate...
  assert (~In (b1, b2, hid, t0) (removeEntry (b1, b2) g)).
  eapply no_dup_not_in_removeEntry...
  contradiction.
  simpl in H9; intuition.
Qed.

Lemma secLabs_nil: forall g q nd_pf,
    sl_pos q -> 
    nil =
      newEntries g
        (secLabs (dep_relabel q (domain g) nd_pf))
        (max (domain g)) ->
    (secLabs (dep_relabel q (domain g) nd_pf))  = nil.
Proof with eauto.
  intros g q nd_pf SLP NE.
  case_eq (secLabs (dep_relabel q (domain g) nd_pf)).
  intros...
  intros (b1, b2) l SL.
  rewrite SL in NE. simpl in NE.
  erewrite identif_seclabs_of_dep_relabel in SL.
  assert (ABS: exists x, (fun x : name * name => (fst x, snd x + max (domain g))) x =  (b1, b2) /\ In x (secLabs q)).
  eapply in_map_iff; erewrite SL...
  destruct ABS as ((c1, c2)& EQ &ABS). simpl in EQ.
  case_eq ( InB (b1, b2) g). intros. destruct b.
  eapply inB_implies_In_2,in_g_in_domain in H.
  inversion EQ.
  unfold sl_pos, pos in SLP; specialize SLP with c1 c2; intuition. eapply proposition27.in_preserves_max in H.
  omega.
  rewrite H in NE.
  destruct (InB (b1, b2 - max (domain g)) g).
  inversion NE.
Qed.

Lemma lts_un_input_action_newEntries_secLabs:
  forall (*g p a1 a2 b1 b2 r g1 p1 nd_pf k pol t rp,*)
    g p a1 a2 b1 b2 g1 p1 nd_pf pol t rp,
    In (a1, a2, vis, Chan un pol t) g ->
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
  - introv REPL; inv REPL; simpl; eapply incl_appl;
      try eapply IHLTS; try eapply in_app_iff in IN as [IN | CONT];
      try eapply in_app_iff; try inv CONT; try inv H0; try discriminate...
    repeat right...
Qed.

Lemma lts_un_tau_action_newEntries_secLabs:
  forall g p a1 a2 g1 p1 nd_pf pol t rp,
    In (a1, a2, vis, Chan un pol t) g ->
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
  - introv REPL; inv REPL; simpl; eapply incl_appl;
      try eapply IHLTS; try eapply in_app_iff in IN as [IN | CONT];
      try eapply in_app_iff; try inv CONT; try inv H0; try discriminate...
    repeat right...
Qed.

Lemma cons_removeEntry_iff: forall x b1 b2 f t g,
    NoDup (domain g) ->
    In (b1, b2) (domain g) ->
    In x (domain ((b1, b2, f, t) :: removeEntry (b1, b2) g)) <-> In x (domain g).
Proof with eauto.
  intros. unfold iff. split. 
  eapply lts_no_dup.in_removeEntry_cons_iff...
  eapply lts_no_dup.in_removeEntry_cons_iff...
Qed.

Hint Resolve cons_removeEntry_iff.

Lemma lts_un_tau_action_newEntries_1 p g a1 a2 c1 c2 t r p1 pf q:
   sl_pos p ->
    incl (secLabs p) (domain (hid_proj g)) ->
    NoDup (secLabs p) ->
    (a1, a2) <> (c1, c2) ->
    In (a1, a2, vis, Chan un io t) g ->
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

        (*assert (EQ: (b1, b2) = (c1, c2)).
        eapply lts_payload_aIn with (k := nil)(b1 := c1) (b2 := c2) (rg := r)in LTS2 as EQ...
        simpl in INCL. eapply incl_distr in INCL as (INCL1 &INCL2).
        assert (incl (domain (hid_proj g)) (domain g)) by eapply hid_proj_incl...
        eapply proposition27.incl_preserves_max,incl_tran...
        eapply in_g_in_domain...*)
        
(*        destruct f.
        right; repeat simpl; try rewrite pairEq_eq_true...
        contradiction.
        left; repeat simpl; try rewrite pairEq_eq_true...
*)        
        inversion EQ; subst c1 c2.

        assert (REPL1: replication q1 q2 q).
        inversion REPL; subst...
        assert (False). eapply replication_not_out... contradiction.
        eapply lts_un_input_action_newEntries_secLabs  with (rp := q) in LTS2 as INCLRP...
        assert (SLP2: sl_pos q).
        unfold sl_pos, pos in *; intros x1 x2; simpl in SLP; specialize
                                                               SLP with x1 x2; intuition.
        assert (INCL1: incl (secLabs q1) (domain g)).
        assert (incl (domain (hid_proj g)) (domain g)) by eapply hid_proj_incl...
        simpl in INCL. eapply incl_distr in INCL as (INCL1 & INCL2); eapply incl_tran...
        
       
        
        subst g'.
        eapply lts_un_input_action_newEntries_2 with (k := nil) (q := q) (pf := nd_pf)in LTS2 as K...
        subst g0.
        assert (SLNIL: (secLabs (dep_relabel q (domain ((b1, b2, vis, s1) :: removeEntry (b1, b2) g)) nd_pf)) = nil). eapply secLabs_nil...
        erewrite identif_seclabs_of_dep_relabel,max_same_domain with (l := domain g),<-identif_seclabs_of_dep_relabel in SLNIL...
        
        
        subst g0; simpl; rewrite pairEq_eq_true...
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
        
 (*   -   intros; clear IHLTS1 IHLTS2.
        assert (nd_pf: NoDup (domain g')).   
        subst g' g0; eapply no_dup_cons_removeEntry...
        simpl in INCL. assert (INCLt := INCL);
          eapply incl_distr in INCLt as (INCL1 &INCL2).
        assert (incl (domain (hid_proj g)) (domain g)) by eapply hid_proj_incl...

        subst g' g0.

        assert (REPL1: replication q1 q2 q).
        inversion REPL; subst...
        eapply lts_un_input_action_newEntries_secLabs  with (rp := q) in LTS2 as INCLRP...
        assert (SLP2: sl_pos q).
        unfold sl_pos, pos in *; intros x1 x2; simpl in SLP; specialize
                                                               SLP with x1 x2; intuition.
       (* assert (INCL1: incl (secLabs q1) (domain g)).
        assert (incl (domain (hid_proj g)) (domain g)) by eapply hid_proj_incl...
        simpl in INCL. eapply incl_distr in INCL as (INCL1 & INCL2); eapply incl_tran...
        assert (f = vis).
        simpl in H3; inverts H3 as EQ2;
          try inv EQ2; try tauto. 
        assert(~ In (b1, b2, vis, s) (removeEntry (b1, b2) g)).
        eapply no_dup_not_in_removeEntry...
        contradiction.
        subst f.*)

        assert (LTS3 := LTS2).
        eapply lts_un_input_action with (t :=t0) in LTS3 as (k &DIS &EQ3);
        try inv H; intuition; try eapply type_plus_comm...
        simpl in EQ3. rewrite pairEq_eq_true in EQ3; subst g3.
        
        eapply lts_un_input_action_newEntries_2 with (k := nil) (q := q) (pf := nd_pf) (r :=r)in LTS2 as K...
        assert (SLNIL: (secLabs (dep_relabel q (domain ((c1, c2, ill, s1) :: removeEntry (c1, c2) g)) nd_pf)) = nil). eapply secLabs_nil...
        erewrite identif_seclabs_of_dep_relabel,max_same_domain with (l := domain g),<-identif_seclabs_of_dep_relabel in SLNIL...
        
        simpl;rewrite pairEq_eq_true...

        destruct k...
        assert (False).
        destruct p as [[[b1 b2] f1] t1]. 
        case_eq ( pair_eq (b1, b2) (c1, c2)); intros ABS;
          simpl in x; try rewrite ABS in x.
        assert (LEN: List.length (k ++ (c1, c2, vis, r) :: removeEntry (c1, c2) g) =
                  List.length(removeEntry (c1, c2) g)).
        rewrite x...
        rewrite app_length in LEN; simpl in LEN; try omega.
        assert (LEN: List.length ((b1, b2, f1, t1) :: removeEntry (c1, c2) (k ++ (c1, c2, vis, r) :: removeEntry (c1, c2) g)) =
                  List.length(removeEntry (c1, c2) g)).
        rewrite x...
        rewrite removeEntry_app_shift in LEN;
          simpl in LEN; try rewrite pairEq_eq_true in LEN; simpl in LEN;
          try rewrite app_length in LEN;  try omega.

        intros ABS2.
        eapply disjoint_absurd with (x0 := (c1, c2))...
        simpl; right...
        simpl...

        contradiction.

        
        simpl in ND; eapply no_dup_iff in ND; intuition.
        simpl...
        assert (MAX: max (domain ((c1, c2, ill, s1) :: removeEntry (c1, c2) g)) = max (domain g)).
        eapply max_same_domain...
        rewrite MAX...
        eapply incl_preserves_max,incl_tran...
        right; eapply removeEntry_in...


*)
    - introv REPL.
      assert (REPL2: replication p p' q).
      inv REPL...

      case_eq (pair_eq (b1,b2) (c1,c2)); intros PEQ;
        try rewrite <-pairEq_eq in PEQ; inversion PEQ;
        try subst c1 c2.

      *   assert (ND2 := ND). simpl in ND; eapply no_dup_iff in ND as (IH &_ &_); eapply IHLTS with  (r := t')in IH; clear IHLTS...
          assert (EQD: domain (h1 ++ (b1, b2, vis, t0) :: h2) =
                        domain (h1 ++ (b1, b2, hid , t0) :: h2)).
      repeat (simpl; try  rewrite domain_distr)...
      assert (pf' := pf1).
     eapply lts_rewrite_pf with (pf1 := pf') in LTS...
     gen pf1; rewrite EQD; intros...
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
(*   In (c1, c2) (domain (h1 ++ (b1, b2, vis, t0) :: h2))
 *)
     simpl in *; rewrite domain_distr in *...
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
     
      * assert (ND2 := ND).
      simpl in ND; eapply no_dup_iff in ND as (IH &_ &_); eapply IHLTS in IH; clear IHLTS...

      (* secLabs (dep_relabel q (domain (h1 ++ (b1, b2, hid, t0) :: h2)) pf) = []*)
      assert (EQD: domain (h1 ++ (b1, b2, vis, t0) :: h2) =
                        domain (h1 ++ (b1, b2, hid , t0) :: h2)).
      repeat (simpl; try  rewrite domain_distr)...
      assert (pf' := pf1).
     eapply lts_rewrite_pf with (pf1 := pf') in LTS...
     gen pf1; rewrite EQD; intros...
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
(*   In (c1, c2) (domain (h1 ++ (b1, b2, vis, t0) :: h2))
 *)
     simpl in *; rewrite domain_distr in *...
     (*  In (a1, a2, vis, Chan un io t) (h1 ++ (b1, b2, vis, t0) :: h2)*)
     eapply in_app_iff in INa as [IN | CONT]; eapply in_app_iff...
     inversion CONT as [ABS3|CONT3]; try inv ABS3; try discriminate.
     repeat right...
     
     (*  h' ++ (b1, b2, vis, t') :: h'' ~= [] ++ (c1, c2, f, ?r) :: removeEntry (c1, c2) (h1 ++ (b1, b2, vis, t0) :: h2)*)
     rewrite <-pairEq_neq in PEQ;
       try erewrite typeEnv_eq_change_flag_removeEntry...
 Qed.
 
 Hint Resolve removeEntry_length_01.
 
Hint Resolve removeEntry_length_02.
 
 Lemma lts_un_tau_action_newEntries_1h:
  forall (g : typeEnv) (p : dproc) (a1 a2 c1 c2 : name) (r t : piType) 
    (g1 : typeEnv) (p1 : dproc) (pf : NoDup (domain g)) (q : dproc)
    (k : list (name * name * flag * piType)),
   sl_pos p ->
    incl (secLabs p) (domain (hid_proj g)) ->
    NoDup (secLabs p) ->
    (a1, a2) <> (c1, c2) ->
    In (a1, a2, vis, Chan un io t) g ->
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
        (*assert (EQ: (b1, b2) = (c1, c2)).
        eapply lts_payload_aIn with (k := nil)(b1 := c1) (b2 := c2) (f2 := vis) in LTS2 as EQ. inversion EQ; subst...
        all:eauto.
        simpl in INCL. eapply incl_distr in INCL as (INCL1 &INCL2).
        assert (incl (domain (hid_proj g)) (domain g)) by eapply hid_proj_incl...
        eapply proposition27.incl_preserves_max,incl_tran...
        all:eauto.
        Unshelve.
        eapply in_g_in_domain...*)
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
        try eapply in_g_in_domain...
        assert (LEN3 : length (removeEntry (c1, c2) g) =
                         length (removeEntry (b1, b2) g))...
        repeat rewrite app_length,LEN3 in LEN1; simpl in LEN1;repeat rewrite app_length,LEN3 in LEN1; simpl in LEN1. 
        assert (NIL: length k' = 0) by omega.
        assert (k'=nil);eapply length_zero_iff_nil...
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

     (*   eapply lts_un_input_action_newEntries with (k := ne) (pf := nd_pf)in LTS2 as K.
        destruct K as [NENIL | (rp  & REPL2 &INCL4 &NEEQ)].
        subst.*)
       
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
        omega.
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
        omega.
        simpl in ABS2; rewrite ABS2,pairEq_eq_true in LEN.
        omega.
        subst...
        simpl in ND; eapply no_dup_iff in ND; intuition.
        simpl...
        all:subst g' g0|| eauto...
        assert (incl (domain (hid_proj g)) (domain g)) by eapply hid_proj_incl...
        eapply proposition27.incl_preserves_max,incl_tran, incl_iff with (m1 :=domain g)...
        right. eapply removeEntry_in...
     - Case hide.
       assert (HIDE: 
                lts  (h1 ++ (b1, b2, hid, t0) :: h2) (dNu b1 b2 p) (aTau a1 a2) (h' ++ (b1, b2, hid, t') :: h'') (dNu b1 b2 p') pf)...
       
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
     erewrite lts_un_tau_action_newEntries_1 with (p := p)
                                                  (p1 := p')...
     rewrite hid_proj_app,domain_distr in *; simpl in *;
       introv IN; assert (IN2 := IN); eapply INCL1 in IN;
       eapply in_app_iff in IN; inv IN as [IN3 | CONT];
       eapply in_app_iff...
     inv CONT.  try eapply disjoint_absurd...
     right...

      rewrite domain_distr in *; simpl in *; eapply in_app_iff in INa; inv INa as [INa2 | CONT]; eapply in_app_iff...
     inv CONT; try inv H0; try contradiction.
     repeat right...
     simpl in *; try rewrite pairEq_eq_true in *.

     erewrite domain_distr; eapply in_app_iff; right; simpl...
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
        intros...
      erewrite dep_relabel_rewrite_pf...
      * 
      
    
      assert (IH: secLabs (dep_relabel q (domain (h1 ++ (b1, b2, vis, t0) :: h2)) pf1) = []).
      eapply IHLTS; clear IHLTS...
     rewrite hid_proj_app,domain_distr in *; simpl in *.
     introv IN; assert (IN2 := IN); eapply INCL1,in_app_iff in IN;
       try destruct IN as [IN | CONT]; try eapply in_app_iff...
     inv CONT.
     try eapply disjoint_absurd...
     right...
     rewrite domain_distr in *; simpl in *; eapply in_app_iff in INb; inv INb as [INb2 | CONT]; eapply in_app_iff...
     rewrite domain_distr in *; simpl in *; eapply in_app_iff in INa; inv INa as [INa2 | CONT]; eapply in_app_iff...
     inv CONT; try inv H0; try contradiction.
     repeat right...
     simpl in *; try rewrite pairEq_eq_true in *.

    
     
     
     erewrite typeEnv_eq_change_flag_removeEntry with (h := nil)...
     simpl...
     
     
     erewrite <-pairEq_neq in H1...
     
      (* secLabs (dep_relabel q (domain (h1 ++ (b1, b2, hid, t0) :: h2)) pf) = []*)
      assert (EQD: domain (h1 ++ (b1, b2, vis, t0) :: h2) =
                        domain (h1 ++ (b1, b2, hid , t0) :: h2)).
      repeat (simpl; try  rewrite domain_distr)...
      assert (pf' := pf1).
     eapply lts_rewrite_pf with (pf1 := pf') in LTS...
     gen pf1; rewrite EQD; intros...
     erewrite dep_relabel_rewrite_pf...
(*  incl (secLabs p) (domain (hid_proj (h1 ++ (b1, b2, vis, t0) :: h2))) *)
(*     try rewrite hid_proj_app in *; simpl in *.
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
(*   In (c1, c2) (domain (h1 ++ (b1, b2, vis, t0) :: h2))
 *)
     simpl in *; rewrite domain_distr in *...
     (*  In (a1, a2, vis, Chan un io t) (h1 ++ (b1, b2, vis, t0) :: h2)*)
     eapply in_app_iff in INa as [IN | CONT]; eapply in_app_iff...
     inversion CONT as [ABS3|CONT3]; try inv ABS3; try discriminate.
     repeat right...
     
     (*  h' ++ (b1, b2, vis, t') :: h'' ~= [] ++ (c1, c2, f, ?r) :: removeEntry (c1, c2) (h1 ++ (b1, b2, vis, t0) :: h2)*)
     rewrite <-pairEq_neq in PEQ.
     erewrite typeEnv_eq_change_flag_removeEntry with
       (f1 := hid) (h := nil); simpl in *;
       try rewrite pairEq_eq_true in *...

 *)
     Unshelve.
     all:eauto.
 Qed.
 
 Hint Resolve lts_un_tau_action_newEntries_1
      lts_un_tau_action_newEntries_1h.

 
        
  Lemma lts_un_tau_action_newEntries_2:
  forall (g : typeEnv) (p : dproc) (a1 a2 b1 b2 : name) (r t : piType) 
    (g1 : typeEnv) (p1 : dproc) (pf: NoDup (domain g)) (q : dproc)
    (k : list (name * name * flag * piType)),
   sl_pos p ->
    incl (secLabs p) (domain (hid_proj g)) ->
    NoDup (secLabs p) ->
    In (a1, a2, vis, Chan un io t) g ->
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
    
    eapply lts_after_tau_un with (nd_pf1 := pf) in LTS as K...

    assert (INCL1: incl (secLabs p) (domain g)).    assert (incl (domain (hid_proj g)) (domain g)) by eapply hid_proj_incl... eapply incl_tran...
    assert (MAX: max (secLabs p) <= max (domain g)).
    eapply proposition27.incl_preserves_max in INCL.
    assert (INCL2: incl (domain (hid_proj g)) (domain g)) by eapply hid_proj_incl...
    eapply proposition27.incl_preserves_max in INCL2.
    omega.
    

    
    destruct K as
      [c1 [c2 [f [tb [ne [DIFF [INc [G1EQ NEEQ]]]]]]]].
    assert (HYP: S(length (removeEntry (c1, c2) g)) = S(length (removeEntry (b1, b2) g))).
    
    repeat rewrite removeEntry_length_0; try assumption;
      try eapply in_g_in_domain...

        assert (LEN: length (removeEntry (c1, c2) g) = length (removeEntry (b1, b2) g)) by omega.

    
    destruct EQ as [OPT1 | OPT2].
    destruct G1EQ as [(OPT3 &NILL) | (OPT4 & EQF)].
    rewrite OPT3 in OPT1.
    assert (EQ: (c1, c2, f, tb) = (b1, b2, vis, r) /\ ne = k).
    eapply length_inv_tl...
    destruct EQ as [EQ1 EQ2]; inv EQ1.
    inv NEEQ.
    erewrite lts_un_tau_action_newEntries_1...
    
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
    assert (List.length k = 0) by omega.
    eapply length_zero_iff_nil...
    subst.

    erewrite lts_un_tau_action_newEntries_1h;
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

    
    
   (* assert (EQ2: ((b1, b2, vis, r) :: nil) ++ removeEntry (b1, b2) g =
                (b1, b2, vis, r) :: removeEntry (b1, b2) g)...
    erewrite <-EQ2,app_assoc...
    eapply removeEntry_length...
    eapply in_g_in_domain...


    assert (q = rp). eapply replication_unique... subst rp.
    destruct ne.
    assert (LEN: List.length ( (c1, c2, hid, tb) :: nil) = List.length (k ++ (b1, b2, vis, r) :: nil)).
    rewrite ABS...
    erewrite app_length in LEN;simpl in LEN.
    assert (EQ: Datatypes.length k = 0) by omega.
    rewrite length_zero_iff_nil in EQ; subst.
    inversion ABS.
    assert (TAIL: ne = nil /\ p0 = (b1, b2, vis, r) \/
                        exists l', ne = l' ++ (b1, b2, vis, r) :: nil).
    eapply inv_tail...
    destruct TAIL as [(EQNIL & OPT3) | (l' &OPT4)].
    subst p0.
    assert (DIS: disjoint (domain g) (domain (newEntries g (secLabs (dep_relabel q (domain g) pf)) (max (domain g))))).
    eapply new_entries_disjoint...
    (* sl_pos q *)
    unfold sl_pos, pos in *; intros; unfold incl in INCLQ; specialize SLP with x1 x2; intuition.
    (*  max (secLabs q) <= max (domain g) *)
    eapply proposition27.incl_preserves_max, incl_tran...
    eapply disjoint_absurd,in_g_in_domain...
    rewrite <-Heqne...
    
    assert (DIS: disjoint (domain g) (domain (newEntries g (secLabs (dep_relabel q (domain g) pf)) (max (domain g))))).
    eapply new_entries_disjoint...
    (* sl_pos q *)
    unfold sl_pos, pos in *; intros; unfold incl in INCLQ; specialize SLP with x1 x2; intuition.
    (*  max (secLabs q) <= max (domain g) *)
     eapply proposition27.incl_preserves_max, incl_tran...
    eapply disjoint_absurd,in_g_in_domain...
    erewrite <-Heqne,OPT4; right.
    erewrite in_app_iff; right...
    assumption.
*)

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
      omega.
      rewrite removeEntry_app_shift in LEN2;
        try eapply in2_nIn_iff;
        simpl in LEN2; try rewrite pairEq_eq_true in LEN2...
      rewrite app_length in LEN2.
      assert (LEN3: length k = 0) by omega.
      rewrite length_zero_iff_nil in LEN3; subst k.

   
      
    erewrite lts_un_tau_action_newEntries_1h;
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
      omega.
      rewrite removeEntry_app_shift in LEN2;
        try eapply in2_nIn_iff;
        simpl in LEN2; try rewrite pairEq_eq_true in LEN2...
      rewrite app_length in LEN2.
      assert (LEN3: length k = 0) by omega.
      rewrite length_zero_iff_nil in LEN3; subst k.
    erewrite lts_un_tau_action_newEntries_1h;
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

Lemma lts_middle: forall g1 g2 g k1 k pf1 pf2 pf nd_pf1 nd_pf p1 act a1 a2 b1 b2 q1 p t,
    tEnv_split g1 g2 g pf1 pf2 pf ->
    lts g1 p1 act k1 q1 nd_pf1 ->
    lts g p1 act k q1 nd_pf ->
    (typeOf g1 (a1, a2) (Chan lin p t) \/
       typeOf g2 (a1, a2) (Chan lin p t) \/
       typeOf g (a1, a2)  (Chan lin p t)) ->
    ((act = aIn a1 a2 b1 b2 ->
      In (a1, a2, vis, Chan lin inp t ) g1 /\
        In (a1, a2, vis, Chan lin empty t ) g2 /\
        In (a1, a2, vis, Chan lin inp t ) g) /\
       (act = aOut a1 a2 b1 b2 ->
        In (a1, a2, vis, Chan lin out t ) g1 /\
          In (a1, a2, vis, Chan lin empty t ) g2 /\
          In (a1, a2, vis, Chan lin out t ) g) /\
       (act = aTau a1 a2->
        (In (a1, a2, vis, Chan lin io t ) g1 /\
           In (a1, a2, vis, Chan lin empty t ) g2 /\
           In (a1, a2, vis, Chan lin io t ) g) \/
          (In (a1, a2, hid, Chan lin io t ) g1 /\
             In (a1, a2, ill, Chan lin empty t ) g2 /\
             In (a1, a2, hid, Chan lin io t ) g)
    )).
Proof with eauto.
  intros g1 g2 g k1 k pf1 pf2 pf nd_pf1 nd_pf p1 act a1 a2 b1 b2 q1 p t
    TS LTS1 LTS TYP.
  split; intros; subst.

  
  - assert (IN1a: In (a1, a2, vis, Chan lin inp  t ) g1).
    assert (LTS' := LTS1).
    destruct TYP as [TYP1a | [TYP2a | TYPa]].
    + eapply type_of_in_action in LTS' as
          [tt [TYP1a' | [TYP1a' | TYP1a']]].
      *
        inversion TYP1a; inversion TYP1a'; subst.
        assert (EQ: f = f0 /\ Chan lin p t = Chan lin inp tt).
        eapply in_isMap with (g := g1)...
        destruct EQ; inversion H1; subst.
        assert (f0 = vis).
        eapply lts_vis_subject with (a1 := a1) (a2 := a2) in LTS1 as F1.
        inversion F1; subst.
        eapply flag_of_map with (x := (a1, a2)) (g := g1)...
        eauto. subst...

      * inversion TYP1a; inversion TYP1a'; subst.
        assert (f = f0 /\ Chan lin p t = Chan un inp tt).
        eapply in_isMap...
        destruct H0; discriminate.

      * inversion TYP1a; inversion TYP1a'; subst.
        assert (f = f0 /\ Chan lin p t = Chan un io tt).
        eapply in_isMap...
        destruct H0; discriminate.

    + inversion TYP2a; subst.
      eapply sub_split.tsub_payload with (pf := pf) in H as (pp &K).
      inversion K; subst.
      assert (W: exists p1 : pol, typeOf g1 (a1, a2) (Chan lin p1 t)). eapply sub_split.tsuper_payload...
      destruct W as [pp1 W].

      eapply type_of_in_action in LTS' as
          [tt [TYP1a' | [TYP1a' | TYP1a']]].

      * inversion W; inversion TYP1a'; subst.
        
        assert (EQ: Chan lin inp tt = Chan lin pp1 t).
        eapply type_of_map with (g := g1)...
        inversion EQ; subst.
        
        assert (f1 = vis).
        eapply lts_vis_subject with (a1 := a1) (a2 := a2) in LTS1 as F1.
        inversion F1; subst...
        eauto. subst...

      *  assert (Chan lin pp1 t = Chan un inp tt).
         eapply type_of_map with (g := g1)...
         inversion H0.

      * assert (Chan lin pp1 t = Chan un io tt).
        eapply type_of_map with (g := g1)...
        inversion H0.
      * eapply split_comm...
    + inversion TYPa; subst. 
      eapply sub_split.tsuper_payload with (pf1 := pf1) in H as [pp1 TYP1a].
      eapply type_of_in_action in LTS' as
          [tt [TYP1a' | [TYP1a' | TYP1a']]].
      *
        inversion TYP1a; inversion TYP1a'; subst.
        assert (EQ: f0 = f1 /\ Chan lin pp1 t = Chan lin inp tt).
        eapply in_isMap with (g := g1)...
        destruct EQ; inversion H1; subst.
        assert (f1 = vis).
        eapply lts_vis_subject with (a1 := a1) (a2 := a2) in LTS1 as F1.
        inversion F1; subst.
        eapply flag_of_map with (x := (a1, a2)) (g := g1)...
        eauto. subst...

      * inversion TYP1a; inversion TYP1a'; subst.
        assert (f0 = f1 /\ Chan lin pp1 t = Chan un inp tt).
        eapply in_isMap...
        destruct H0; discriminate.

      * inversion TYP1a; inversion TYP1a'; subst.
        assert (f0 = f1 /\ Chan lin pp1 t = Chan un io tt).
        eapply in_isMap...
        destruct H0; discriminate.

      * eauto.

    + split...
      eapply lts_vis_subject with (a1 := a1) (a2 := a2) in LTS1 as F1.
      inversion F1; subst.
      eapply sub_split.tsub_in with (pf := pf) in IN1a as K. destruct K as [K | ABS].
      inversion K; subst.
      eapply sub_split.fsub_vis with (pf := pf) in H as K2.
      inversion K2; subst.
      assert (f = vis).
      eapply flag_of_map with (g := g)...
      subst.
      eapply sub_split.tsuper_payload_r with (pf2 := pf2) in H0 as W.
      destruct W as (pp2 & W); inversion W; subst.
      eapply sub_split.fsuper_vis with (pf2 := pf2) in H1 as K3.
      destruct K3 as [_ K3]; inversion K3; subst.
      assert (f = vis).
      eapply flag_of_map with (g := g2)...
      subst.
      assert (pol_plus inp pp2 inp).
      eapply split_cons_remove.split_plus_lin with (pf1 := pf1)...
      inversion H4; subst; intuition auto.
      all:eauto.
      inversion ABS; subst.
      eapply type_of_in_action in LTS as [tt [ABS2 | [ABS2 | ABS2]]].
      assert (ABS3: Chan lin io t = Chan lin inp tt).
      eapply type_of_map with (g := g)...
      inversion ABS3.
      assert (ABS3: Chan lin io t = Chan un inp tt).
      eapply type_of_map with (g := g)...
      inversion ABS3.
      assert (ABS3: Chan lin io t = Chan un io tt).
      eapply type_of_map with (g := g)...
      inversion ABS3.

  - split; intros; subst.

    assert (IN1a: In (a1, a2, vis, Chan lin out t ) g1).
    assert (LTS' := LTS1).
    destruct TYP as [TYP1a | [TYP2a | TYPa]].
    + eapply type_of_out_action in LTS' as
          [tt [TYP1a' | [TYP1a' | TYP1a']]].
      *
        inversion TYP1a; inversion TYP1a'; subst.
        assert (EQ: f = f0 /\ Chan lin p t = Chan lin out tt).
        eapply in_isMap with (g := g1)...
        destruct EQ; inversion H1; subst.
        assert (f0 = vis).
        eapply lts_vis_subject with (a1 := a1) (a2 := a2) in LTS1 as F1.
        inversion F1; subst.
        eapply flag_of_map with (x := (a1, a2)) (g := g1)...
        eauto. subst...

      * inversion TYP1a; inversion TYP1a'; subst.
        assert (f = f0 /\ Chan lin p t = Chan un out tt).
        eapply in_isMap...
        destruct H0; discriminate.

      * inversion TYP1a; inversion TYP1a'; subst.
        assert (f = f0 /\ Chan lin p t = Chan un io tt).
        eapply in_isMap...
        destruct H0; discriminate.

    + inversion TYP2a; subst.
      eapply sub_split.tsub_payload with (pf := pf) in H as (pp &K).
      inversion K; subst.
      assert (W: exists p1 : pol, typeOf g1 (a1, a2) (Chan lin p1 t)). eapply sub_split.tsuper_payload...
      destruct W as [pp1 W].

      eapply type_of_out_action in LTS' as
          [tt [TYP1a' | [TYP1a' | TYP1a']]].

      * inversion W; inversion TYP1a'; subst.
        
        assert (EQ: Chan lin out tt = Chan lin pp1 t).
        eapply type_of_map with (g := g1)...
        inversion EQ; subst.
        
        assert (f1 = vis).
        eapply lts_vis_subject with (a1 := a1) (a2 := a2) in LTS1 as F1.
        inversion F1; subst...
        eauto. subst...

      *  assert (Chan lin pp1 t = Chan un out tt).
         eapply type_of_map with (g := g1)...
         inversion H0.

      * assert (Chan lin pp1 t = Chan un io tt).
        eapply type_of_map with (g := g1)...
        inversion H0.
      * eapply split_comm...
    + inversion TYPa; subst. 
      eapply sub_split.tsuper_payload with (pf1 := pf1) in H as [pp1 TYP1a].
      eapply type_of_out_action in LTS' as
          [tt [TYP1a' | [TYP1a' | TYP1a']]].
      *
        inversion TYP1a; inversion TYP1a'; subst.
        assert (EQ: f0 = f1 /\ Chan lin pp1 t = Chan lin out tt).
        eapply in_isMap with (g := g1)...
        destruct EQ; inversion H1; subst.
        assert (f1 = vis).
        eapply lts_vis_subject with (a1 := a1) (a2 := a2) in LTS1 as F1.
        inversion F1; subst.
        eapply flag_of_map with (x := (a1, a2)) (g := g1)...
        eauto. subst...

      * inversion TYP1a; inversion TYP1a'; subst.
        assert (f0 = f1 /\ Chan lin pp1 t = Chan un out tt).
        eapply in_isMap...
        destruct H0; discriminate.

      * inversion TYP1a; inversion TYP1a'; subst.
        assert (f0 = f1 /\ Chan lin pp1 t = Chan un io tt).
        eapply in_isMap...
        destruct H0; discriminate.

      * eauto.

    + split...
      eapply lts_vis_subject with (a1 := a1) (a2 := a2) in LTS1 as F1.
      inversion F1; subst.
      eapply sub_split.tsub_out with (pf := pf) in IN1a as K. destruct K as [K | ABS].
      inversion K; subst.
      eapply sub_split.fsub_vis with (pf := pf) in H as K2.
      inversion K2; subst.
      assert (f = vis).
      eapply flag_of_map with (g := g)...
      subst.
      eapply sub_split.tsuper_payload_r with (pf2 := pf2) in H0 as W.
      destruct W as (pp2 & W); inversion W; subst.
      eapply sub_split.fsuper_vis with (pf2 := pf2) in H1 as K3.
      destruct K3 as [_ K3]; inversion K3; subst.
      assert (f = vis).
      eapply flag_of_map with (g := g2)...
      subst.
      assert (pol_plus out pp2 out).
      eapply split_cons_remove.split_plus_lin with (pf1 := pf1)...
      inversion H4; subst; intuition auto.
      all:eauto.
      inversion ABS; subst.
      eapply type_of_out_action in LTS as [tt [ABS2 | [ABS2 | ABS2]]].
      assert (ABS3: Chan lin io t = Chan lin out tt).
      eapply type_of_map with (g := g)...
      inversion ABS3.
      assert (ABS3: Chan lin io t = Chan un out tt).
      eapply type_of_map with (g := g)...
      inversion ABS3.
      assert (ABS3: Chan lin io t = Chan un io tt).
      eapply type_of_map with (g := g)...
      inversion ABS3.
    +  eapply type_of_tau_Action in LTS1 as (m &tt &[IN | INH]).
       assert (m = lin /\ t = tt).
       * destruct TYP as [TYP1 | [TYP2 | TYP]].
         inversion TYP1; subst.
         assert (EQ: Chan m io tt = Chan lin p t).
         eapply type_of_map with (g := g1) (x := (a1,a2))...
         inversion EQ...
         inversion TYP2; subst.
         eapply sub_split.tsub_payload_r with (pf := pf) in H as (pp & H). inversion H; subst.
         eapply sub_split.tsuper_payload with (pf1 := pf1) in H0 as (pp1 & K).
         inversion K; subst.
         assert (EQ: Chan m io tt = Chan lin pp1 t).
         eapply type_of_map with (g := g1)...
         inversion EQ...
         all:eauto.
         inversion TYP; subst. eapply sub_split.tsuper_payload with (pf1 := pf1) in H as (pp1 & K).
         inversion K; subst.
         assert (EQ: Chan m io tt = Chan lin pp1 t).
         eapply type_of_map with (g := g1)...
         inversion EQ...
         all:eauto.
       * destruct H; subst.
         assert (K: exists p1 : pol, typeOf g (a1, a2) (Chan lin p1 tt)).
         eapply sub_split.tsub_payload... 
         destruct K as [pp K]; inversion K; subst.
         eapply sub_split.tsuper_payload_r with (pf2 := pf2) in H
             as W.
         destruct W as (pp2 & W). inversion W; subst.
         assert (PP: pol_plus io pp2 pp).
         eapply split_cons_remove.split_plus_lin with (pf1 := pf1)...
         inversion PP; subst.
         eapply sub_split.fsub_vis with (pf := pf) in IN as K1.
         inversion K1; subst.
         assert (f = vis).
         eapply flag_of_map with (g := g)...
         subst.
         eapply sub_split.fsuper_vis with (pf2 := pf2) in H as K2.
         destruct K2 as [_ K2].
         assert (f0 = vis).
         eapply flag_of_map with (g := g2)...
         subst...
         all:eauto.
       * right.

         assert (m = lin /\ t = tt).
         ** destruct TYP as [TYP1 | [TYP2 | TYP]].
            inversion TYP1; subst.
            assert (EQ: Chan m io tt = Chan lin p t).
            eapply type_of_map with (g := g1) (x := (a1,a2))...
            inversion EQ...
            inversion TYP2; subst.
            eapply sub_split.tsub_payload_r with (pf := pf) in H as (pp & H). inversion H; subst.
            eapply sub_split.tsuper_payload with (pf1 := pf1) in H0 as (pp1 & K).
            inversion K; subst.
            assert (EQ: Chan m io tt = Chan lin pp1 t).
            eapply type_of_map with (g := g1)...
            inversion EQ...
            all:eauto.
            inversion TYP; subst. eapply sub_split.tsuper_payload with (pf1 := pf1) in H as (pp1 & K).
            inversion K; subst.
            assert (EQ: Chan m io tt = Chan lin pp1 t).
            eapply type_of_map with (g := g1)...
            inversion EQ...
            all:eauto.
         ** destruct H; subst.
            assert (K: exists p1 : pol, typeOf g (a1, a2) (Chan lin p1 tt)).
            eapply sub_split.tsub_payload... 
            destruct K as [pp K]; inversion K; subst.
            eapply sub_split.tsuper_payload_r with (pf2 := pf2) in H
                as W.
            destruct W as (pp2 & W). inversion W; subst.
            assert (PP: pol_plus io pp2 pp).
            eapply split_cons_remove.split_plus_lin with (pf1 := pf1)...
            inversion PP; subst.
            split...
            eapply sub_split.fsub_hid with (pf := pf) in INH as K1.
            inversion K1; subst.
            assert (f = hid).
            eapply flag_of_map with (g := g)...
            subst.
            eapply fsuper_hid with (pf2 := pf2) in H as K2.
            destruct K2 as [[_ K2] | [_ ABS]].
            assert (f0 = ill).
            eapply flag_of_map with (g := g2)...
            subst...

            inverts ABS as ABS2;
              eapply split_operations_2.finv_hid_r in ABS2...
            assert (hid = ill).
            eapply flag_of_map with (g := g1)...
            discriminate.
            
            all:eauto.
            
            
Qed.


