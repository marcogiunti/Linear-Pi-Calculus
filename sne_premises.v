Require Import
         Bool List Omega PeanoNat Program.Equality
        ListAddOns Max RemoveEntry Domain
        header
        operations pi_syntax 
        pairEq type_system
        semantics
        type_system_rules
        disjoint_newEntries
        type_operations_1
        no_dup_split_no_dup
        split_cons_remove.
        

 Require Import CpdtTactics LibTactics.


 Lemma in_removeEntry_cons_iff_1 : forall g a1 a2 b1 b2 f t f1 t1,
     NoDup (domain g) ->
     In (a1, a2, f, t) g ->
    In (b1, b2, f1, t1) g ->
    forall x,
      In x g <-> In x ((a1, a2, f, t) :: (b1, b2, f1, t1) :: (removeEntry (a1, a2) (removeEntry (b1, b2) g))).
Proof with eauto using no_dup_isMap.
  intros. split; intros.
 destruct x as (((x1 &x2) &f2) &t2).
 case_eq (pair_eq (a1, a2) (x1, x2)). intros EQ. rewrite <-pairEq_eq in EQ. inversion EQ; subst.
 assert (EQ2: f =f2 /\ t = t2).
 eapply in_isMap with (g := g)...
 destruct EQ2; subst...
 intros NEQ.
 case_eq (pair_eq (b1, b2) (x1, x2)). intros EQ2. rewrite <-pairEq_eq in EQ2. inversion EQ2; subst.
 assert (EQ3: f1 =f2 /\ t1 = t2).
 eapply in_isMap with (g := g)...
 destruct EQ3; subst; right...
 intros NEQ2.
 repeat right...
 rewrite <-pairEq_neq in NEQ, NEQ2; eapply removeEntry_in,removeEntry_in...
 inversion H2; subst...
 inversion H3; subst...
 destruct x as (((x1 &x2) &f2) &t2); eapply in_removeEntry...
Qed.

Lemma in_removeEntry_cons_iff_2 : forall x g a1 a2 b1 b2 f1 t1 f2 t2,
             NoDup (domain g) ->
  In (a1, a2) (domain g) ->
  In (b1, b2) (domain g) ->
  (a1, a2) <> (b1, b2) ->
  In x (domain g) <->
  In x
    (domain
       ((a1, a2, f1, t1) :: (b1, b2, f2, t2) :: removeEntry (a1, a2) (removeEntry (b1, b2) g))).
  Proof with eauto.
    intros x g a1 a2 b1 b2 f1 t1 f2 t2
           ND IN1 IN2 DIFF.
    assert (ND2: NoDup
    (domain
       ((a1, a2, f1, t1) :: (b1, b2, f2, t2) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)))).
    eapply no_dup_cons_removeEntry_app...
     eapply in_domain_in_g in IN1 as (f4 &t4 & IN1).
   eapply in_domain_in_g in IN2 as (f5 &t5 & IN2).
    intuition.
    - eapply in_domain_in_g in H as (f3 &t3 & IN).
      specialize in_removeEntry_cons_iff_1
        with g a1 a2 b1 b2 f4 t4 f5 t5  (a,b, f3, t3) as IFF. eapply IFF in ND as K; intuition.
      eapply in_g_in_domain in H1; simpl in *...
    - simpl in *; destruct H; try inversion H0; subst.
        try inversion H; subst;eapply in_g_in_domain...
        destruct H; try inversion H0; subst.
        try inversion H; subst;eapply in_g_in_domain...
        eapply in_domain_in_g in H as (ff &tt &H).
        eapply in_g_in_domain,in_removeEntry...
  Qed.

 
Lemma split_iff: forall g1 g2 g h pf1 pf2 pf pfh (nd_pf: NoDup (domain g)) (nd_pfh: NoDup (domain h)),
    tEnv_split g1 g2 g pf1 pf2 pf ->
    (forall x,
        In x g <-> In x h) ->
    tEnv_split g1 g2 h pf1 pf2 pfh.
Proof with eauto.
  intros g1 g2 g h pf1 pf2 pf pfh nd_pf nd_pfh TS IFF.
  generalize dependent h.
  dependent induction TS.
  - intros. subst.
  assert (forall x, ~In x h);
    intros. specialize IFF with x; intuition.
  assert (h = nil).
  eapply length_zero_iff_nil. destruct h...
  specialize H with p; intuition.
  subst. apply SpNil...
  - intros.
  assert (pfh' : isMap (removeEntry n h)).
  eapply isMap_removeEntry...
  specialize IHTS with (pfh := pfh').
  assert ((forall x : name * name * flag * piType, In x g''' <-> In x (removeEntry n h))).
  subst g'''.
  eapply removeEntry_iff...
  eapply SpLin with (pf''' := pfh').
  eauto. eauto. eauto. eauto. 
  eapply IHTS.
  subst. eapply no_dup_removeEntry_no_dup...
  eapply no_dup_removeEntry_no_dup...
  eauto.
  eauto.
  specialize IFF with (n, f', Chan lin p' t).
  inversion H4; inversion H5; subst.
  assert (f' = f1 /\ t0 = Chan lin p' t).
  eapply in_isMap with (g := g3)...
  intuition; subst; intuition auto.
  eauto.
   specialize IFF with (n, f', Chan lin p' t).
  inversion H4; inversion H5; subst.
  assert (f' = f1 /\ t0 = Chan lin p' t).
  eapply in_isMap with (g := g3)...
  intuition; subst; intuition auto.
  eauto.
  - intros.
    assert (pfh' : isMap (removeEntry n h)).
  eapply isMap_removeEntry...
  specialize IHTS with (pfh := pfh').
  assert ((forall x : name * name * flag * piType, In x g''' <-> In x (removeEntry n h))).
   subst g'''.
    eapply removeEntry_iff...
  assert (NoDup (domain g''')). subst g'''...
  intuition.  eapply SpUn with (pf''' := pfh').
  eauto. eauto. eauto. eauto. eauto.
  inversion H3. subst.
  specialize IFF with (n, f', t0); intuition...
   inversion H4. subst.
   specialize IFF with (n, f0, Chan un p t); intuition...
  - intros.
    assert (pfh' : isMap (removeEntry n h)).
  eapply isMap_removeEntry...
  specialize IHTS with (pfh := pfh').
  assert ((forall x : name * name * flag * piType, In x g''' <-> In x (removeEntry n h))).
   subst g'''.
  eapply removeEntry_iff...
  assert (NoDup (domain g''')). subst g'''...
  intuition. eapply SpTop with (pf''' := pfh').
  eauto. eauto. eauto. eauto. eauto.
  inversion H3. subst.
  specialize IFF with (n, f', t); intuition...
   inversion H4. subst.
   specialize IFF with (n, f0, Top); intuition...
   Unshelve. all:eauto.
Qed.
    
   
   Lemma lts_vis_subject: forall a a1 a2 b1 b2 g p g1 p1 pf,
       lts g p a g1 p1 pf ->
       (a = aIn a1 a2 b1 b2 \/ a = aOut a1 a2 b1 b2) ->
       flagOf g (a1, a2) vis.
   Proof with eauto.
     intros a a1 a2 b1 b2 g p g1 p1 pf LTS [AIN | AOUT].
     dependent induction LTS; intuition; try discriminate;
       inversion AIN; subst...
     destruct H as (DIFF1 &DIFF2).
     inverts H1 as IN; eapply in_app_iff in IN as [IN | CONT];
       econstructor; try eapply in_app_iff.
     left...
     inverts CONT as IN; try inv IN; try contradiction...
     repeat right...
     dependent induction LTS; intuition; try discriminate;
       inversion AOUT; subst...
     inversion H0; subst.
     inversion H1. inversion H2; subst.
     eapply  nonRecActions2 in LTS; contradiction.
     eapply in_removeEntry in H2...
      destruct H as (DIFF1 &DIFF2).
     inverts H1 as IN; eapply in_app_iff in IN as [IN | CONT];
       econstructor; try eapply in_app_iff.
     left...
     inverts CONT as IN; try inv IN; try contradiction...
     repeat right...
   Qed.

   Hint Constructors disjoint_2.
     
 Lemma disjoint_iff: forall {A} (l1 l2 m : list A),
     disjoint l1 m ->
     (forall x, In x l1 <-> In x l2) ->
     disjoint l2 m.
 Proof with eauto.
   intros A l1 l2 m DIS IFF.
   induction m...
   erewrite disjoint_commute,<-disjoint_car...
   erewrite disjoint_commute in DIS.
   eapply disjoint_l_cons in DIS as [DIS NIN];
     erewrite disjoint_commute in DIS; intuition.
   erewrite IFF in NIN.
   erewrite disjoint_commute; econstructor...
   eapply disjoint_commute...
 Qed.

  Lemma incl_newEntries_domain: forall g l m,
      incl (domain (newEntries g l m))  l.
  Proof with eauto.
    induction l; intros; simpl;
      try destruct a as [a1 a2]...
    case_eq (InB (a1, a2) g); intros.
    case_eq b; intros; subst.
    intuition.
    destruct (InB (a1, a2 - m) g);
      simpl; intuition.
  Qed.
