Require Import
        Bool List Omega PeanoNat Program.Equality
        ListAddOns Max RemoveEntry Domain Classical
        NewEntries
        Coq.Logic.Classical_Prop
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
        (*split_existential_2*) 
        type_checking_1
        lts_no_dup 
        proposition27
        disjoint_newEntries
        type_system_rules
        split_cons_remove.

Require Import CpdtTactics LibTactics.

Hint Resolve typeCheck_rewrite_pf.





Hint Resolve removeEntry_iff.




Lemma isMap_not_in : forall x f t g,
    ~ In x (domain g) ->
    isMap g ->
    isMap ((x, f, t) :: g).
Proof with eauto.
  introv NIN pf.
  econstructor; intuition.
  inversion H0; inversion H1; try inversion H2; try inversion H; subst; try tauto.
  - inversion H1; try inversion H3; subst; try tauto.
    eapply in_g_in_domain in H2; intuition.
  - eapply in_g_in_domain in H; intuition.
  - eapply pf...
  -  inversion H0; inversion H1; try inversion H2; try inversion H; subst; try tauto.
     + inversion H1; try inversion H3; subst; try tauto.
       eapply in_g_in_domain in H2; intuition.
     + eapply in_g_in_domain in H; intuition.
     + eapply pf...
Qed.

Lemma in_diff_not_in : forall x1 x2 a1 a2 f t g,
    ~ In (x1, x2) (domain g) ->
    In (a1, a2, f, t) g ->
    (x1, x2) <> (a1, a2).
Proof with eauto.
  introv NIN IN ABS; inverts ABS;
    try eapply in_g_in_domain in IN;
    intuition.
Qed.  


Hint Resolve isMap_not_in map_nil_eq.

Lemma gcons_iff: forall g1 g2 pf1 pf2 (nd_pf1 : NoDup (domain g1)) (nd_pf2 : NoDup(domain g2)),
    cons g1 pf1 ->
    (forall x, In x g1 <-> In x g2) ->
    cons g2 pf2.
  intros g1 g2 pf1 pf2 nd_pf1 nd_pf2 CONS IFF.
  Proof with eauto.
    revert dependent g2.
    dependent induction CONS.
    - intros; assert (g2 = nil). destruct g2...
      specialize IFF with p; subst; assert (In p (p :: g2))...
      intuition. subst; econstructor...
    - intros.
      assert (K := H); inversion H; subst.
      assert ((forall x : name * name * flag * piType, In x (removeEntry n g) <-> In x (removeEntry n g2))).
      eapply removeEntry_iff...
      assert (ND: NoDup (domain (removeEntry n g))).
      eapply no_dup_removeEntry_no_dup...
      eapply IHCONS in ND.
      specialize  IFF with  (n, f, Top).
      intuition; eapply Co_top... assumption.
      eapply removeEntry_iff...
      intuition.
    - intros.
      assert (K := H); inversion H; subst.
      assert ((forall x : name * name * flag * piType, In x (removeEntry n g) <-> In x (removeEntry n g2))).
      eapply removeEntry_iff...
      assert (ND: NoDup (domain (removeEntry n g))).
      eapply no_dup_removeEntry_no_dup...
      eapply IHCONS in ND.
      specialize  IFF with  (n, f, Chan un p t).
      intuition; eapply Co_un... assumption.
      eapply removeEntry_iff...
      intuition.
    - intros.
      assert (K := H); inversion H; subst.
      assert ((forall x : name * name * flag * piType, In x (removeEntry n g) <-> In x (removeEntry n g2))).
      eapply removeEntry_iff...
      assert (ND: NoDup (domain (removeEntry n g))).
      eapply no_dup_removeEntry_no_dup...
      eapply IHCONS in ND.
      specialize  IFF with  (n, f, Chan lin empty t).
      intuition; eapply Co_lin... assumption.
      eapply removeEntry_iff...
      intuition.
      Unshelve.  all:eauto.
  Qed.

  Hint Resolve gcons_iff.

  Lemma cons_lin: forall a1 a2 f p t g pf,
      cons g pf -> In (a1, a2, f, Chan lin p t) g -> p = empty.
  Proof with eauto.
    intros a1 a2 f p t g pf CONS IN.
    revert dependent a1. revert dependent a2. revert dependent p. revert dependent t.
    dependent induction CONS.
    - intros; subst; inversion IN.
    - intros; case_eq (pair_eq (a1, a2) n); intros EQ; try rewrite <-pairEq_eq in EQ; subst. 
      assert (Top = Chan lin p t).
      eapply type_of_map with (g :=g)... discriminate.
      rewrite <-pairEq_neq in EQ;
        eapply removeEntry_in in IN...
    - intros; case_eq (pair_eq (a1, a2) n); intros EQ; try rewrite <-pairEq_eq in EQ; subst. 
      assert (ABS: Chan un p t = Chan lin p0 t0).
      eapply type_of_map with (g :=g)... inversion ABS.
      rewrite <-pairEq_neq in EQ;
        eapply removeEntry_in in IN...
    - intros; case_eq (pair_eq (a1, a2) n); intros EQ; try rewrite <-pairEq_eq in EQ; subst. 
      assert (EQ: Chan lin empty t = Chan lin p t0).
      eapply type_of_map with (g :=g)...
      inversion EQ...
      rewrite <-pairEq_neq in EQ;
        eapply removeEntry_in in IN...
  Qed.

  Lemma cons2_rewrite_pf: forall g pf1 pf2,
      cons g pf1 -> cons g pf2.
  Proof with eauto.
    intros g pf1 pf2 CO.
    dependent induction CO.
    subst. apply Co_nil...
    eapply Co_top...
    eapply Co_un...
    eapply Co_lin...
  Qed.

  Lemma isMap_distr : forall g1 g2,
                 isMap (g1 ++ g2) ->
                 isMap g1 /\ isMap g2.
Proof with eauto.
  intros; split; unfold isMap in *; intros; specialize H with x f1 t1 f2 t2; eapply H.
  assert (In (x, f1, t1) (g1 ++ g2)). eapply in_or_app...
  assert (In (x, f2, t2) (g1 ++ g2)). eapply in_or_app...
  all:intuition auto; eapply in_or_app...
Qed.

Lemma gcons_abs g pf :
  ~(cons g pf) ->
  exists a1 a2 f p t,
    In (a1, a2, f, Chan lin p t) g /\ p <> empty.
Proof with eauto.
  introv NOT.
  induction g.
  assert (cons nil pf).
  econstructor...
  contradiction.
  destruct a as [[[a1 a2] f] t].
  destruct t; try destruct m.
  destruct p.
  - eapply isMap_cons in pf as pf';
      specialize IHg with (pf := pf').
    assert (NOT2: ~ cons g pf'). intros ABS.
    assert (pf'' : isMap (removeEntry (a1, a2) ((a1, a2, f, Chan lin empty t) :: g))).
    eapply isMap_removeEntry...
    assert (cons ((a1, a2, f, Chan lin empty t) :: g) pf). eapply Co_lin with (pf' := pf'')...
    gen pf''.
    simpl. rewrite pairEq_eq_true; intros...
    contradiction.
    eapply IHg in NOT2  as (b1 &b2 &f1 &p1 &t1 &In &DIFF).
    exists b1 b2 f1 p1 t1; intuition.
  - exists a1 a2 f inp t; intuition; try discriminate.
  - exists a1 a2 f out t; intuition; try discriminate.
  - exists a1 a2 f io t; intuition; try discriminate.
  -  eapply isMap_cons in pf as pf';
       specialize IHg with (pf := pf').
     assert (NOT2: ~ cons g pf'). intros ABS.
     assert (pf'' : isMap (removeEntry (a1, a2) ((a1, a2, f, Chan un p t) :: g))).
     eapply isMap_removeEntry...
     assert (cons ((a1, a2, f, Chan un p t) :: g) pf). eapply Co_un with (pf' := pf'')...
     gen pf''.
     simpl. rewrite pairEq_eq_true; intros...
     contradiction.
     eapply IHg in NOT2  as (b1 &b2 &f1 &p1 &t1 &In &DIFF).
     exists b1 b2 f1 p1 t1; intuition.
    -  eapply isMap_cons in pf as pf';
       specialize IHg with (pf := pf').
     assert (NOT2: ~ cons g pf'). intros ABS.
     assert (pf'' : isMap (removeEntry (a1, a2) ((a1, a2, f, Top) :: g))).
     eapply isMap_removeEntry...
     assert (cons ((a1, a2, f, Top) :: g) pf). eapply Co_top with (pf' := pf'')...
     gen pf''.
     simpl. rewrite pairEq_eq_true; intros...
     contradiction.
     eapply IHg in NOT2  as (b1 &b2 &f1 &p1 &t1 &In &DIFF).
     exists b1 b2 f1 p1 t1; intuition.
Qed.

  Lemma gcons_cons : forall a1 a2 f t g pf1 pf,
    cons ((a1, a2, f, t) :: g) pf1 ->
    cons  g pf.
  Proof with eauto using cons2_rewrite_pf, isMap_distr.
    introv CONS.
    assert (~(cons g pf) -> False).
    intros ABS. 
    eapply gcons_abs in ABS as (b1 &b2 &f1 &p1 &t1 &IN &DIFF).
    assert (p1 = empty).
    eapply cons_lin...
    right...
    contradiction.
    eapply Peirce.
    intuition.     
Qed. 

Hint Constructors cons.


Lemma gcons_removeEntry: forall a1 a2 g pf pf1,
    cons g pf ->
    cons (removeEntry (a1, a2) g) pf1.
Proof with eauto using isMap_removeEntry.
  introv CONS;
  dependent induction g;
    try destruct a as [[[b1 b2] ff1] tt1].
  eauto.
  assert (CONS2 :=CONS).
  assert (pf2 : isMap g). eapply isMap_cons...
  eapply gcons_cons with (pf := pf2) in CONS2 as K;
      eapply IHg in K as IH;
      gen pf1; simpl;
        case_eq (pair_eq (b1, b2) (a1, a2));
        try intros PEQ; intros.
    eauto.
    assert (EQ: pair_eq (b1, b2) (b1, b2) = true).
    eapply pairEq_eq...
    assert (pf3: isMap (removeEntry (b1, b2) ((b1, b2, ff1, tt1) :: removeEntry (a1, a2) g))).
   simpl; rewrite EQ...
    destruct tt1; try destruct m.
    + destruct p.
      * eapply Co_lin with (n := (b1, b2)) (pf' := pf3). simpl... 
        gen pf3; simpl; rewrite EQ; intros...
      * assert (inp = empty).
        eapply cons_lin with (a1 := b1) (a2 := b2) (g := (b1, b2, ff1, Chan lin inp tt1) :: g)... discriminate.
      * assert (out = empty).
        eapply cons_lin with (a1 := b1) (a2 := b2) (g := (b1, b2, ff1, Chan lin out tt1) :: g)... discriminate.
      * assert (io = empty).
        eapply cons_lin with (a1 := b1) (a2 := b2) (g := (b1, b2, ff1, Chan lin io tt1) :: g)... discriminate.
    + eapply Co_un with (n := (b1, b2)) (pf' := pf3). simpl... 
        gen pf3; simpl; rewrite EQ; intros...
    +  eapply Co_top with (n := (b1, b2)) (pf' := pf3). simpl... 
       gen pf3; simpl; rewrite EQ; intros...
       Unshelve.
       assert (pf' := pf); eapply isMap_cons in pf'...
Qed.

  Lemma cons_distr: forall g1 g2 pf1 pf2 pf,
      cons (g1 ++ g2) pf <-> (cons g1 pf1  /\ cons g2 pf2).
  Proof with eauto using cons_lin,gcons_cons, cons2_rewrite_pf.
    split; intros.
    - induction g1, g2.
      econstructor...
      split. econstructor...
      revert dependent pf; rewrite  app_nil_l;
        intros...
      split.
      revert dependent pf; rewrite  app_nil_r;
        intros...
      econstructor...
      split.
      destruct a as [[[a1 a2] f] t];
        destruct t;
        try destruct m.
      + assert (p0 = empty).
        eapply cons_lin... try left...
        subst.
        assert (pf' : isMap (removeEntry (a1, a2) ((a1, a2, f, Chan lin empty t) :: g1))).
        unfold removeEntry; rewrite pairEq_eq_true;
          eapply isMap_cons...
        assert (pf'' : isMap (removeEntry (a1, a2) (((a1, a2, f, Chan lin empty t) :: g1) ++ p :: g2))).
        eapply isMap_removeEntry...
        rewrite <-app_comm_cons in pf'';
        revert dependent pf'';
          unfold removeEntry;
           try rewrite pairEq_eq_true; intros.
        eapply Co_lin with (pf' := pf')...
        revert dependent pf'.
        unfold removeEntry;
          try rewrite pairEq_eq_true; intros;
            eapply IHg1...
        Unshelve.
        all:assumption.
      +   assert (pf' : isMap (removeEntry (a1, a2) ((a1, a2, f, Chan un p0 t) :: g1))).
        unfold removeEntry; rewrite pairEq_eq_true;
          eapply isMap_cons...
         assert (pf'' : isMap (removeEntry (a1, a2) (((a1, a2, f, Chan un p0 t) :: g1) ++ p :: g2))).
        eapply isMap_removeEntry...
        rewrite <-app_comm_cons in pf'';
        revert dependent pf'';
          unfold removeEntry;
           try rewrite pairEq_eq_true; intros.
        eapply Co_un with (pf' := pf')...
        revert dependent pf'.
        unfold removeEntry;
          try rewrite pairEq_eq_true; intros;
            eapply IHg1...
        
        Unshelve.
        all:assumption.
      +  assert (pf' : isMap (removeEntry (a1, a2) ((a1, a2, f,Top) :: g1))).
        unfold removeEntry; rewrite pairEq_eq_true;
          eapply isMap_cons...
          assert (pf'' : isMap (removeEntry (a1, a2) (((a1, a2, f, Top) :: g1) ++ p :: g2))).
        eapply isMap_removeEntry...
        rewrite <-app_comm_cons in pf'';
        revert dependent pf'';
          unfold removeEntry;
           try rewrite pairEq_eq_true; intros.
        eapply Co_top with (pf' := pf')...
        revert dependent pf'.
        unfold removeEntry;
          try rewrite pairEq_eq_true; intros;
            eapply IHg1...
        Unshelve.
        all:assumption.
      + destruct a as [[[a1 a2] f] t].
         assert (pf'' : isMap (removeEntry (a1, a2) (((a1, a2, f, t) :: g1) ++ p :: g2))).
        eapply isMap_removeEntry...
        rewrite <-app_comm_cons in pf'';
        revert dependent pf'';
          unfold removeEntry;
           try rewrite pairEq_eq_true; intros.
        eapply   IHg1.
        assert (pf' : isMap (removeEntry (a1, a2)
                                         ((a1, a2, f, t) :: g1))).
        eapply isMap_removeEntry...
        unfold removeEntry in *;
          try rewrite pairEq_eq_true in *...
        revert dependent pf;
          rewrite <-app_comm_cons; intros.
        assert (pf' : isMap (removeEntry (a1, a2)
                                         ((a1, a2, f, t) :: g1 ++ p :: g2))).
        eapply isMap_removeEntry...
        assert (cons (removeEntry (a1, a2) ((a1, a2, f, t) :: g1 ++ p :: g2)) pf').
        eapply gcons_removeEntry...
        unfold removeEntry in *;
          try rewrite pairEq_eq_true in *...
        Unshelve. all: try assumption.
    - induction g1, g2;
      revert dependent pf;
      try rewrite app_nil_l;
      try rewrite app_nil_r; intros; intuition.
      eauto.
      eauto.
      destruct a as [[[a1 a2] f] t].
      assert (pff1: isMap (removeEntry (a1, a2) ((a1, a2, f, t) :: g1))).
      eapply isMap_removeEntry...
      unfold removeEntry in pff1;
         try rewrite pairEq_eq_true in pff1.
      destruct t; try destruct m.
      + assert (p0 = empty). inversion H0... 
        subst.
        assert (pf' : isMap (removeEntry (a1, a2) ((a1, a2, f, Chan lin empty t) :: g1))).
        unfold removeEntry; rewrite pairEq_eq_true;
          eapply isMap_cons...
        assert (pf'' : isMap (removeEntry (a1, a2) (((a1, a2, f, Chan lin empty t) :: g1) ++ p :: g2))).
        eapply isMap_removeEntry...
        rewrite <-app_comm_cons in pf'';
       
          eapply Co_lin with (pf' := pf'').
        econstructor; try left...
        revert dependent pf''.
        unfold removeEntry;
          try rewrite pairEq_eq_true; intros;
            eapply IHg1...
        Unshelve. all: try assumption.

        +  assert (pf' : isMap (removeEntry (a1, a2) ((a1, a2, f, Chan un p0 t) :: g1))).
        unfold removeEntry; rewrite pairEq_eq_true;
          eapply isMap_cons...
        assert (pf'' : isMap (removeEntry (a1, a2) (((a1, a2, f, Chan un p0 t) :: g1) ++ p :: g2))).
        eapply isMap_removeEntry...
        rewrite <-app_comm_cons in pf'';
       
          eapply Co_un with (pf' := pf'').
        econstructor; try left...
        revert dependent pf''.
        unfold removeEntry;
          try rewrite pairEq_eq_true; intros;
            eapply IHg1...
        Unshelve. all: try assumption.

        +  assert (pf' : isMap (removeEntry (a1, a2) ((a1, a2, f, Top) :: g1))).
        unfold removeEntry; rewrite pairEq_eq_true;
          eapply isMap_cons...
        assert (pf'' : isMap (removeEntry (a1, a2) (((a1, a2, f, Top) :: g1) ++ p :: g2))).
        eapply isMap_removeEntry...
        rewrite <-app_comm_cons in pf'';
       
          eapply Co_top with (pf' := pf'').
        econstructor; try left...
        revert dependent pf''.
        unfold removeEntry;
          try rewrite pairEq_eq_true; intros;
            eapply IHg1...
        Unshelve. all: try assumption.
  Qed.
  
  Lemma no_dup_vis_proj: forall g,
      NoDup (domain g) ->
      NoDup (domain (vis_proj g)).
  Proof with eauto.
    introv nd_pf.
    induction g.
    simpl...
    destruct a as [[[a1 a2] f] t]; destruct f; simpl...
    econstructor...
    intros ABS.
    eapply vis_proj_incl in ABS.
    inversion nd_pf; contradiction.
  Qed.
  
  Lemma ill_proj_incl  : forall g,
    incl (domain (ill_proj g)) (domain g).
Proof.
  intros. induction g.
  unfold ill_proj. intuition. 
  unfold ill_proj. fold ill_proj.
  induction a. induction a. induction b0. intuition. 
  unfold domain. fold domain. intuition.      
  unfold domain. fold domain. intuition.
  unfold domain. fold domain. intuition.
  unfold domain. fold domain. intuition.
Qed.
  Lemma no_dup_ill_proj: forall g,
      NoDup (domain g) ->
      NoDup (domain (ill_proj g)).
 Proof with eauto.
    introv nd_pf.
    induction g.
    simpl...
    destruct a as [[[a1 a2] f] t]; destruct f; simpl...
    econstructor...
    intros ABS.
    eapply ill_proj_incl in ABS.
    inversion nd_pf; contradiction.
 Qed.

 

Lemma proj_distr: forall f (g1 g2 : typeEnv),
     (f= vis_proj \/ f = ill_proj) -> 
     f (g1 ++ g2) = f g1 ++ f g2.
Proof with eauto.
  intros f g1 g2 [H | H]; subst.
  - induction g1,g2...
  destruct a as [[[a1 a2] f] t]; destruct f;unfold vis_proj; fold vis_proj...
  assert (EQ : ((a1, a2, vis, t) :: g1) ++ nil =
               (a1, a2, vis, t) :: g1)...
  rewrite app_nil_r...
  rewrite EQ,app_nil_r;unfold vis_proj; fold vis_proj...
  destruct a as [[[a1 a2] f] t]; destruct p as [[[b1 b2] h] s];destruct f;  unfold vis_proj; fold vis_proj...
  assert (EQ: ((a1, a2, vis, t) :: g1) ++ (b1, b2, h, s) :: g2 =
              ((a1, a2, vis, t) :: (g1 ++ (b1, b2, h, s) :: g2)))...
  rewrite EQ; unfold vis_proj; fold vis_proj;rewrite IHg1...
  - induction g1,g2...
  destruct a as [[[a1 a2] f] t]; destruct f;unfold ill_proj; fold ill_proj...
  assert (EQ : ((a1, a2, ill, t) :: g1) ++ nil =
               (a1, a2, ill, t) :: g1)...
  rewrite app_nil_r...
  rewrite EQ,app_nil_r;unfold ill_proj; fold ill_proj...
  destruct a as [[[a1 a2] f] t]; destruct p as [[[b1 b2] h] s];destruct f;  unfold ill_proj; fold ill_proj...
  assert (EQ: ((a1, a2, ill, t) :: g1) ++ (b1, b2, h, s) :: g2 =
              ((a1, a2, ill, t) :: (g1 ++ (b1, b2, h, s) :: g2)))...
  rewrite EQ; unfold ill_proj; fold ill_proj;rewrite IHg1...
Qed.

Lemma proj_in: forall f (g : typeEnv) x,
     (f= vis_proj \/ f = ill_proj) -> 
     In x (f g) ->
     In x g.
Proof with eauto.
  introv EQ IN;
    destruct x as [[[a1 a2] ff] tt];
    dependent induction g; inv EQ; subst;
      try destruct a as [[[b1 b2] ff1] tt1];
      try destruct ff1; simpl in *; intuition...
Qed.  
Lemma in_vis_proj: forall a1 a2 t g,
    In (a1, a2, vis, t) g->
    In (a1, a2, vis, t) (vis_proj g).
Proof with eauto.
  intros. 
  eapply in_split in H as (l1 &l2 &IN); subst.
  erewrite proj_distr. erewrite in_app_iff; right;simpl...
  left...
Qed.


Lemma in_ill_proj: forall a1 a2 t g,
    In (a1, a2, ill, t) g->
    In (a1, a2, ill, t) (ill_proj g).
Proof with eauto.
  intros. 
  eapply in_split in H as (l1 &l2 &IN); subst.
  erewrite proj_distr,in_app_iff; right;simpl...
Qed.


  Lemma vis_proj_in: forall a f t g,
      In (a, f, t) (vis_proj g) ->
      f = vis.
  Proof with eauto.
    introv IN; induction g. simpl in *; intuition.
    destruct a0 as [[[a1 a2] ff] tt]; destruct ff; simpl in *.
    eauto. eauto. destruct IN as [IN1 | IN2]; try inversion IN1...
Qed.     

  Lemma ill_proj_in: forall a f t g,
      In (a, f, t) (ill_proj g) ->
      f = ill.
  Proof with eauto.
    introv IN; induction g. simpl in *; intuition.
    destruct a0 as [[[a1 a2] ff] tt]; destruct ff; simpl in *.
    eauto.  destruct IN as [IN1 | IN2]; try inversion IN1...
    eauto.
Qed.   

  Lemma vis_proj_iff : forall g1 g2,
      (forall x, In x g1 <-> In x g2) ->
      (forall x, In x (vis_proj g1) <-> In x (vis_proj g2)).
  Proof with eauto using vis_proj_in.
    intuition.
    - assert (b0 = vis)...
      subst.
      eapply proj_in, H,in_vis_proj in H0...
    - assert (b0 = vis)...
      subst.
      eapply proj_in, H,in_vis_proj in H0...
  Qed. 
      
  Lemma ill_proj_iff : forall g1 g2,
      (forall x, In x g1 <-> In x g2) ->
      (forall x, In x (ill_proj g1) <-> In x (ill_proj g2)).
Proof with eauto using ill_proj_in.
    intuition.
    - assert (b0 = ill)...
      subst.
      eapply proj_in, H,in_ill_proj in H0...
    - assert (b0 = ill)...
      subst.
      eapply proj_in, H,in_ill_proj in H0...
  Qed. 

  Hint Resolve no_dup_vis_proj no_dup_ill_proj
       vis_proj_iff ill_proj_iff.


  
  Lemma typeCheck_impl:
    forall p g1 pf1 g2 pf2
           (nd_pf1 : NoDup (domain g1)) (nd_pf2 : NoDup (domain g2)),
      typeCheck g1 pf1 p ->
      (forall x, In x g1 <-> In x g2) ->
      typeCheck g2 pf2 p.
  Proof with eauto.
    intros p g1 pf1 g2 pf2 nd_pf1 nd_pf2 TC IFF.
    generalize dependent g2. 
    dependent induction TC.
    - intros. eapply TNil... 
    - intros. eapply TNew with (t := t).
      specialize IFF with (n, hid, t). intuition.
      assert (pf'' : isMap ((n, vis, t) :: removeEntry n g2)).
      apply cons_removeEntry...
      specialize IHTC with (pf2 := pf'').
      assert (nd_pf' : NoDup (domain ((n, vis, t) :: removeEntry n g))).
      apply no_dup_cons_removeEntry...
      apply IHTC in nd_pf'.
      eauto.
      eapply no_dup_cons_removeEntry...
      intros. specialize IFF with x. unfold iff; split; intros IN. inversion IN; try inversion H; subst...
      right. destruct x, p0;eapply removeEntry_in.
      intros ABS; subst.
      assert (~ In (n, f, p1) (removeEntry n g)). eapply no_dup_not_in_removeEntry... contradiction.
      eapply IFF...
      inversion IN; subst...
      right. destruct x, p0;eapply removeEntry_in.
      intros ABS; subst.
      assert (~ In (n, f, p1) (removeEntry n g2)). eapply no_dup_not_in_removeEntry... contradiction.
      eapply IFF... 
    - intuition. eapply TPar...
      eapply split_iff with (g := g)...
    - intuition.
      Case TOutL.
      assert (CASE: typeCheck g pf (dOut (fst u) (snd u) (fst v) (snd v) q)).
      specialize  Case with g pf u p t v t' q t1 t2 pf1...
      assert (NEQ: u <> v).
      assert (nonRec_typable (dOut (fst u) (snd u) (fst v) (snd v) q)).
      eapply typeCheck_object_neq_subject...
      unfold nonRec_typable in H3; fold nonRec_typable in H3; destruct u, v; intuition.
      eapply TOutL.
      eauto. eauto.
      specialize IFF with (u, vis, Chan lin p t); intuition.
      specialize IFF with (v, vis, t'); intuition.
      assert (nd_pf' : NoDup (domain ((u, vis, t1) :: (v, vis, t2) :: removeEntry v (removeEntry u g)))).
      rewrite removeEntry_swap.
      apply no_dup_cons_removeEntry_app...
      intuition.
      intuition.
      assert (pf' : isMap ((u, vis, t1) :: (v, vis, t2) :: removeEntry v (removeEntry u g2))).
      rewrite removeEntry_swap.
      apply cons_removeEntry_app...
      all:intuition.
      specialize H3 with (pf2 := pf').
      assert (NoDup (domain ((u, vis, t1) :: (v, vis, t2) :: removeEntry v (removeEntry u g2))) ).
      rewrite removeEntry_swap.
      apply no_dup_cons_removeEntry_app...
      all:intuition.
      assert (IFF2: forall x : name * name * flag * piType,
                 In x ((u, vis, t1) :: (v, vis, t2) :: removeEntry v (removeEntry u g)) <->
                 In x ((u, vis, t1) :: (v, vis, t2) :: removeEntry v (removeEntry u g2))).
      intros. split; intros IN. inversion IN; subst...
      inversion H3; subst... repeat right.
      specialize IFF with x. intuition.
      destruct x,p0. eapply removeEntry_in,removeEntry_in.
      intros ABS; subst.
      assert (~In (v, f, p1) (removeEntry v (removeEntry u g)))...
      intros ABS; subst.
      assert (~In (u, f, p1) (removeEntry v (removeEntry u g))). intros ABS2. eapply in_removeEntry in ABS2...
      assert (~In (u, f, p1) (removeEntry u g))...
      contradiction.
      eauto.
      inversion IN; subst...
      inversion H3; subst... repeat right.
      specialize IFF with x. intuition.
      destruct x,p0. eapply removeEntry_in,removeEntry_in.
      intros ABS; subst.
      assert (~In (v, f, p1) (removeEntry v (removeEntry u g2)))... 
      intros ABS2; subst.
      assert (~In (u, f, p1) (removeEntry v (removeEntry u g2))). intros ABS2. eapply in_removeEntry in ABS2...
      assert (~In (u, f, p1) (removeEntry u g2))...
      contradiction.
      all:eauto.
    - Case TOutUn.
      intros.
      assert (CASE: typeCheck g pf (dOut (fst u) (snd u) (fst v) (snd v) q)).
      specialize  Case with g pf u p t v t' q t2 pf1...
      assert (NEQ: u <> v).
      assert (nonRec_typable (dOut (fst u) (snd u) (fst v) (snd v) q)).
      eapply typeCheck_object_neq_subject...
      unfold nonRec_typable in H3; fold nonRec_typable in H3; destruct u, v;simpl in H3; eapply H3...
      eapply TOutUn.
      eauto. eauto.
      eapply IFF...  eapply IFF...
      eapply IHTC.
      
      all:try apply no_dup_cons_removeEntry...
      
      intros. split; intros IN. inversion IN; subst...
      repeat right.
      specialize IFF with x. 
      destruct x,p0. eapply removeEntry_in.
      intros ABS; subst.
      assert (~In (v, f, p1) (removeEntry v g))...
      eapply IFF...
      inversion IN; subst...
      specialize IFF with x.
      right.
      destruct x,p0. eapply removeEntry_in.
      intros ABS; subst.
      assert (~In (v, f, p1) (removeEntry v g2))...
      eapply IFF...
    - intros.
      eapply TInL.
      eauto. specialize IFF with (u, vis, Chan lin p t); intuition...
      intro. apply in_domain_in_g in H3.
      destruct H3 as [ff [tt IN]];
        specialize IFF with (x, ff, tt).
      apply IFF in IN. apply in_g_in_domain in IN; intuition.

      erewrite max_same_domain with (l := domain g).
      eauto.
      (* forall x0 : name * name, In x0 (domain g2) <-> In x0 (domain g) *)
      split; intros.
      eapply in_domain_in_g in H3 as (f &t2 &K); specialize IFF with (x0, f, t2); eapply in_g_in_domain,IFF...
      eapply in_domain_in_g in H3 as (f &t2 &K); specialize IFF with (x0, f, t2); eapply in_g_in_domain,IFF...
      assert (NoDup (domain ((u, vis, t1) :: (x, vis, t) :: removeEntry u g))).
      eapply no_dup_cons_removeEntry_app_1...
      intros ABS; subst. eapply in_g_in_domain in H0; contradiction.
      assert (nd_pf' : NoDup (domain ((u, vis, t1) :: (x, vis, t) :: removeEntry u g2))).
      eapply no_dup_cons_removeEntry_app_1...
      intros ABS; subst. eapply in_g_in_domain in H0; contradiction.
      intros ABS. eapply in_domain_in_g in ABS as (f &t2 &K).
      eapply IFF, in_g_in_domain in K...
      eapply IHTC... 
      (* forall x0 : name * name * flag * piType, In x0 ((x, vis, t) :: g) <-> In x0 ((x, vis, t) :: g2)*)
      split; intros.
      inversion H4; subst...
      inversion H5; subst...
      repeat right... destruct x0,p0; eapply removeEntry_in,IFF...
      intros ABS; subst.
      assert (~In (u, f, p1) (removeEntry u g))...
      inversion H4; subst...
      inversion H5; subst...
      repeat right... destruct x0,p0; eapply removeEntry_in,IFF...
      intros ABS; subst.
      assert (~In (u, f, p1) (removeEntry u g2))...
    - intros.
      eapply TInUn.
      eauto. specialize IFF with (u, vis, Chan un p t); intuition...
      intro. apply in_domain_in_g in H3.
      destruct H3 as [ff [tt IN]];
        specialize IFF with (x, ff, tt).
      apply IFF in IN. apply in_g_in_domain in IN; intuition.

      erewrite max_same_domain with (l := domain g).
      eauto.
      (* forall x0 : name * name, In x0 (domain g2) <-> In x0 (domain g) *)
      split; intros.
      eapply in_domain_in_g in H3 as (f &t1 &K); specialize IFF with (x0, f, t1); eapply in_g_in_domain,IFF...
      eapply in_domain_in_g in H3 as (f &t1 &K); specialize IFF with (x0, f, t1); eapply in_g_in_domain,IFF...
      assert ( NoDup (domain ((x, vis, t) :: g))).
      apply NoDup_cons_iff...
      assert (nd_pf' : NoDup (domain ((x, vis, t) :: g2))).
      unfold domain; fold domain. apply NoDup_cons_iff...
      split. intro.
      apply in_domain_in_g in H4.
      destruct H4 as [ff [tt IN]];
        specialize IFF with (x, ff, tt).
      apply IFF in IN. apply in_g_in_domain in IN; intuition.
      eauto.
      eapply no_dup_isMap in nd_pf' as pf'.
      specialize IHTC with (pf2 := pf').
      apply IHTC in H3...
      (* forall x0 : name * name * flag * piType, In x0 ((x, vis, t) :: g) <-> In x0 ((x, vis, t) :: g2)*)
      split; intros.
      inversion H4; subst...
      right... eapply IFF...
      inversion H4; subst...
      right... eapply IFF...
    -  intros.
       eapply TInU.
       eauto. specialize IFF with (u, vis, Chan un p t); intuition...
       intro. apply in_domain_in_g in H4.
       destruct H4 as [ff [tt IN]];
         specialize IFF with (x, ff, tt).
       apply IFF in IN. apply in_g_in_domain in IN; intuition.
       erewrite max_same_domain. eauto.
       (*forall x0 : name * name, In x0 (domain g2) <-> In x0 (domain g)*)
       split; intros.
       eapply in_domain_in_g in H4 as (f &t1 &K).
       eapply in_g_in_domain,IFF...
       eapply in_domain_in_g in H4 as (f &t1 &K).
       eapply in_g_in_domain,IFF...
       (*  cons (vis_proj g2) ?pf2 *)
       eapply cons_distr. split.
       eapply cons_distr in H3 as (K1 &K2).
       eapply gcons_iff with (g1 := vis_proj g). eauto.
       
       
       eapply no_dup_vis_proj...
       eauto.
       intros...
       eapply cons_distr in H3 as (K1 &K2).
       eapply gcons_iff with (g1 := ill_proj g). eauto.
       eapply no_dup_ill_proj...
       eauto.
       intros...

       assert (ND: NoDup (domain ((x, vis, t) :: g))).
       apply NoDup_cons_iff...
       assert (nd_pf' : NoDup (domain ((x, vis, t) :: g2))).
       unfold domain; fold domain. apply NoDup_cons_iff...
       split. intro.
       apply in_domain_in_g in H4.
       destruct H4 as [ff [tt IN]];
         specialize IFF with (x, ff, tt).
       apply IFF in IN. apply in_g_in_domain in IN. intuition.
       eauto.
       apply no_dup_isMap in nd_pf' as pf'.
       specialize IHTC with (pf2 := pf').
       apply IHTC in ND...
       (* forall x0 : name * name * flag * piType, In x0 ((x, vis, t) :: g) <-> In x0 ((x, vis, t) :: g2)*)
       intros. split; intros.
       inversion H4; subst...
       right. eapply IFF...
       inversion H4; subst...
       right. eapply IFF...
       
       Unshelve. eauto. eauto. eauto.
       apply cons_removeEntry... eapply no_dup_isMap...
       eapply no_dup_isMap... 
       rewrite removeEntry_swap.
       apply cons_removeEntry_app...
       intuition. all:  try assumption.
       eapply no_dup_isMap, no_dup_cons_removeEntry...
       eapply no_dup_isMap,no_dup_cons_removeEntry_app_1...
       intros ABS; subst. eapply in_g_in_domain in H0; contradiction.
       intros ABS; subst.
       eapply in_domain_in_g in ABS as (ff &tt &ABS).
       eapply IFF,in_g_in_domain in ABS; contradiction.
       eapply no_dup_isMap. simpl.  eapply NoDup_cons_iff;split... intros ABS;subst. eapply in_domain_in_g in ABS as (ff &tt &ABS).
       eapply IFF,in_g_in_domain in ABS; contradiction.
       
       (*isMap (vis_proj g2 ++ ill_proj g2)*)
       assert (IFFVIS: forall x : name * name * flag * piType, In x (vis_proj g) <-> In x (vis_proj g2)).
       eapply vis_proj_iff...
       assert (IFFILL: forall x : name * name * flag * piType, In x (ill_proj g) <-> In x (ill_proj g2)).
       eapply ill_proj_iff...
       unfold isMap; intros. destruct H4 as (IN1 &IN2); eapply in_app_iff in IN1. eapply in_app_iff in IN2.
       inversion IN1; inversion IN2.

       eapply IFFVIS in H4.  eapply IFFVIS in H5.
       eapply in_isMap...
       
       eapply IFFVIS in H4.  eapply IFFILL in H5.
       assert (f1 = vis). eapply vis_proj_in...
       assert (f2 = ill). eapply ill_proj_in...
       subst. 
       assert (vis = ill). eapply flag_of_map with (x := x0) (g := vis_proj g ++ ill_proj g). eauto. 
       econstructor; eapply in_app_iff; left...
       econstructor; eapply in_app_iff; right...
       discriminate.

       eapply IFFVIS in H5.  eapply IFFILL in H4.
       eapply in_isMap...
       assert (f2 = vis). eapply vis_proj_in...
       assert (f1 = ill). eapply ill_proj_in...
       subst. 
       assert (vis = ill). eapply flag_of_map with (x := x0) (g := vis_proj g ++ ill_proj g). eauto. 
       econstructor; eapply in_app_iff; left...
       econstructor; eapply in_app_iff; right...
       discriminate.

       eapply IFFILL in H4.  eapply IFFILL in H5.
       eapply in_isMap...
       
       
       try assert ( K := pf2); eapply isMap_distr in K as (K1 &K2); eauto.
       eapply no_dup_isMap, no_dup_vis_proj;eauto.
       try assert ( K := pf2); eapply isMap_distr in K as (K1 &K2); eauto.
       try assert ( K := pf2); eapply isMap_distr in K as (K1 &K2); eauto.
       eapply no_dup_isMap, no_dup_ill_proj;eauto.
       try assert ( K := pf2); eapply isMap_distr in K as (K1 &K2); eauto.
       eapply no_dup_isMap; simpl; eapply NoDup_cons_iff; split...
       intros ABS. eapply in_domain_in_g in ABS as (ff &tt &ABS).
       eapply IFF,in_g_in_domain in ABS; contradiction.
  Qed.



  
 
   Lemma in_newEntries: forall b1 b2 f1 t g p (pf : isMap g),
      sl_pos p ->
      In (b1, b2, f1, t) g ->
      In (b1, b2) (secLabs p) ->
      In (b1, b2 + max (domain g), f1, t)
         (newEntries g (map (fun x : name * name => (fst x, snd x + max (domain g))) (secLabs p))
                     (max (domain g))).
  Proof with eauto.
    intros b1 b2 f1 t g p pf SLP.
    intros.
    induction p.
    unfold secLabs in H0. inversion H0.
    unfold secLabs in H0. fold secLabs in H0.
    intuition.
    unfold secLabs; fold secLabs.
    unfold secLabs in H0. fold secLabs in H0.
    apply sl_pos_par_l in SLP as SLP1.
    apply sl_pos_par_r in SLP as SLP2.
    apply in_app_iff in H0; intuition.
    rewrite map_app.
    rewrite newEntries_distr.
    intuition.
    rewrite map_app.
    rewrite newEntries_distr.
    intuition.
    unfold secLabs in H0. fold secLabs in H0.
    unfold secLabs; fold secLabs.
    apply in_app_iff in H0; intuition.
    rewrite map_app.
    rewrite newEntries_distr.
    apply sl_pos_nu in SLP as SLP1.
    intuition.
    clear IHp. inversion H1; inversion H0; subst.
    rewrite map_app.
    rewrite newEntries_distr. 
    apply in_app_iff. right.
    rewrite map_cons. simpl.
    case_eq (InB (b1, b2 + max (domain g)) g). intros.
    case_eq b. intros.
    subst b.
    apply inB_implies_In in H2 as K2.
    destruct K2 as [f2 [t2 ABS]].
    assert ( b2 + max (domain g) <= max (domain g)).
    apply in_preserves_max with (x := b1)...
    assert (b2 = 0). omega.
    unfold sl_pos in SLP; fold sl_pos in SLP.
    unfold pos in SLP; unfold secLabs in SLP; fold secLabs in SLP; fold pos in SLP.
    specialize SLP with b1 b2. assert (In (b1, b2) (secLabs p ++ (b1, b2) :: nil)). apply in_app_iff... intuition.

    intros. subst.
    assert (b2 + max (domain g) - max (domain g) = b2).
    omega. rewrite H3.
    apply in_implies_InB in H as K. rewrite K.
    intuition.
    assumption.
    unfold secLabs in H0. fold secLabs in H0.
    unfold secLabs; fold secLabs.
    apply sl_pos_inp in SLP. intuition.
    unfold secLabs in H0. fold secLabs in H0.
    unfold secLabs; fold secLabs.
    apply sl_pos_out in SLP. intuition.
  Qed.
