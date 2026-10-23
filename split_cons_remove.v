Require Import
  Bool List Lia PeanoNat Program.Equality
  ListAddOns Max RemoveEntry
  header
  operations pi_syntax 
  pairEq type_system semantics
  type_operations_1
  split_exists_neutral
  sub_split
  no_dup_split_no_dup
  split_existential
  split_operations_4
  disjoint_newEntries.

Require Import CpdtTactics LibTactics.

Lemma flag_plus_comm: forall f g h,
    flag_plus f g h <-> flag_plus g f h.
Proof with eauto.
  intros; intuition. 
  destruct f, g;  inversion H; subst; econstructor...
  destruct f, g;  inversion H; subst; econstructor...
Qed.

#[global] Hint Resolve flag_plus_comm.

Lemma split_comm : forall g1 g2 g pf1 pf2 pf,
    tEnv_split g1 g2 g pf1 pf2 pf <->
      tEnv_split g2 g1 g pf2 pf1 pf.
Proof with eauto.
  intros. intuition.
  dependent induction H. 
  subst.
  apply SpNil...
  apply SpLin with n g f' f q p p' t g''' pf'' pf' pf'''.
  all:eauto.
  apply flag_plus_comm...
  apply pol_plus_comm...
  apply SpUn with n g f' f p t g''' pf'' pf' pf'''.
  all:eauto.
  apply flag_plus_comm...
  apply SpTop with n g f' f g''' pf'' pf' pf'''...
  apply flag_plus_comm...

  dependent induction H. subst.
  apply SpNil...
  apply SpLin with n g f' f q p p' t g''' pf'' pf' pf'''.
  all:eauto.
  apply flag_plus_comm...
  apply pol_plus_comm...
  apply SpUn with n g f' f p t g''' pf'' pf' pf'''.
  all:eauto.
  apply flag_plus_comm...
  apply SpTop with n g f' f g''' pf'' pf' pf'''...
  apply flag_plus_comm...
Qed.


Lemma fimpl_removeEntry g2 g l1 l2
  a1 a2 b1 b2  fb ta tb ta1 tb1 (nd_pf2 : NoDup (domain g2)) (nd_pf : NoDup (domain g)):
  (a1, a2) <> (b1, b2) ->
  (forall (x : name * name) (f f2 : flag),
      flagOf g2 x f2 ->
      flagOf g x f ->
      f2 <> f ->
      f2 = hid /\ f = ill /\ ~ In x (l1 ++ l2)) ->
  forall (x : name * name) (f f2 : flag),
    flagOf
      ((a1, a2, vis, ta1)
         :: (b1, b2, fb, tb1) :: removeEntry (a1, a2) (removeEntry (b1, b2) g2)) x f2 ->
    flagOf
      ((a1, a2, vis, ta )
         :: (b1, b2, fb, tb) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)) x f ->
    f2 <> f ->
    f2 = hid /\ f = ill /\ ~ In x l1 /\ ~In x l2.
Proof with eauto.
  introv DIFF FIMPL; intros [x1 x2] f1 f2 FYP2 FYP1 DIFF2.
  simpl in FIMPL; specialize FIMPL with (x1, x2) f1 f2.
  inverts FYP1 as IN1;
    inverts FYP2 as IN2;
    try inv IN1 as [EQ1 | IN3]; try inv EQ1;
    try inv IN2 as [EQ2 | IN4]; try inv EQ2;
    try inv IN3 as [EQ3 | IN5]; try inv EQ3;
    try contradiction;
    try inv IN4 as [EQ4 | IN6]; try inv EQ4;
    try contradiction.
  - try eapply no_dup_removeEntry_no_dup with (a := (b1,b2)),no_dup_not_in_removeEntry
        with (a := (x1, x2))  (f := f2) (t := t0)
      in nd_pf2; try contradiction...
  - try eapply no_dup_removeEntry_no_dup with (a := (b1,b2)),no_dup_not_in_removeEntry
        with (a := (x1, x2))  (f := f1) (t := t)
      in nd_pf; try contradiction...
  - eapply in_removeEntry in IN6;
      try eapply no_dup_not_in_removeEntry with (a := (x1,x2)) (f := f2) (t := t0) in nd_pf2; try contradiction...
  - eapply in_removeEntry in IN5;
      try eapply no_dup_not_in_removeEntry with (a := (x1,x2)) (f := f1) (t := t) in nd_pf; try contradiction...
  - repeat eapply in_removeEntry in IN5;
      repeat eapply in_removeEntry in IN6;
      eapply F_Entry, FIMPL in IN6;
      intuition;
      try econstructor...
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



Lemma  split_iff2:
  forall (g1 g2 g : typeEnv) (h2 : list (name * name * flag * piType)) 
         (pf1 : isMap g1) (pf2 : isMap g2) (pf : isMap g) (pfh2 : isMap h2),
    NoDup (domain g2) ->
    NoDup (domain h2) ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    (forall x : name * name * flag * piType, In x g2 <-> In x h2) ->
    tEnv_split g1 h2 g pf1 pfh2 pf.
Proof with eauto using isMap_removeEntry, removeEntry_iff,no_dup_split_no_dup_r,no_dup_split_no_dup_l,no_dup_removeEntry_no_dup.
  introv nd_pf2 nd_pfh2 TS IFF.
  generalize dependent h2.
  dependent induction TS; subst.
  intros. assert (h2 = nil).
  destruct h2; try specialize IFF with p; intuition;
    assert (ABS: In p nil); try contradiction...
  subst; try eapply SpNil...
  - intros.
    assert (isMap (removeEntry n g1)).
    eapply isMap_removeEntry...
    assert (isMap (removeEntry n g3)).
    eapply isMap_removeEntry...
    assert (pfh' : isMap (removeEntry n h2)).
    eapply isMap_removeEntry...
    
    eapply SpLin with (f := f) (g :=g)(f' := f')
                      (p := p) (q:=q)(p':= p')
                      (t := t) (n :=n); try assumption.
    eapply IFF...
    specialize IHTS with (pfh2 := pfh').
    assert ((forall x : name * name * flag * piType, In x 
                                                       (removeEntry n h2)<-> In x (removeEntry n g2))).
    eapply removeEntry_iff...
    intuition; eapply IFF...
    eapply IHTS...
    tauto.
  - intros.
    assert (isMap (removeEntry n g1)).
    eapply isMap_removeEntry...
    assert (isMap (removeEntry n g3)).
    eapply isMap_removeEntry...
    assert (pfh' : isMap (removeEntry n h2)).
    eapply isMap_removeEntry...
    
    eapply SpUn with (f := f) (g :=g)(f' := f')
                     (p := p) 
                     (t := t) (n :=n); try assumption.
    eapply IFF...
    specialize IHTS with (pfh2 := pfh').
    assert ((forall x : name * name * flag * piType, In x 
                                                       (removeEntry n h2)<-> In x (removeEntry n g2))).
    eapply removeEntry_iff...
    intuition; eapply IFF...
    eapply IHTS...
    tauto.
  - intros.
    assert (isMap (removeEntry n g1)).
    eapply isMap_removeEntry...
    assert (isMap (removeEntry n g3)).
    eapply isMap_removeEntry...
    assert (pfh' : isMap (removeEntry n h2)).
    eapply isMap_removeEntry...
    
    eapply SpTop with (f := f) (g :=g)(f' := f')
                      (n :=n); try assumption.
    eapply IFF...
    specialize IHTS with (pfh2 := pfh').
    assert ((forall x : name * name * flag * piType, In x 
                                                       (removeEntry n h2)<-> In x (removeEntry n g2))).
    eapply removeEntry_iff...
    intuition; eapply IFF...
    eapply IHTS...
    tauto.
    Unshelve.
    all:eauto.
Qed.


Lemma split_plus_un :
  forall g1 g2 g3 pf1 pf2 pf3 
         b1 b2 t f1 p1 f2 p2 f3 p3,
    In (b1, b2, f1, Chan un p1 t) g1 ->
    In (b1, b2, f2, Chan un p2 t) g2 ->
    In (b1, b2, f3, Chan un p3 t) g3 ->
    tEnv_split g1 g2 g3 pf1 pf2 pf3 ->
    p1 = p2 /\ p2 = p3.
Proof with eauto.
  intros g1 g2 g3 pf1 pf2 pf3 
    b1 b2 t f1 p1 f2 p2 f3 p3
    T1 T2 T3 TS.
  dependent induction TS.
  + subst; inversion T1.
  + case_eq (pair_eq n (b1, b2)). intros PEQ.
    rewrite <-pairEq_eq in PEQ. subst.
    inversion H5; subst.
    assert (f1 = f /\  Chan un p1 t = Chan lin p t0).
    apply in_isMap with (x := (b1, b2)) (g := g1)...
    intuition. inversion H8. inversion H8.
    
    intros PNEQ. rewrite <-pairEq_neq in PNEQ.
    assert (In (b1, b2, f1, Chan un p1 t) (removeEntry n g1)).
    apply removeEntry_in...
    assert ( In (b1, b2, f2, Chan un p2 t) (removeEntry n g2) ).
    apply removeEntry_in...
    assert (In (b1, b2, f3, Chan un p3 t) g'''). rewrite <-H3.
    apply removeEntry_in...
    intuition.
  + case_eq (pair_eq n (b1, b2)). intros PEQ.
    rewrite <-pairEq_eq in PEQ. subst.
    inversion H4; subst. 
    assert (f1 = f /\  Chan un p1 t = Chan un p t0).
    apply in_isMap with (x := (b1, b2)) (g := g1)...
    assert (f2 = g /\  Chan un p2 t = Chan un p t0).
    apply in_isMap with (x := (b1, b2)) (g := g2)...
    assert (f3 = f0 /\  Chan un p3 t = Chan un p t0).
    apply in_isMap with (x := (b1, b2)) (g := g3)...
    intuition. 
    inversion H9. inversion H10. inversion H11. subst...
    inversion H9. inversion H10. inversion H11. subst...
    
    intros PNEQ. rewrite <-pairEq_neq in PNEQ.
    assert (In (b1, b2, f1, Chan un p1 t) (removeEntry n g1)).
    apply removeEntry_in...
    assert ( In (b1, b2, f2, Chan un p2 t) (removeEntry n g2) ).
    apply removeEntry_in...
    assert (In (b1, b2, f3, Chan un p3 t) g'''). rewrite <-H2.
    apply removeEntry_in...
    intuition.
  + case_eq (pair_eq n (b1, b2)). intros PEQ.
    rewrite <-pairEq_eq in PEQ. subst.
    assert (f1 = f /\  Chan un p1 t = Top).
    apply in_isMap with (x := (b1, b2)) (g := g1)...
    intuition. inversion H6. inversion H6.
    intros PNEQ. rewrite <-pairEq_neq in PNEQ.
    assert (In (b1, b2, f1, Chan un p1 t) (removeEntry n g1)).
    apply removeEntry_in...
    assert ( In (b1, b2, f2, Chan un p2 t) (removeEntry n g2) ).
    apply removeEntry_in...
    assert (In (b1, b2, f3, Chan un p3 t) g'''). rewrite <-H2.
    apply removeEntry_in...
    intuition.
Qed. 

Lemma split_plus_lin :
  forall g1 g2 g3 pf1 pf2 pf3 
         b1 b2 t f1 p1 f2 p2 f3 p3,
    In (b1, b2, f1, Chan lin p1 t) g1 ->
    In (b1, b2, f2, Chan lin p2 t) g2 ->
    In (b1, b2, f3, Chan lin p3 t) g3 ->
    tEnv_split g1 g2 g3 pf1 pf2 pf3 ->
    pol_plus p1 p2 p3.
Proof with eauto.
  intros g1 g2 g3 pf1 pf2 pf3 
    b1 b2 t f1 p1 f2 p2 f3 p3
    T1 T2 T3 TS.
  dependent induction TS.
  + subst; inversion T1.
  + case_eq (pair_eq n (b1, b2)). intros PEQ.
    rewrite <-pairEq_eq in PEQ. subst.
    inversion H5; subst.
    assert (f1 = f /\  Chan lin p1 t = Chan lin p t0).
    apply in_isMap with (x := (b1, b2)) (g := g1)...
    assert (f2 = g /\  Chan lin p2 t = Chan lin q t0).
    apply in_isMap with (x := (b1, b2)) (g := g2)...
    assert (f3 = f0 /\  Chan lin p3 t = Chan lin p' t0).
    apply in_isMap with (x := (b1, b2)) (g := g3)...
    intuition; inversion H10; inversion H11; inversion H12.
    subst p q p' t0.
    eauto.
    intros PNEQ. rewrite <-pairEq_neq in PNEQ.
    assert (In (b1, b2, f1, Chan lin p1 t) (removeEntry n g1)).
    apply removeEntry_in...
    assert ( In (b1, b2, f2, Chan lin p2 t) (removeEntry n g2) ).
    apply removeEntry_in...
    assert (In (b1, b2, f3, Chan lin p3 t) g'''). rewrite <-H3.
    apply removeEntry_in...
    intuition.

  + case_eq (pair_eq n (b1, b2)). intros PEQ.
    rewrite <-pairEq_eq in PEQ. subst.
    inversion H4; subst.
    assert (f1 = f /\  Chan lin p1 t = Chan un p t0).
    apply in_isMap with (x := (b1, b2)) (g := g1)...
    intuition. inversion H7.
    
    intros PNEQ. rewrite <-pairEq_neq in PNEQ.
    assert (In (b1, b2, f1, Chan lin p1 t) (removeEntry n g1)).
    apply removeEntry_in...
    assert ( In (b1, b2, f2, Chan lin p2 t) (removeEntry n g2) ).
    apply removeEntry_in...
    assert (In (b1, b2, f3, Chan lin p3 t) g'''). rewrite <-H2.
    apply removeEntry_in...
    intuition.

  + case_eq (pair_eq n (b1, b2)). intros PEQ.
    rewrite <-pairEq_eq in PEQ. subst.
    assert (f1 = f /\  Chan lin p1 t = Top).
    apply in_isMap with (x := (b1, b2)) (g := g1)...
    intuition. inversion H6.

    intros PNEQ. rewrite <-pairEq_neq in PNEQ.
    assert (In (b1, b2, f1, Chan lin p1 t) (removeEntry n g1)).
    apply removeEntry_in...
    assert ( In (b1, b2, f2, Chan lin p2 t) (removeEntry n g2) ).
    apply removeEntry_in...
    assert (In (b1, b2, f3, Chan lin p3 t) g'''). rewrite <-H2.
    apply removeEntry_in...
    intuition.
Qed.


Lemma split_pf :
  forall g1 g2 g3 pf1 pf2 pf3
         pf1' pf2' pf3',
    tEnv_split g1 g2 g3 pf1 pf2 pf3  ->
    tEnv_split g1 g2 g3 pf1' pf2' pf3'.
Proof with eauto.
  intros g1 g2 g3 pf1 pf2 pf3 pf1' pf2' pf3' TS.
  dependent induction TS. 
  subst. apply SpNil...
  apply SpLin
    with  n f f' g p q p' t g''' pf' pf'' pf'''.
  all:eauto.
  apply SpUn
    with  n f f' g p t g''' pf' pf'' pf'''.
  all:eauto.
  apply SpTop with n f f' g g''' pf' pf'' pf'''.
  all:eauto.
Qed.



Lemma split_remove :
  forall g1 g2 g3 pf1 pf2 pf3 
         (nd_pf1 : NoDup (domain g1))
         (nd_pf2 : NoDup (domain g2))
         (nd_pf3 : NoDup (domain g3))
         b pf1' pf2' pf3',
    tEnv_split g1 g2 g3 pf1 pf2 pf3  ->
    tEnv_split
      (removeEntry b g1)
      (removeEntry b g2)
      (removeEntry b g3) pf1' pf2' pf3'.
Proof with eauto.
  intros g1 g2 g3 pf1 pf2 pf3
    nd_pf1 nd_pf2 nd_pf3
    b pf1' pf2' pf3'
    TS.
  dependent induction TS.
  + subst. unfold removeEntry. apply SpNil...
  + case_eq (pair_eq b n); intros PEQ.
    rewrite <-pairEq_eq in PEQ. subst.
    apply split_pf with (pf1 := pf') (pf2 := pf'') (pf3 := pf''')...
    rewrite <-pairEq_neq in PEQ.
    apply no_dup_removeEntry_no_dup with (a := n) in nd_pf1 as nd_pf1'.
    apply no_dup_removeEntry_no_dup with (a := n) in nd_pf2 as nd_pf2'.
    apply no_dup_removeEntry_no_dup with (a := n) in nd_pf3 as nd_pf3'.
    subst g'''; intuition.
    apply no_dup_removeEntry_no_dup with (a := b) in nd_pf1' as nd_pf1''.
    apply no_dup_removeEntry_no_dup with (a := b) in nd_pf2' as nd_pf2''.
    apply no_dup_removeEntry_no_dup with (a := b) in nd_pf3' as nd_pf3''.
    apply no_dup_isMap in nd_pf1'' as pf1b.
    apply no_dup_isMap in nd_pf2'' as pf2b.
    apply no_dup_isMap in nd_pf3'' as pf3b.
    specialize H3 with pf1b pf2b pf3b.
    assert ((removeEntry b (removeEntry n g1)) =
              (removeEntry n (removeEntry b g1))).
    apply removeEntry_swap...
    assert ((removeEntry b (removeEntry n g2)) =
              (removeEntry n (removeEntry b g2))).
    apply removeEntry_swap...
    assert ((removeEntry b (removeEntry n g3)) =
              (removeEntry n (removeEntry b g3))).
    apply removeEntry_swap...
    revert dependent pf1b.
    revert dependent pf2b.
    revert dependent pf3b.
    rewrite H6. rewrite H7. rewrite H8.
    intros.
    
    apply SpLin with n f f' g p q p' t (removeEntry n (removeEntry b g3)) pf1b pf2b pf3b.
    eauto. eauto. 
    apply removeEntry_in...
    apply removeEntry_in...
    eauto. 
    tauto.
    eauto. 
    inversion H4; subst.
    apply removeEntry_in with (y := b) in H9...
    inversion H5; subst.
    apply removeEntry_in with (y := b) in H9...
  + case_eq (pair_eq b n); intros PEQ.
    rewrite <-pairEq_eq in PEQ. subst.
    apply split_pf with (pf1 := pf') (pf2 := pf'') (pf3 := pf''')...
    rewrite <-pairEq_neq in PEQ.
    apply no_dup_removeEntry_no_dup with (a := n) in nd_pf1 as nd_pf1'.
    apply no_dup_removeEntry_no_dup with (a := n) in nd_pf2 as nd_pf2'.
    apply no_dup_removeEntry_no_dup with (a := n) in nd_pf3 as nd_pf3'.
    subst g'''; intuition.
    apply no_dup_removeEntry_no_dup with (a := b) in nd_pf1' as nd_pf1''.
    apply no_dup_removeEntry_no_dup with (a := b) in nd_pf2' as nd_pf2''.
    apply no_dup_removeEntry_no_dup with (a := b) in nd_pf3' as nd_pf3''.
    apply no_dup_isMap in nd_pf1'' as pf1b.
    apply no_dup_isMap in nd_pf2'' as pf2b.
    apply no_dup_isMap in nd_pf3'' as pf3b.
    specialize H2 with pf1b pf2b pf3b.
    assert ((removeEntry b (removeEntry n g1)) =
              (removeEntry n (removeEntry b g1))).
    apply removeEntry_swap...
    assert ((removeEntry b (removeEntry n g2)) =
              (removeEntry n (removeEntry b g2))).
    apply removeEntry_swap...
    assert ((removeEntry b (removeEntry n g3)) =
              (removeEntry n (removeEntry b g3))).
    apply removeEntry_swap...
    revert dependent pf1b.
    revert dependent pf2b.
    revert dependent pf3b.
    rewrite H5. rewrite H6. rewrite H7.
    intros.
    
    apply SpUn with n f f' g p t (removeEntry n (removeEntry b g3)) pf1b pf2b pf3b.
    eauto. 
    apply removeEntry_in...
    apply removeEntry_in...
    eauto. 
    tauto. 
    inversion H3; subst.
    apply removeEntry_in with (y := b) in H8...
    inversion H4; subst.
    apply removeEntry_in with (y := b) in H8...
  + case_eq (pair_eq b n); intros PEQ.
    rewrite <-pairEq_eq in PEQ. subst.
    apply split_pf with (pf1 := pf') (pf2 := pf'') (pf3 := pf''')...
    rewrite <-pairEq_neq in PEQ.
    apply no_dup_removeEntry_no_dup with (a := n) in nd_pf1 as nd_pf1'.
    apply no_dup_removeEntry_no_dup with (a := n) in nd_pf2 as nd_pf2'.
    apply no_dup_removeEntry_no_dup with (a := n) in nd_pf3 as nd_pf3'.
    subst g'''; intuition.
    apply no_dup_removeEntry_no_dup with (a := b) in nd_pf1' as nd_pf1''.
    apply no_dup_removeEntry_no_dup with (a := b) in nd_pf2' as nd_pf2''.
    apply no_dup_removeEntry_no_dup with (a := b) in nd_pf3' as nd_pf3''.
    apply no_dup_isMap in nd_pf1'' as pf1b.
    apply no_dup_isMap in nd_pf2'' as pf2b.
    apply no_dup_isMap in nd_pf3'' as pf3b.
    specialize H2 with pf1b pf2b pf3b.
    assert ((removeEntry b (removeEntry n g1)) =
              (removeEntry n (removeEntry b g1))).
    apply removeEntry_swap...
    assert ((removeEntry b (removeEntry n g2)) =
              (removeEntry n (removeEntry b g2))).
    apply removeEntry_swap...
    assert ((removeEntry b (removeEntry n g3)) =
              (removeEntry n (removeEntry b g3))).
    apply removeEntry_swap...
    revert dependent pf1b.
    revert dependent pf2b.
    revert dependent pf3b.
    rewrite H5. rewrite H6. rewrite H7.
    intros.
    
    apply SpTop with n f f' g (removeEntry n (removeEntry b g3)) pf1b pf2b pf3b.
    eauto. 
    apply removeEntry_in...
    apply removeEntry_in...
    eauto. 
    tauto. 
    inversion H3; subst.
    apply removeEntry_in with (y := b) in H8...
    inversion H4; subst.
    apply removeEntry_in with (y := b) in H8...
Qed.

Lemma split_cons_remove :
  forall g1 g2 g3 pf1 pf2 pf3 
         (nd_pf1 : NoDup (domain g1))
         (nd_pf2 : NoDup (domain g2))
         (nd_pf3 : NoDup (domain g3))
         b1 b2 f1 t1 f2 t2 f3 t3 pf1' pf2' pf3',
    In (b1, b2, f1, t1) g1 ->
    In (b1, b2, f2, t2) g2 ->
    In (b1, b2, f3, t3) g3 ->
    tEnv_split g1 g2 g3 pf1 pf2 pf3  ->
    tEnv_split
      ((b1, b2, vis, t1) :: removeEntry (b1, b2) g1)
      ((b1, b2, vis, t2) :: removeEntry (b1, b2) g2)
      ((b1, b2, vis, t3) :: removeEntry (b1, b2) g3)
      pf1' pf2' pf3'.
Proof with eauto.
  intros g1 g2 g3 pf1 pf2 pf3
    nd_pf1 nd_pf2 nd_pf3
    b1 b2 f1 t1 f2 t2 f3 t3 pf1' pf2' pf3'
    T1 T2 T3 TS.
  destruct t1. remember t1 as t; subst t1.
  apply tsub_payload with
    g1 g2 g3 pf1 pf2 pf3 b1 b2 f1 m p t
    in T1 as TYP0.
  destruct TYP0 as [p3 TYP3].
  inversion TYP3; subst.
  assert (f3 = f /\ t3 = Chan m p3 t).
  apply in_isMap with (x := (b1, b2)) (g := g3)...
  intuition; subst f. 
  apply tsuper_payload_r with
    g1 g2 g3 pf1 pf2 pf3 b1 b2 f3 m p3 t
    in H as TYP2.
  destruct TYP2 as [p2 TYP2].
  inversion TYP2; subst.
  assert (f2 = f /\ t2 = Chan m p2 t).
  apply in_isMap with (x := (b1, b2)) (g := g2)...
  intuition; subst f t2.
  destruct m. all:eauto. 

  + assert (pol_plus p p2 p3).
    apply split_plus_lin with
      g1 g2 g3 pf1 pf2 pf3 
      b1 b2 t f1 f2 f3...
    assert (pf' : isMap (removeEntry (b1, b2) ((b1, b2, vis, Chan lin p t) :: removeEntry (b1, b2) g1))).
    unfold removeEntry at 1.
    assert (PEQ: pair_eq (b1, b2) (b1, b2)=true).
    apply pairEq_eq_true...
    rewrite PEQ...
    assert (pf'' : isMap (removeEntry (b1, b2) ((b1, b2, vis, Chan lin p2 t) :: removeEntry (b1, b2) g2))). 
    unfold removeEntry at 1.
    assert (PEQ: pair_eq (b1, b2) (b1, b2)=true).
    apply pairEq_eq_true...
    rewrite PEQ...
    assert (pf''' : isMap (removeEntry (b1, b2) ((b1, b2, vis, Chan lin p3 t) :: removeEntry (b1, b2) g3))). 
    unfold removeEntry at 1.
    assert (PEQ: pair_eq (b1, b2) (b1, b2)=true).
    apply pairEq_eq_true...
    rewrite PEQ...
    
    apply SpLin with
      (n := (b1, b2))
      (f := vis) (g := vis) (f' := vis)
      (p := p) (t := t) (pf' := pf') (pf'' := pf'')
      (pf''' := pf''') (q := p2) (p' := p3).
    apply Fp_vv.
    all:eauto.
    
    revert dependent pf'. revert dependent pf''. revert dependent pf'''.
    unfold removeEntry .
    assert (PEQ: pair_eq (b1, b2) (b1, b2)=true).
    apply pairEq_eq_true...
    rewrite PEQ...
    fold removeEntry.
    intros.

    apply split_remove 
      with (b := (b1, b2))  (pf1' := pf')
           (pf2' := pf'') (pf3' := pf''')
      in TS as TS1...

  +  assert (p = p2 /\ p2 = p3).
     apply split_plus_un with
       g1 g2 g3 pf1 pf2 pf3 
       b1 b2 t f1 f2 f3...
     assert (pf' : isMap (removeEntry (b1, b2) ((b1, b2, vis, Chan un p t) :: removeEntry (b1, b2) g1))).
     unfold removeEntry at 1.
     assert (PEQ: pair_eq (b1, b2) (b1, b2)=true).
     apply pairEq_eq_true...
     rewrite PEQ...
     assert (pf'' : isMap (removeEntry (b1, b2) ((b1, b2, vis, Chan un p2 t) :: removeEntry (b1, b2) g2))). 
     unfold removeEntry at 1.
     assert (PEQ: pair_eq (b1, b2) (b1, b2)=true).
     apply pairEq_eq_true...
     rewrite PEQ...
     assert (pf''' : isMap (removeEntry (b1, b2) ((b1, b2, vis, Chan un p3 t) :: removeEntry (b1, b2) g3))). 
     unfold removeEntry at 1.
     assert (PEQ: pair_eq (b1, b2) (b1, b2)=true).
     apply pairEq_eq_true...
     rewrite PEQ...
     destruct H1 as [K1 k2]; inversion K1. inversion H1; subst p2 p3. 
     clear H1 H2. 
     apply SpUn with
       (n := (b1, b2))
       (f := vis) (g := vis) (f' := vis)
       (p := p) (t := t) (pf' := pf') (pf'' := pf'')
       (pf''' := pf''') .
     apply Fp_vv.
     all:eauto.
     
     revert dependent pf'. revert dependent pf''. revert dependent pf'''.
     unfold removeEntry .
     assert (PEQ: pair_eq (b1, b2) (b1, b2)=true).
     apply pairEq_eq_true...
     rewrite PEQ...
     fold removeEntry.
     intros.

     apply split_remove 
       with (b := (b1, b2))  (pf1' := pf')
            (pf2' := pf'') (pf3' := pf''')
       in TS as TS1...

  +  assert (pf' : isMap (removeEntry (b1, b2) ((b1, b2, vis, Top) :: removeEntry (b1, b2) g1))).
     unfold removeEntry at 1.
     assert (PEQ: pair_eq (b1, b2) (b1, b2)=true).
     apply pairEq_eq_true...
     rewrite PEQ...
     assert (pf'' : isMap (removeEntry (b1, b2) ((b1, b2, vis, Top) :: removeEntry (b1, b2) g2))). 
     unfold removeEntry at 1.
     assert (PEQ: pair_eq (b1, b2) (b1, b2)=true).
     apply pairEq_eq_true...
     rewrite PEQ...
     assert (pf''' : isMap (removeEntry (b1, b2) ((b1, b2, vis, Top) :: removeEntry (b1, b2) g3))). 
     unfold removeEntry at 1.
     assert (PEQ: pair_eq (b1, b2) (b1, b2)=true).
     apply pairEq_eq_true...
     rewrite PEQ...

     apply tsub_top
       with  g1 g2 g3 pf1 pf2 pf3 b1 b2 f1 in T1 as K1.
     inversion K1.  subst.
     assert (f = f3 /\ Top = t3).
     apply in_isMap with (x := (b1, b2)) (g := g3)...
     destruct H0 as [W0 W1]; inversion W0; inversion W1; subst.
     apply tsuper_top_r with
       g1 g2 g3 pf1 pf2 pf3 b1 b2 f3 in H.
     inversion H. subst.
     assert (f = f2 /\ Top = t2).
     apply in_isMap with (x := (b1, b2)) (g := g2)...
     destruct H3 as [W0 W1]; inversion W0; inversion W1; subst.
     
     apply SpTop with
       (n := (b1, b2))
       (f := vis) (g := vis) (f' := vis)
       (pf' := pf') (pf'' := pf'')
       (pf''' := pf''') .
     apply Fp_vv.
     all:eauto.


     revert dependent pf'. revert dependent pf''. revert dependent pf'''.
     unfold removeEntry .
     assert (PEQ: pair_eq (b1, b2) (b1, b2)=true).
     apply pairEq_eq_true...
     rewrite PEQ...
     fold removeEntry.
     intros.

     apply split_remove 
       with (b := (b1, b2))  (pf1' := pf')
            (pf2' := pf'') (pf3' := pf''')
       in TS as TS1...
Qed.
