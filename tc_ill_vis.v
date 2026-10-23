Require Import
  Bool List Lia PeanoNat Program.Equality
  ListAddOns Max Domain RemoveEntry NewEntries Replication
  header
  operations pi_syntax 
  pairEq type_system type_system_rules
  no_dup_split_no_dup
  type_operations_1
  tc_prelim
  split_operations_2
  split_cons_remove
  tc_premises2
  tc_premises_4
  type_checking_0
  sub_split
  split_existential
  lts_no_dup
  disjoint_newEntries
  substitution_prelim
  sne_premises
  split_not_exists.

Require Import CpdtTactics LibTactics.

Notation cons_removeEntry := gcons_removeEntry.

Lemma cons_cons a1 a2 g f1 f2 t pf pf1 (nd_pf : NoDup (domain g)):
  cons g pf->
  In (a1, a2, f1, t) g ->
  cons ((a1, a2, f2, t) ::  removeEntry (a1, a2) g) pf1.
Proof with eauto using cons_removeEntry.
  intros CONS IN.
  assert (EQ: removeEntry (a1, a2) ((a1, a2, f2, t) ::  removeEntry (a1, a2) g) =
                removeEntry (a1, a2) g).
  simpl;  try rewrite pairEq_eq_true...
  assert (pf2 : isMap (removeEntry (a1, a2) g)).
  eapply no_dup_isMap, no_dup_removeEntry_no_dup...
  destruct t; try destruct m.
  - rewrite <-EQ in *;
      eapply Co_lin with (n:= (a1, a2))(pf' := pf2).
    assert (p = empty). eapply cons_lin...
    subst...
    revert dependent pf2;
      simpl; try rewrite pairEq_eq_true; intros...
  - rewrite <-EQ in *;
      eapply Co_un with (n:= (a1, a2))(pf' := pf2).
    econstructor...
    revert dependent pf2;
      simpl; try rewrite pairEq_eq_true; intros...
  - rewrite <-EQ in *;
      eapply Co_top with (n:= (a1, a2))(pf' := pf2).
    econstructor...
    revert dependent pf2;
      simpl; try rewrite pairEq_eq_true; intros...
Qed.

Lemma cons_cons2 a1 a2 g g2 f1 f2 t pf pf1 pf2 (nd_pf : NoDup (domain g)):
  cons g pf->
  cons g2 pf2->
  In (a1, a2, f1, t) g2 ->
  cons ((a1, a2, f2, t) ::  removeEntry (a1, a2) g) pf1.
Proof with eauto using cons_removeEntry.
  intros CONS CONS2 IN.
  assert (EQ: removeEntry (a1, a2) ((a1, a2, f2, t) ::  removeEntry (a1, a2) g) =
                removeEntry (a1, a2) g).
  simpl;  try rewrite pairEq_eq_true...
  assert (pf3 : isMap (removeEntry (a1, a2) g)).
  eapply no_dup_isMap, no_dup_removeEntry_no_dup...
  destruct t; try destruct m.
  - rewrite <-EQ in *;
      eapply Co_lin with (n:= (a1, a2))(pf' := pf3).
    assert (p = empty). eapply cons_lin...
    subst...
    revert dependent pf3;
      simpl; try rewrite pairEq_eq_true; intros...
  - rewrite <-EQ in *;
      eapply Co_un with (n:= (a1, a2))(pf' := pf3).
    subst...
    revert dependent pf3;
      simpl; try rewrite pairEq_eq_true; intros...
  - rewrite <-EQ in *;
      eapply Co_top with (n:= (a1, a2))(pf' := pf3).
    subst...
    revert dependent pf3;
      simpl; try rewrite pairEq_eq_true; intros...
Qed.

Notation cons_distr := tc_prelim.cons_distr.


Notation no_dup_vis_proj := tc_prelim.no_dup_vis_proj.

Notation no_dup_ill_proj := tc_prelim.no_dup_ill_proj.



#[global] Hint Resolve cons_cons no_dup_cons_removeEntry
  no_dup_split_no_dup_r no_dup_split_no_dup_l.


Lemma typeCheck_ill_vis : forall g pf p b1 b2 t pf1 (nd_pf : NoDup (domain g)),
    typeCheck g pf p ->
    In (b1, b2, ill, t) g ->
    typeCheck
      ((b1, b2, vis, t) :: removeEntry (b1, b2) g) pf1 p.
Proof with eauto.
  intros g pf p b1 b2 t pf1 nd_pf TC IN.
  revert dependent b1. revert dependent b2.
  revert dependent t.
  dependent induction TC.
  - intros. econstructor; eapply cons_cons...
  - intros.
    assert (DIFF: n <> (b1, b2)).
    intros ABS. subst.
    assert (ill = hid). eapply flag_of_map with (g := g)...
    discriminate. 
    assert (nd_pf' : NoDup(domain(((n, vis, t) :: removeEntry n ((b1, b2, vis, t0) :: removeEntry (b1, b2) g))))).
    eapply no_dup_cons_removeEntry, no_dup_cons_removeEntry...
    eapply no_dup_isMap in nd_pf' as pf'.
    econstructor. right. eapply removeEntry_in.
    eauto. eauto.
    instantiate (1 := pf').
    assert (nd_pf'' : NoDup(domain( ((b1, b2, vis, t0) :: removeEntry (b1, b2) ((n, vis, t) :: removeEntry n g))))).
    eapply no_dup_cons_removeEntry, no_dup_cons_removeEntry...
    eapply no_dup_isMap in nd_pf'' as pf''.
    eapply typeCheck_impl with (pf1 := pf'').
    eauto. eauto.
    eapply IHTC.
    eapply no_dup_cons_removeEntry...
    right. eapply removeEntry_in...
    destruct n.

    erewrite <-removeEntry_shift,<-removeEntry_shift,removeEntry_swap.
    eapply cons_cons_iff...
    all:eauto.
  - intros.
    eapply super_in_sub with (pf1 := pf1) (pf2 := pf2) in IN as EX.
    destruct EX as [f1 [t1 [f2 [t2 [IN1 IN2]]]]].
    assert (nd_pf': NoDup (domain (((b1, b2, vis, t1) :: removeEntry (b1, b2) g1)))).
    eapply no_dup_cons_removeEntry, no_dup_split_no_dup_l...
    assert (nd_pf'': NoDup (domain (((b1, b2, vis, t2) :: removeEntry (b1, b2) g2)))).
    eapply no_dup_cons_removeEntry; try eapply no_dup_split_no_dup_r in H...
    eapply no_dup_isMap in nd_pf'' as pf''.
    eapply no_dup_isMap in nd_pf' as pf'.
    eapply TPar with (pf1 := pf') (pf2 := pf'').
    eapply tEnv_split_add_vis.
    eauto.
    (*type_plus t1 t2 t*)
    assert (EX:  exists t2 : piType, typeOf g2 (b1, b2)  t2 /\ type_plus t1 t2 t). 
    eapply split_type_plus...
    destruct EX as [t'' [T2 TP]].
    assert (t2 = t'').
    eapply type_of_map with (g := g2)...
    subst...
    (*is_unrestricted t -> t1 = t2 /\ t2 = t*)
    intros ISUN.
    assert (typeOf g2 (b1, b2) t1 /\ typeOf g (b1, b2) t1).
    eapply split_plus_un_isrestricted with (pf1 := pf1) (pf2 := pf2) (pf := pf)...
    unfold is_unrestricted in ISUN; destruct ISUN as [pp [tt ISUN]]. subst. eapply tsuper_payload with (pf1 := pf1) in IN.
    destruct IN as [pp1 TYP1].
    assert (t1 = Chan un pp1 tt).
    eapply type_of_map with (g := g1)...
    subst; eapply un_is_unrestricted...
    eauto.
    assert (t2 = t1).
    intuition;eapply type_of_map with (g := g2)...
    assert (t1 = t).
    intuition;eapply type_of_map with (g := g)...
    intuition; subst...
    eauto.
    (* typeCheck ((b1, b2, vis, t1) :: removeEntry (b1, b2) g1) pf' p1*)
    eapply  IHTC1.
    eapply no_dup_split_no_dup_l with (pf := pf)...
    assert (ill = f1).
    eapply split_eq_flag...
    discriminate.
    subst...
    eapply  IHTC2.
    eapply no_dup_split_no_dup_r with (pf := pf)...
    assert (ill = f2).
    eapply split_eq_flag with (pf1 := pf2).
    eapply split_comm...
    discriminate.
    all:subst; eauto.
  - Case TOutL.
    assert (TOUT:  typeCheck
                     g pf (dOut (fst u) (snd u) (fst v) (snd v) q))...
    intros.
    assert (u <> (b1, b2)).
    intros ABS. subst.
    assert (vis = ill).
    eapply flag_of_map with (x := (b1, b2)) (g := g)...
    discriminate.
    assert (v <> (b1, b2)).
    intros ABS. subst.
    assert (vis = ill).
    eapply flag_of_map with (x := (b1, b2)) (g := g)...
    discriminate.
    assert (u <> v).
    destruct u, v; eapply typeCheck_object_neq_subject in TOUT; unfold nonRec_typable in *; fold nonRec_typable in *; intuition.
    assert (nd_pf' :
             NoDup(domain(
                       ((u, vis, t1)
                          :: (v, vis, t2)
                          :: removeEntry v (removeEntry u ((b1, b2, vis, t0) :: removeEntry (b1, b2) g)))))).
    rewrite removeEntry_swap.
    destruct u, v; eapply no_dup_cons_removeEntry_app...
    intuition.
    eapply no_dup_isMap in nd_pf' as pf'.
    (*typeCheck ((b1, b2, vis, t0) :: removeEntry (b1, b2) g) pf0
    (dOut (fst u) (snd u) (fst v) (snd v) q)*)
    eapply TOutL with (pf1 := pf'). eauto. eauto.
    right; eapply removeEntry_in...
    right; eapply removeEntry_in...
    revert dependent pf'.
    destruct u, v. erewrite <-removeEntry_shift, <-removeEntry_shift. intros.
    eapply typeCheck_impl with (g1 := ((b1, b2, vis, t0)
                                         :: removeEntry (b1, b2)
                                         ((n, n0, vis, t1)
                                            :: (n1, n2, vis, t2) :: removeEntry (n1, n2) (removeEntry (n, n0) g)))).          
    eapply no_dup_cons_removeEntry.
    erewrite removeEntry_swap.
    eapply no_dup_cons_removeEntry_app...
    intuition.
    erewrite removeEntry_shift.
    assert (EQ: ((b1, b2, vis, t0) :: removeEntry (n, n0) (removeEntry (b1, b2) g)) =
                  removeEntry (n, n0)     ((b1, b2, vis, t0) :: removeEntry (b1, b2) g)).
    eapply removeEntry_shift...
    rewrite EQ.
    erewrite removeEntry_swap.
    eapply no_dup_cons_removeEntry_app...
    eauto. eauto.
    eapply IHTC.
    erewrite removeEntry_swap.
    eapply no_dup_cons_removeEntry_app...
    eauto.
    right. right. eapply removeEntry_in, removeEntry_in.
    eauto. eauto. eauto.
    assert (EQ: ((b1, b2, vis, t0)
                   :: removeEntry (b1, b2)
                   ((n, n0, vis, t1) :: (n1, n2, vis, t2) :: removeEntry (n1, n2) (removeEntry (n, n0) g))) =
                  ((b1, b2, vis, t0)
                     :: 
                     ((n, n0, vis, t1) :: (n1, n2, vis, t2) :: (removeEntry (n1, n2) (removeEntry (n, n0) (removeEntry (b1, b2) g)))))).
    rewrite <-removeEntry_shift,<-removeEntry_shift,removeEntry_swap, removeEntry_swap with (b:=(n, n0))...
    rewrite EQ.
    eapply cons_cons_cons_iff.
    all:eauto.
    Unshelve. eauto. eauto. eauto.
    eapply no_dup_isMap, no_dup_cons_removeEntry.
    rewrite removeEntry_swap.
    eapply no_dup_cons_removeEntry_app...
    eauto.
  - Case TOutUn.
    assert (TOUT:  typeCheck
                     g pf (dOut (fst u) (snd u) (fst v) (snd v) q))...
    intros.
    assert (u <> (b1, b2)).
    intros ABS. subst.
    assert (vis = ill).
    eapply flag_of_map with (x := (b1, b2)) (g := g)...
    discriminate.
    assert (v <> (b1, b2)).
    intros ABS. subst.
    assert (vis = ill).
    eapply flag_of_map with (x := (b1, b2)) (g := g)...
    discriminate.
    assert (u <> v).
    destruct u, v; eapply typeCheck_object_neq_subject in TOUT; unfold nonRec_typable in *; fold nonRec_typable in *; intuition.
    assert (nd_pf' :
             NoDup(domain((v, vis, t2)
                            :: removeEntry v ((b1, b2, vis, t0) :: removeEntry (b1, b2) g)))).
    eapply no_dup_cons_removeEntry, no_dup_cons_removeEntry...
    eapply no_dup_isMap in nd_pf' as pf'.
    (*typeCheck ((b1, b2, vis, t0) :: removeEntry (b1, b2) g) pf0
    (dOut (fst u) (snd u) (fst v) (snd v) q)*)
    eapply TOutUn with (pf1 := pf'). eauto. eauto.
    right; eapply removeEntry_in...
    right; eapply removeEntry_in...
    revert dependent pf'.
    destruct u, v. erewrite <-removeEntry_shift with (b1 := b1) (b2:= b2). intros.
    eapply typeCheck_impl with (g1 := ((b1, b2, vis, t0)
                                         :: removeEntry (b1, b2)( (n1, n2, vis, t2) :: removeEntry (n1, n2)  g))).          
    eapply no_dup_cons_removeEntry,no_dup_cons_removeEntry...
    eapply no_dup_cons_removeEntry_app...
    eapply IHTC.
    eapply no_dup_cons_removeEntry...
    right. eapply removeEntry_in...
    rewrite <-removeEntry_shift with (b1 := n1), removeEntry_swap.
    eapply cons_cons_iff.
    all:eauto.
    Unshelve. eauto. eauto. eauto.
    eapply no_dup_isMap, no_dup_cons_removeEntry,no_dup_cons_removeEntry...
  -  Case TInL.
     assert (TIN:  typeCheck g pf (dInp (fst u) (snd u) (fst x) (snd x) q))...
     intros.
     assert (u <> (b1, b2)).
     intros ABS. subst.
     assert (vis = ill).
     eapply flag_of_map with (x := (b1, b2)) (g := g)...
     discriminate.
     assert (x <> (b1, b2)).
     intros ABS. subst.
     apply in_g_in_domain in IN; intuition.
     assert (x <> u).
     intros ABS. subst.
     apply in_g_in_domain in H0; intuition.
     assert (nd_pf' :
              NoDup(domain(
                        ((u, vis, t1) :: (x, vis, t) :: removeEntry u ((b1, b2, vis, t0) :: removeEntry (b1, b2) g) )))).
     destruct u, x as [x1 x2].
     rewrite removeEntry_shift with (b1 := x1).
     eapply no_dup_cons_removeEntry.
     assert (EQ: domain ((x1, x2, vis, t) :: (b1, b2, vis, t0) :: removeEntry (b1, b2) g) =
                   (x1, x2) :: domain ((b1, b2, vis, t0) :: removeEntry (b1, b2) g)).
     unfold domain; fold domain...
     rewrite EQ;
       eapply NoDup_cons...
     (*~ In (x1, x2) ((b1, b2) :: domain (removeEntry (b1, b2) g))*)
     intros ABS. unfold domain in ABS; fold domain in ABS;
       inversion ABS; intuition. 
     eapply in_domain_in_g in H6; destruct H6 as [ff [tt ABS2]]; eapply in_removeEntry in ABS2; eapply in_g_in_domain in ABS2;  intuition. 
     eauto.
     eapply no_dup_isMap in nd_pf' as pf'.
     (*  typeCheck ((b1, b2, vis, t0) :: removeEntry (b1, b2) g) pf0
    (dInp (fst u) (snd u) (fst x) (snd x) q)*)
     eapply TInL with (pf1 := pf').
     eauto. right; eapply removeEntry_in...
     unfold domain; fold domain.
     (*~ In (x1, x2) ((b1, b2) :: domain (removeEntry (b1, b2) g))*)
     intros ABS.
     inversion ABS; intuition.
     eapply in_domain_in_g in H6; destruct H6 as [ff [tt ABS2]]; eapply in_removeEntry in ABS2; eapply in_g_in_domain in ABS2;  intuition.
     (*  snd x < max (domain ((b1, b2, vis, t0) :: removeEntry (b1, b2) g)) *)
     erewrite max_same_domain with (l := domain g)...
     (*typeCheck
    ((u, vis, t1)
     :: (x, vis, t) :: removeEntry u ((b1, b2, vis, t0) :: removeEntry (b1, b2) g)) pf' q*)
     assert (nd_pf'' : NoDup(domain(((b1, b2, vis, t0)
                                       :: removeEntry (b1, b2) ((u, vis, t1) :: (x, vis, t) :: removeEntry u g))))).
     eapply no_dup_cons_removeEntry.
     destruct u, x as [x1 x2].
     rewrite removeEntry_shift with (b1 := x1).
     eapply no_dup_cons_removeEntry.
     unfold domain; fold domain; 
       eapply NoDup_cons...
     intuition.
     eapply no_dup_isMap in nd_pf'' as pf''.
     eapply typeCheck_impl with (pf1 := pf'').
     eauto.
     eauto.
     eapply IHTC.
     destruct u, x as [x1 x2].
     rewrite removeEntry_shift with (b1 := x1).
     eapply no_dup_cons_removeEntry.
     unfold domain; fold domain; 
       eapply NoDup_cons...
     eauto.
     right. right. eapply removeEntry_in...
     destruct u, x. rewrite <-removeEntry_shift, <-removeEntry_shift, removeEntry_swap. rewrite <-removeEntry_shift with (b1 := b1).
     eapply cons_cons_cons_iff...
     all:eauto.
     Unshelve. eauto. eauto. eauto. 
  -  Case TInUn.
     assert (TIN:  typeCheck g pf (dInp (fst u) (snd u) (fst x) (snd x) q))...
     intros.
     assert (u <> (b1, b2)).
     intros ABS. subst.
     assert (vis = ill).
     eapply flag_of_map with (x := (b1, b2)) (g := g)...
     discriminate.
     assert (x <> (b1, b2)).
     intros ABS. subst.
     apply in_g_in_domain in IN; intuition.
     assert (x <> u).
     intros ABS. subst.
     apply in_g_in_domain in H0; intuition.
     assert (nd_pf' :
              NoDup(domain(
                        ( (x, vis, t) :: (b1, b2, vis, t0) :: removeEntry (b1, b2) g) ))).
     destruct u, x as [x1 x2].
     assert (EQ: domain ((x1, x2, vis, t) :: (b1, b2, vis, t0) :: removeEntry (b1, b2) g) =
                   (x1, x2) :: domain ((b1, b2, vis, t0) :: removeEntry (b1, b2) g)).
     unfold domain; fold domain...
     rewrite EQ;
       eapply NoDup_cons...
     (*~ In (x1, x2) ((b1, b2) :: domain (removeEntry (b1, b2) g))*)
     intros ABS; unfold domain in ABS; fold domain in ABS;
       inversion ABS...
     eapply in_domain_in_g in H6; destruct H6 as [ff [tt ABS2]]; eapply in_removeEntry in ABS2; eapply in_g_in_domain in ABS2.  contradiction.
     eapply no_dup_isMap in nd_pf' as pf'.
     (*  typeCheck ((b1, b2, vis, t0) :: removeEntry (b1, b2) g) pf0
    (dInp (fst u) (snd u) (fst x) (snd x) q)*)
     eapply TInUn with (pf1 := pf').
     eauto. right; eapply removeEntry_in...
     unfold domain; fold domain.
     (*~ In (x1, x2) ((b1, b2) :: domain (removeEntry (b1, b2) g))*)
     intros ABS.
     inversion ABS... 
     eapply in_domain_in_g in H6; destruct H6 as [ff [tt ABS2]]; eapply in_removeEntry in ABS2; eapply in_g_in_domain in ABS2;  contradiction.
     (*  snd x < max (domain ((b1, b2, vis, t0) :: removeEntry (b1, b2) g)) *)
     erewrite max_same_domain with (l := domain g)...
     (*typeCheck
    ((x, vis, t) :: removeEntry u ((b1, b2, vis, t0) :: removeEntry (b1, b2) g)) pf' q*)
     assert (nd_pf'' : NoDup(domain(((b1, b2, vis, t0)
                                       :: removeEntry (b1, b2) ( (x, vis, t) ::g))))).
     eapply no_dup_cons_removeEntry.
     destruct u, x as [x1 x2].
     eapply NoDup_cons...
     eapply no_dup_isMap in nd_pf'' as pf''.
     eapply typeCheck_impl with (pf1 := pf'').
     eauto.
     eauto.
     eapply IHTC.
     destruct u, x as [x1 x2].
     eapply NoDup_cons...
     right... 
     destruct x. rewrite <-removeEntry_shift.  
     eapply cons_cons_iff...
     all:eauto.
     Unshelve. all:eauto.
  - Case TInU.
    assert (TINU:  typeCheck g pf (dBang (fst u) (snd u) (fst x) (snd x) q))...
    intros.
    assert (u <> (b1, b2)).
    intros ABS. subst.
    assert (vis = ill).
    eapply flag_of_map with (x := (b1, b2)) (g := g)...
    discriminate.
    assert (x <> (b1, b2)).
    intros ABS. subst.
    apply in_g_in_domain in IN; intuition.
    assert (x <> u).
    intros ABS. subst.
    apply in_g_in_domain in H0; intuition.
    assert (nd_pf' :
             NoDup(domain(
                       ( (x, vis, t) :: (b1, b2, vis, t0) :: removeEntry (b1, b2) g) ))).
    destruct u, x as [x1 x2].
    assert (EQ: domain ((x1, x2, vis, t) :: (b1, b2, vis, t0) :: removeEntry (b1, b2) g) =
                  (x1, x2) :: domain ((b1, b2, vis, t0) :: removeEntry (b1, b2) g)).
    unfold domain; fold domain...
    rewrite EQ;
      eapply NoDup_cons...
    (*~ In (x1, x2) ((b1, b2) :: domain (removeEntry (b1, b2) g))*)
    intros ABS; unfold domain in ABS; fold domain in ABS;
      inversion ABS...
    eapply in_domain_in_g in H7; destruct H7 as [ff [tt ABS2]]; eapply in_removeEntry in ABS2; eapply in_g_in_domain in ABS2.  contradiction.
    eapply no_dup_isMap in nd_pf' as pf'.
    assert (nd_pf_cons: NoDup (domain
                                 (vis_proj ((b1, b2, vis, t0) :: removeEntry (b1, b2) g) ++
                                    ill_proj ((b1, b2, vis, t0) :: removeEntry (b1, b2) g)))).
    rewrite domain_distr; eapply distr_no_dup.
    eapply no_dup_vis_proj...
    eapply no_dup_ill_proj...
    eapply disjoint_projections...
    eapply no_dup_isMap in nd_pf_cons as pf_cons.
    (*  typeCheck ((b1, b2, vis, t0) :: removeEntry (b1, b2) g) pf0
    (dBang (fst u) (snd u) (fst x) (snd x) q)*)
    eapply TInU with (pf1 := pf') (pf2 := pf_cons).
    eauto. right; eapply removeEntry_in...
    unfold domain; fold domain.
    (*~ In (x1, x2) ((b1, b2) :: domain (removeEntry (b1, b2) g))*)
    intros ABS.
    inversion ABS... 
    eapply in_domain_in_g in H7; destruct H7 as [ff [tt ABS2]]; eapply in_removeEntry in ABS2; eapply in_g_in_domain in ABS2;  contradiction.
    (*  snd x < max (domain ((b1, b2, vis, t0) :: removeEntry (b1, b2) g)) *)
    erewrite max_same_domain with (l := domain g)...
    (*assert (forall x0 : name * name,
               In x0 (domain g) <-> In x0 (domain ((b1, b2, vis, t0) :: removeEntry (b1, b2) g))). 
    eapply in_removeEntry_cons_iff, in_g_in_domain...
    unfold iff in *; intros; specialize H7 with x0.
    destruct H7...*)
    (*cons
    (vis_proj ((b1, b2, vis, t0) :: removeEntry (b1, b2) g) ++
     ill_proj ((b1, b2, vis, t0) :: removeEntry (b1, b2) g)) ?pf2*)
    assert (nd_pf_vp : NoDup (domain (vis_proj ((b1, b2, vis, t0) :: removeEntry (b1, b2) g)))).
    eapply no_dup_vis_proj...
    assert (nd_pf_ip : NoDup (domain (ill_proj ((b1, b2, vis, t0) :: removeEntry (b1, b2) g)))).
    eapply no_dup_ill_proj...
    eapply no_dup_isMap in nd_pf_vp as pf_vp.
    eapply no_dup_isMap in nd_pf_ip as pf_ip.
    erewrite cons_distr with (pf1 := pf_vp) (pf2 := pf_ip).
    split.
    (*cons (vis_proj ((b1, b2, vis, t0) :: removeEntry (b1, b2) g)) pf_vp*)
    revert dependent pf_vp.
    unfold vis_proj, ill_proj. fold vis_proj; fold ill_proj.
    arewrite vis_proj_removeEntry.
    intros.
    eapply cons_cons2 with (g2 := (ill_proj g)).
    eapply no_dup_vis_proj...
    erewrite cons_distr in H3. intuition...
    erewrite cons_distr in H3. intuition...
    eapply in_ill_proj...
    (* cons (ill_proj ((b1, b2, vis, t0) :: removeEntry (b1, b2) g)) pf_ip*)
    revert dependent pf_ip.
    unfold vis_proj, ill_proj. fold vis_proj; fold ill_proj.
    rewrite ill_proj_removeEntry.
    intros.
    eapply cons_removeEntry.
    erewrite cons_distr in H3. intuition...
    assumption.
    (* typeCheck ((x, vis, t) :: (b1, b2, vis, t0) :: removeEntry (b1, b2) g) pf' q*)
    assert (nd_pf'' : NoDup(domain(((b1, b2, vis, t0)
                                      :: removeEntry (b1, b2) ( (x, vis, t) ::g))))).
    eapply no_dup_cons_removeEntry.
    destruct u, x as [x1 x2].
    eapply NoDup_cons...
    eapply no_dup_isMap in nd_pf'' as pf''.
    eapply typeCheck_impl with (pf1 := pf'').
    eauto.
    eauto.
    eapply IHTC.
    destruct u, x as [x1 x2].
    eapply NoDup_cons...
    right... 
    destruct x. rewrite <-removeEntry_shift.  
    eapply cons_cons_iff...
    all:eauto.
    Unshelve. eauto. eauto. eauto.
    all : try eapply no_dup_isMap, no_dup_vis_proj
                                   || eapply no_dup_isMap, no_dup_ill_proj.
    all : eauto.
Qed.
