Require Import
  Bool List Omega PeanoNat Program.Equality  Classical
  ListAddOns Max RemoveEntry Domain NewEntries
  header
  operations pi_syntax 
  pairEq type_system semantics
  type_operations_1
  split_exists_neutral
  sub_split
  no_dup_split_no_dup
  split_existential
  split_cons_remove
  split_operations
  split_cons_remove
  disjoint_newEntries
  Permutation.

Require Import CpdtTactics LibTactics.




Hint Resolve pol_cup_empty.
Hint Resolve pol_cup_empty_r.
Hint Resolve pol_cup_empty_res.

Hint Resolve no_dup_split_no_dup_r no_dup_split_no_dup_l.

Hint Resolve beq_nat_refl.

Ltac appIH IH := 
  try eapply IH;  econstructor; eauto.



Lemma split_plus_un_isrestricted: forall g1 g2 g pf1 pf2 pf b1 b2 t,
     typeOf g1 (b1, b2) t ->
     is_unrestricted t ->
     tEnv_split g1 g2 g pf1 pf2 pf ->
     (typeOf g2 (b1, b2) t /\ typeOf g (b1, b2) t).
 Proof with eauto.
   intros g1 g2 g pf1 pf2 pf b1 b2 t TYP ISUN TS.
   inversion TYP; subst.
   destruct ISUN as (p &t1 &EQ); subst.
   eapply sub_split.tsub_un with (pf := pf) in H as K.
   inversion K; subst.
   eapply sub_split.tsuper_payload  with (pf1 := pf2) in H0 as (p1 &W).
   inversion TYP; inversion K; inversion W; subst.
   assert (EQ: p = p1 /\ p1 = p).
   eapply split_cons_remove.split_plus_un with (pf1 := pf1)...
   destruct EQ; subst; intuition.
   eapply split_comm; eauto.
   eauto.
 Qed.
 
Lemma lts_flagOf_vis_entry
  c1 c2 g g1 a p p1 pf:
  lts g p a g1 p1 pf ->
  flagOf g (c1, c2) vis ->
  flagOf g1 (c1, c2) vis.
Proof with eauto.
  introv LTS FYP.
  gen c1 c2.
  dependent induction LTS; introv FYP.
  
  - intuition; appIH IHLTS.
  - case_eq (pair_eq (a1, a2) (c1, c2)).
    introv PEQ; try rewrite <-pairEq_eq in PEQ; inv PEQ;
      appIH IHLTS.
    introv PNEQ.
    case_eq (pair_eq (b1, b2) (c1, c2)).
    introv PEQ; try rewrite <-pairEq_eq in PEQ; inv PEQ...
    introv PNEQ2.
    eapply pairEq_neq in PNEQ; eapply pairEq_neq in PNEQ2;
      inv FYP; econstructor; try repeat right; repeat eapply removeEntry_in...
    
  - case_eq (pair_eq (b1, b2) (c1, c2)).
    introv PEQ; try rewrite <-pairEq_eq in PEQ; inv PEQ...
    introv PNEQ.
    eapply pairEq_neq in PNEQ;
      inv FYP; econstructor; try repeat right; repeat eapply removeEntry_in...

  -  case_eq (pair_eq (a1, a2) (c1, c2)).
     introv PEQ; try rewrite <-pairEq_eq in PEQ; inv PEQ;
       appIH IHLTS.
     introv PNEQ.
     case_eq (pair_eq (b1, b2) (c1, c2)).
     introv PEQ; try rewrite <-pairEq_eq in PEQ; inv PEQ...
     introv PNEQ2.
     eapply pairEq_neq in PNEQ; eapply pairEq_neq in PNEQ2;
       inv FYP; econstructor; try repeat right; repeat eapply removeEntry_in...

  - case_eq (pair_eq (b1, b2) (c1, c2)).
    introv PEQ; try rewrite <-pairEq_eq in PEQ; inv PEQ...
    introv PNEQ.
    eapply pairEq_neq in PNEQ;
      inv FYP; econstructor; try repeat right; repeat eapply removeEntry_in...

  -  
    case_eq (pair_eq (b1, b2) (c1, c2)).
    introv PEQ; try rewrite <-pairEq_eq in PEQ; inv PEQ;
      econstructor; eapply in_app_iff; right...
    introv PNEQ.
    eapply pairEq_neq in PNEQ;
      inv FYP; econstructor; eapply in_app_iff;
      try repeat right; 
      repeat eapply removeEntry_in...

  - subst g0. 
    case_eq (pair_eq (a1, a2) (c1, c2)).
    introv PEQ; try rewrite <-pairEq_eq in PEQ; inv PEQ;
      appIH IHLTS.
    introv PNEQ.
    case_eq (pair_eq (b1, b2) (c1, c2)).
    introv PEQ; try rewrite <-pairEq_eq in PEQ; inv PEQ...
    introv PNEQ2.
    eapply pairEq_neq in PNEQ; eapply pairEq_neq in PNEQ2;
      inv FYP; econstructor; try repeat right; repeat eapply removeEntry_in...

  - subst g0 g3. 
    case_eq (pair_eq (a1, a2) (c1, c2)).
    introv PEQ; try rewrite <-pairEq_eq in PEQ; inv PEQ;
      appIH IHLTS.
    introv PNEQ.
    case_eq (pair_eq (b1, b2) (c1, c2)).
    introv PEQ; try rewrite <-pairEq_eq in PEQ; inv PEQ; inv FYP.
    assert (vis =hid); try discriminate...
    introv PNEQ2.
    eapply pairEq_neq in PNEQ; eapply pairEq_neq in PNEQ2;
      inv FYP; econstructor; try repeat right; repeat eapply removeEntry_in...

  - subst g0 g'.
    case_eq (pair_eq (b1, b2) (c1, c2)).
    introv PEQ; try rewrite <-pairEq_eq in PEQ; inv PEQ.
    appIH IHLTS2...   
    
    inv FYP.
    introv PNEQ.
    appIH IHLTS2... 
    eapply pairEq_neq in PNEQ;
      try repeat right; 
      repeat eapply removeEntry_in...

  - subst g' g0.
    inv FYP.
    assert (GGOAL: flagOf g3 (c1, c2) vis).
    appIH IHLTS2;
      try repeat right; repeat eapply removeEntry_in...
    intros ABS; inv ABS;
      assert (vis =hid); try discriminate...
    inv GGOAL;
      econstructor; try repeat right; repeat eapply removeEntry_in;
      try intros ABS; try inv ABS...
    assert (vis =hid); try discriminate...

  - inv FYP; appIH IHLTS...
    try repeat right; repeat eapply removeEntry_in...
    intros ABS; inv ABS;
      assert (vis =hid); try discriminate...

  -  case_eq (pair_eq (b1, b2) (c1, c2)).
     introv PEQ; try rewrite <-pairEq_eq in PEQ; inv PEQ.
     inv FYP.
     assert (ABS: vis =hid /\ t0 = t).
     eapply in_isMap...
     try eapply in_app_iff; try right...
     destruct ABS; discriminate.
     introv PNEQ; subst g. 
     assert (IH: flagOf (h1 ++ (b1, b2, vis, t) :: h2) (c1, c2) vis ).
     inverts FYP as IN; eapply in_app_iff in IN as [HD | TL];
       try inverts TL as EQ; try inv EQ;
       econstructor; eapply in_app_iff...
     repeat right...

     
     eapply IHLTS in IH.
     inverts IH as IN. eapply in_app_iff in IN as [HD | TL].
     econstructor.
     eapply in_app_iff...
     eapply in_inv in TL as [ABS | OK].
     try inv ABS; try eapply pairEq_neq in PNEQ; try contradiction.
     econstructor; eapply in_app_iff; repeat right...
Qed.


Lemma split_rewrite_pf_gen: forall g1 g2 g pf1 pf2 pf pfa1 pfa2 pf',
    tEnv_split g1 g2 g pf1 pf2 pf ->
    tEnv_split g1 g2 g pfa1 pfa2 pf'.
Proof with eauto.
  intros g1 g2 g pf1 pf2 pf pfa1 pfa2 pf' TS. 
  dependent induction TS.
  subst; apply SpNil...
  assert (pfk :  isMap (removeEntry n g3)).
  apply isMap_removeEntry...
  apply SpLin with
    n f f' g p q p' t (removeEntry n g3)  pf'0 pf'' pfk.
  all:eauto.
  subst.
  eauto.
  subst.
  eapply SpUn...
  subst; eauto.
  eapply SpTop...
Qed.



Lemma tEnv_split_add_fp:
  forall b1 b2 f1 f2 f s1 s2 s g1 g2 g
         pf1 pf2 pf (nd_pf : NoDup (domain g)) pf' pf'' pf''',
    type_plus s1 s2 s ->
    flag_plus f1 f2 f ->
    (is_unrestricted s -> s1 = s2 /\ s2 = s) ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    tEnv_split
      ((b1, b2, f1, s1) :: removeEntry (b1, b2) g1)
      ((b1, b2, f2, s2) :: removeEntry (b1, b2) g2)
      ((b1, b2, f, s) :: removeEntry (b1, b2) g)
      pf' pf'' pf'''.
Proof with eauto.
  intros b1 b2 f1 f2 f s1 s2 s g1 g2 g
    pf1 pf2 pf nd_pf pf' pf'' pf''' TP FP ISUN
    TS.
  assert (pfa1 : isMap (removeEntry (b1, b2) g1)).
  eapply isMap_removeEntry...
  assert (pfa2 : isMap (removeEntry (b1, b2) g2)).
  eapply isMap_removeEntry...
  assert (pfa : isMap (removeEntry (b1, b2) g)).
  eapply isMap_removeEntry...
  specialize split_remove with
    (pf1 := pf1)
    (pf2 := pf2) (pf3 := pf) (pf1' := pfa1)
    (pf2' := pfa2)
    (pf3' := pfa)
    as TS2.
  
  
  (* dependent induction TS. 
      - subst; simpl...*)
  assert (pfn1 : isMap (removeEntry (b1, b2) ((b1, b2, f1, s1) :: removeEntry (b1, b2) g1))).
  eapply isMap_removeEntry...
  assert (pfn2 : isMap (removeEntry (b1, b2) ((b1, b2, f2, s2) :: removeEntry (b1, b2) g2))).
  eapply isMap_removeEntry...
  assert (pfn : isMap (removeEntry (b1, b2) ((b1, b2, f, s) :: removeEntry (b1, b2) g))).
  eapply isMap_removeEntry...
  inversion TP; inversion FP; subst...
  try eapply SpTop with (pf' := pfn1)  (pf'' := pfn2) (pf''' := pfn);
    revert dependent pfn1;
    revert dependent pfn2;
    revert dependent pfn;
    simpl;
    try  erewrite pairEq_eq_true;
    intros; try
              eapply split_rewrite_pf_gen...
  try eapply SpTop with (pf' := pfn1)  (pf'' := pfn2) (pf''' := pfn);
    revert dependent pfn1;
    revert dependent pfn2;
    revert dependent pfn;
    simpl;
    try  erewrite pairEq_eq_true;
    intros; try
              eapply split_rewrite_pf_gen...
  try eapply SpTop with (pf' := pfn1)  (pf'' := pfn2) (pf''' := pfn);
    revert dependent pfn1;
    revert dependent pfn2;
    revert dependent pfn;
    simpl;
    try  erewrite pairEq_eq_true;
    intros; try
              eapply split_rewrite_pf_gen...
  try eapply SpTop with (pf' := pfn1)  (pf'' := pfn2) (pf''' := pfn);
    revert dependent pfn1;
    revert dependent pfn2;
    revert dependent pfn;
    simpl;
    try  erewrite pairEq_eq_true;
    intros; try
              eapply split_rewrite_pf_gen...
  try eapply SpLin with (pf' := pfn1)  (pf'' := pfn2) (pf''' := pfn);
    revert dependent pfn1;
    revert dependent pfn2;
    revert dependent pfn;
    simpl;
    try  erewrite pairEq_eq_true;
    intros; try
              eapply split_rewrite_pf_gen...
  try eapply SpLin with (pf' := pfn1)  (pf'' := pfn2) (pf''' := pfn);
    revert dependent pfn1;
    revert dependent pfn2;
    revert dependent pfn;
    simpl;
    try  erewrite pairEq_eq_true;
    intros; try
              eapply split_rewrite_pf_gen...
  try eapply SpLin with (pf' := pfn1)  (pf'' := pfn2) (pf''' := pfn);
    revert dependent pfn1;
    revert dependent pfn2;
    revert dependent pfn;
    simpl;
    try  erewrite pairEq_eq_true;
    intros; try
              eapply split_rewrite_pf_gen...
  try eapply SpLin with (pf' := pfn1)  (pf'' := pfn2) (pf''' := pfn);
    revert dependent pfn1;
    revert dependent pfn2;
    revert dependent pfn;
    simpl;
    try  erewrite pairEq_eq_true;
    intros; try
              eapply split_rewrite_pf_gen...

  assert (is_unrestricted (Chan un (pol_cup p1 p2) t)) by eapply un_is_unrestricted; intuition; inversion H1; inversion H2; subst;try eapply SpUn with (pf' := pfn1)  (pf'' := pfn2) (pf''' := pfn);
    revert dependent pfn1;
    revert dependent pfn2;
    revert dependent pfn;
    simpl;
    try  erewrite pairEq_eq_true;
    intros; try
              eapply split_rewrite_pf_gen...
  rewrite <-H4...

  assert (is_unrestricted (Chan un (pol_cup p1 p2) t)) by eapply un_is_unrestricted; intuition; inversion H1; inversion H2; subst;try eapply SpUn with (pf' := pfn1)  (pf'' := pfn2) (pf''' := pfn);
    revert dependent pfn1;
    revert dependent pfn2;
    revert dependent pfn;
    simpl;
    try  erewrite pairEq_eq_true;
    intros; try
              eapply split_rewrite_pf_gen...
  rewrite <-H4...

  assert (is_unrestricted (Chan un (pol_cup p1 p2) t)) by eapply un_is_unrestricted; intuition; inversion H1; inversion H2; subst;try eapply SpUn with (pf' := pfn1)  (pf'' := pfn2) (pf''' := pfn);
    revert dependent pfn1;
    revert dependent pfn2;
    revert dependent pfn;
    simpl;
    try  erewrite pairEq_eq_true;
    intros; try
              eapply split_rewrite_pf_gen...
  rewrite <-H4...

  assert (is_unrestricted (Chan un (pol_cup p1 p2) t)) by eapply un_is_unrestricted; intuition; inversion H1; inversion H2; subst;try eapply SpUn with (pf' := pfn1)  (pf'' := pfn2) (pf''' := pfn);
    revert dependent pfn1;
    revert dependent pfn2;
    revert dependent pfn;
    simpl;
    try  erewrite pairEq_eq_true;
    intros; try
              eapply split_rewrite_pf_gen...
  rewrite <-H4...
  Unshelve.
  all:eauto.
Qed.

Hint Constructors flag_plus.

Lemma tEnv_split_add_vis:
  forall b1 b2 s1 s2 s g1 g2 g
         pf1 pf2 pf (nd_pf : NoDup (domain g)) pf' pf'' pf''',
    type_plus s1 s2 s ->
    (is_unrestricted s -> s1 = s2 /\ s2 = s) ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    tEnv_split
      ((b1, b2, vis, s1) :: removeEntry (b1, b2) g1)
      ((b1, b2, vis, s2) :: removeEntry (b1, b2) g2)
      ((b1, b2, vis, s) :: removeEntry (b1, b2) g)
      pf' pf'' pf'''.
Proof with eauto.
  intros; eapply tEnv_split_add_fp...
Qed.

Lemma split_type_plus : forall g1 g2 g pf1 pf2 pf a t1 t,
    typeOf g1 a t1 ->
    typeOf g a t ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    exists t2,
      typeOf g2 a t2 /\
        type_plus t1 t2 t.
Proof with eauto.
  intros  g1 g2 g pf1 pf2 pf a t1 t TYP1 TYP TS.
  dependent induction TS.
  - subst. inversion TYP1. inversion H.
  - destruct a as [a1 a2]; destruct n as [n1 n2].
    case_eq (pair_eq (n1, n2) (a1, a2)). intros PEQ. 
    rewrite <-pairEq_eq in PEQ; inversion PEQ; subst.
    exists  (Chan lin q t0).
    split...
    inversion TYP1; inversion TYP; inversion H5; subst.
    assert (f = f0 /\ Chan lin p t0 = t1).
    apply in_isMap with (x := (a1, a2)) (g := g1)...
    assert (f1 = f2 /\ t =  Chan lin p' t0).
    apply in_isMap with (x := (a1, a2)) (g := g3)...
    destruct H6; destruct H7; subst.
    apply Tp_LinPlus...
    intros PNEQ. assert (PNEQ2 := PNEQ).
    rewrite <-pairEq_neq in PNEQ.
    inversion TYP1. subst.
    assert ( In (a1, a2, f0, t1)  (removeEntry (n1, n2) g1)).
    apply removeEntry_in...
    apply T_Entry in H3 as IHH.
    apply IHTS in IHH.
    destruct IHH as [t2 [TYP2 TP]].
    exists t2.
    split. inversion TYP2.  subst. apply in_removeEntry in H7...
    eauto.
    inversion TYP; subst. apply removeEntry_in with (y := (n1, n2)) in H7...
  - destruct a as [a1 a2]; destruct n as [n1 n2].
    case_eq (pair_eq (n1, n2) (a1, a2)). intros PEQ. 
    rewrite <-pairEq_eq in PEQ; inversion PEQ; subst.
    exists  (Chan un p t0).
    split...
    inversion TYP1; inversion TYP; inversion H4; subst.
    assert (f = f0 /\ Chan un p t0 = t1).
    apply in_isMap with (x := (a1, a2)) (g := g1)...
    assert (f1 = f2 /\ t =  Chan un p t0).
    apply in_isMap with (x := (a1, a2)) (g := g3)...
    destruct H5; destruct H6; subst.
    assert (POLEQ : pol_cup p p = p)...
    rewrite <-POLEQ at 3.
    apply Tp_UnPlus...
    intros PNEQ. assert (PNEQ2 := PNEQ).
    rewrite <-pairEq_neq in PNEQ.
    inversion TYP1. subst.
    assert ( In (a1, a2, f0, t1)  (removeEntry (n1, n2) g1)).
    apply removeEntry_in...
    apply T_Entry in H2 as IHH.
    apply IHTS in IHH.
    destruct IHH as [t2 [TYP2 TP]].
    exists t2.
    split. inversion TYP2.  subst. apply in_removeEntry in H6...
    eauto.
    inversion TYP; subst. apply removeEntry_in with (y := (n1, n2)) in H6...
  - destruct a as [a1 a2]; destruct n as [n1 n2].
    case_eq (pair_eq (n1, n2) (a1, a2)). intros PEQ. 
    rewrite <-pairEq_eq in PEQ; inversion PEQ; subst.
    exists  Top.
    split...
    inversion TYP1; inversion TYP; inversion H4; subst.
    assert (f = f0 /\ Top = t1).
    apply in_isMap with (x := (a1, a2)) (g := g1)...
    assert (f1 = f2 /\ t =  Top).
    apply in_isMap with (x := (a1, a2)) (g := g3)...
    destruct H5; destruct H6; subst.
    apply Tp_Base...
    intros PNEQ. assert (PNEQ2 := PNEQ).
    rewrite <-pairEq_neq in PNEQ.
    inversion TYP1. subst.
    assert ( In (a1, a2, f0, t1)  (removeEntry (n1, n2) g1)).
    apply removeEntry_in...
    apply T_Entry in H2 as IHH.
    apply IHTS in IHH.
    destruct IHH as [t2 [TYP2 TP]].
    exists t2.
    split. inversion TYP2.  subst. apply in_removeEntry in H6...
    eauto.
    inversion TYP; subst. apply removeEntry_in with (y := (n1, n2)) in H6...
Qed.


Lemma split_type_plus_r : forall g1 g2 g pf1 pf2 pf a t1 t,
    typeOf g1 a t1 ->
    typeOf g2 a t ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    exists t2,
      typeOf g a t2 /\
        type_plus t1 t t2.
Proof with eauto.
  intros  g1 g2 g pf1 pf2 pf a t1 t TYP1 TYP TS.
  dependent induction TS.
  - subst. inversion TYP1. inversion H.
  - destruct a as [a1 a2]; destruct n as [n1 n2].
    case_eq (pair_eq (n1, n2) (a1, a2)). intros PEQ. 
    rewrite <-pairEq_eq in PEQ; inversion PEQ; subst.
    exists  (Chan lin p' t0).
    split...
    inversion TYP1; inversion TYP; inversion H5; subst.
    assert (f = f0 /\ Chan lin p t0 = t1).
    apply in_isMap with (x := (a1, a2)) (g := g1)...
    assert (f1 = g /\ t =  Chan lin q t0).
    apply in_isMap with (x := (a1, a2)) (g := g2)...
    destruct H6; destruct H7; subst.
    apply Tp_LinPlus...
    intros PNEQ. assert (PNEQ2 := PNEQ).
    rewrite <-pairEq_neq in PNEQ.
    inversion TYP1. subst.
    assert ( In (a1, a2, f0, t1)  (removeEntry (n1, n2) g1)).
    apply removeEntry_in...
    apply T_Entry in H3 as IHH.
    apply IHTS in IHH.
    destruct IHH as [t2 [TYP2 TP]].
    exists t2.
    split. inversion TYP2.  subst. apply in_removeEntry in H7...
    eauto.
    inversion TYP; subst. apply removeEntry_in with (y := (n1, n2)) in H7...
  - destruct a as [a1 a2]; destruct n as [n1 n2].
    case_eq (pair_eq (n1, n2) (a1, a2)). intros PEQ. 
    rewrite <-pairEq_eq in PEQ; inversion PEQ; subst.
    exists  (Chan un p t0).
    split...
    inversion TYP1; inversion TYP; inversion H4; subst.
    assert (f = f0 /\ Chan un p t0 = t1).
    apply in_isMap with (x := (a1, a2)) (g := g1)...
    assert (f1 = g /\ t =  Chan un p t0).
    apply in_isMap with (x := (a1, a2)) (g := g2)...
    destruct H5; destruct H6; subst.
    assert (POLEQ : pol_cup p p = p)...
    rewrite <-POLEQ at 3.
    apply Tp_UnPlus...
    intros PNEQ. assert (PNEQ2 := PNEQ).
    rewrite <-pairEq_neq in PNEQ.
    inversion TYP1. subst.
    assert ( In (a1, a2, f0, t1)  (removeEntry (n1, n2) g1)).
    apply removeEntry_in...
    apply T_Entry in H2 as IHH.
    apply IHTS in IHH.
    destruct IHH as [t2 [TYP2 TP]].
    exists t2.
    split. inversion TYP2.  subst. apply in_removeEntry in H6...
    eauto.
    inversion TYP; subst. apply removeEntry_in with (y := (n1, n2)) in H6...
  - destruct a as [a1 a2]; destruct n as [n1 n2].
    case_eq (pair_eq (n1, n2) (a1, a2)). intros PEQ. 
    rewrite <-pairEq_eq in PEQ; inversion PEQ; subst.
    exists  Top.
    split...
    inversion TYP1; inversion TYP; inversion H4; subst.
    assert (f = f0 /\ Top = t1).
    apply in_isMap with (x := (a1, a2)) (g := g1)...
    assert (f1 = g /\ t =  Top).
    apply in_isMap with (x := (a1, a2)) (g := g2)...
    destruct H5; destruct H6; subst.
    apply Tp_Base...
    intros PNEQ. assert (PNEQ2 := PNEQ).
    rewrite <-pairEq_neq in PNEQ.
    inversion TYP1. subst.
    assert ( In (a1, a2, f0, t1)  (removeEntry (n1, n2) g1)).
    apply removeEntry_in...
    apply T_Entry in H2 as IHH.
    apply IHTS in IHH.
    destruct IHH as [t2 [TYP2 TP]].
    exists t2.
    split. inversion TYP2.  subst. apply in_removeEntry in H6...
    eauto.
    inversion TYP; subst. apply removeEntry_in with (y := (n1, n2)) in H6...
Qed.



Lemma split_hid_vis b1 b2 t1 t2 t l1 l2 m1 m2 h1 h2 pff1 pff2 pff pf1 pf2 pf (nd_pf : NoDup ( domain (h1 ++ (b1, b2, hid, t) :: h2))):
  tEnv_split (l1 ++ (b1, b2, hid, t1) :: l2)
    (m1 ++ (b1, b2, ill, t2) :: m2)
    (h1 ++ (b1, b2, hid, t) :: h2)
    pff1 pff2 pff ->
  tEnv_split (l1 ++ (b1, b2, vis, t1) :: l2)
    (m1 ++ (b1, b2, vis, t2) :: m2)
    (h1 ++ (b1, b2, vis, t) :: h2) pf1 pf2 pf.
Proof with eauto.
  introv TS.

     assert (P0: forall c1 c2 tt1 (ll1 : typeEnv) ll2,
                   Permutation ((c1, c2, vis, tt1) :: ll1 ++ ll2)(ll1 ++ (c1, c2, vis, tt1) :: ll2)).
        intros;
          specialize Permutation_cons_append with (l := ll1) (x :=  (c1, c2, vis, tt1)) as P1.
     assert (EQ2: ((c1, c2, vis, tt1) :: ll1 ++ ll2 =
                   ((c1, c2, vis, tt1) :: ll1 )++ll2))...
     assert (EQ3: ll1 ++ (c1, c2, vis, tt1) :: ll2 =
                  (ll1 ++ (c1, c2, vis, tt1) :: nil) ++ ll2).
     erewrite cons_app,<-app_assoc...
     erewrite EQ2,EQ3;
       eapply Permutation_app...

  assert (nd_pf1 : (NoDup (domain ( (l1 ++ (b1, b2, hid, t1) :: l2) )))).
  eapply no_dup_split_no_dup_l...

  assert (nd_pf2 : (NoDup (domain ( (m1 ++ (b1, b2, ill, t2) :: m2) )))).
  eapply no_dup_split_no_dup_r in TS...

    assert (NIN : ~In (b1, b2) (domain l1) /\ ~In (b1, b2) (domain l2)).
    erewrite domain_distr in nd_pf1; simpl in nd_pf1;
      eapply no_dup_iff in nd_pf1 as (ND1 &ND2 &DIS); split;
      introv ABS.
    try eapply disjoint_absurd...
    inv ND2...
  destruct NIN as (NINL1 &NINL2).

   assert (NIN : ~In (b1, b2) (domain m1) /\ ~In (b1, b2) (domain m2)).
   erewrite domain_distr in nd_pf2; simpl in nd_pf2;
      eapply no_dup_iff in nd_pf2 as (ND1 &ND2 &DIS); split;
      introv ABS.
    try eapply disjoint_absurd...
    inv ND2...
  destruct NIN as (NINM1 &NINM2).

     assert (NIN : ~In (b1, b2) (domain h1) /\ ~In (b1, b2) (domain h2)).
   erewrite domain_distr in nd_pf; simpl in nd_pf;
      eapply no_dup_iff in nd_pf as (ND1 &ND2 &DIS); split;
      introv ABS.
    try eapply disjoint_absurd...
    inv ND2...
  destruct NIN as (NINH1 &NINH2).

  assert (nd_prf: (NoDup (domain ((b1, b2, vis, t) :: h1 ++ h2)))).
  simpl; econstructor; 
    try rewrite domain_distr;
    try eapply not_in_and_app...
  simpl in *; rewrite domain_distr in *;
    simpl in *; 
    try eapply no_dup_iff in nd_pf as (ND1 &ND2 &DIS);
    try eapply no_dup_iff;
    repeat split;
    try inv ND2;
      try eapply disjoint_r_cons...
  eapply no_dup_isMap in nd_prf as prf.

  eapply split_iff with (pf := prf); try assumption.
  rewrite domain_distr in *; simpl in *...

  assert (nd_prf2: (NoDup (domain ((b1, b2, vis, t2) :: m1 ++ m2)))).
 simpl; econstructor; 
    try rewrite domain_distr;
    try eapply not_in_and_app...
  simpl in *; rewrite domain_distr in *;
    simpl in *; 
    try eapply no_dup_iff in nd_pf2 as (ND1 &ND2 &DIS);
    try eapply no_dup_iff;
    repeat split;
    try inv ND2;
      try eapply disjoint_r_cons...
  eapply no_dup_isMap in nd_prf2 as prf2.
 
  eapply split_iff2 with (pf2 := prf2); try assumption.
  eapply no_dup_split_no_dup_r in TS;
  rewrite domain_distr in *; simpl in *...

  assert (nd_prf1: (NoDup (domain ((b1, b2, vis, t1) :: l1 ++ l2)))).
  simpl; econstructor; 
    try rewrite domain_distr;
    try eapply not_in_and_app...
  simpl in *; rewrite domain_distr in *;
    simpl in *; 
    try eapply no_dup_iff in nd_pf1 as (ND1 &ND2 &DIS);
    try eapply no_dup_iff;
    repeat split;
    try inv ND2;
      try eapply disjoint_r_cons...
  eapply no_dup_isMap in nd_prf1 as prf1.

  eapply split_comm.
  eapply split_iff2 with (pf2 := prf1); try assumption.
   rewrite domain_distr in *; simpl in *...
  eapply split_comm.

  assert (L1: removeEntry (b1, b2) (l1 ++ l2) = (l1 ++ l2)).
  eapply removeEntry_idempot; try rewrite domain_distr;
    try eapply not_in_and_app...
  assert (M1: removeEntry (b1, b2) (m1 ++ m2) = (m1 ++ m2)).
  eapply removeEntry_idempot; try rewrite domain_distr;
    try eapply not_in_and_app...
  assert (HH1: removeEntry (b1, b2) (h1 ++ h2) = (h1 ++ h2)).
  eapply removeEntry_idempot; try rewrite domain_distr;
    try eapply not_in_and_app...

      
      gen prf1 prf2 prf.
      erewrite <-L1, <-M1, <-HH1;
        intros.
      eapply tEnv_split_add_vis;
        try eassumption.

      rewrite domain_distr in *;
        simpl in nd_pf;
        try erewrite no_dup_iff in *;
        intuition;
        try inv H5;
        try eapply disjoint_r_cons...

      eapply split_type_plus with (a := (b1, b2))
        in TS as (t2' &TYP2 &TP).
      assert (t2 = t2').
      inverts TYP2 as IN;
        try eapply in_app_iff in IN as [ABS1 | [EQ | ABS2]];
        try eapply in_g_in_domain in ABS1;
        try inv EQ;
        try eapply in_g_in_domain in ABS2;
        try contradiction...
      subst...

      econstructor; eapply in_app_iff; right...
      econstructor; eapply in_app_iff; right...
      introv (ff&tt&ISUN); try subst t.

      destruct t1; try destruct m.
      eapply tsub_payload with (a1 := b1) (a2 := b2) (m := lin)in TS
          as (pp &ABS);
        try inverts ABS as IN;
        try eapply in_app_iff in IN as [ABS1 | [EQ |ABS2]];
          try eapply in_g_in_domain in ABS1;
        try inv EQ;
        try eapply in_g_in_domain in ABS2;
        try contradiction...
      
      eapply in_app_iff; right...
      eapply split_plus_un_isrestricted
        with (b1 := b1) (b2 := b2) in TS as (TYP1 &TYP2);
        try inverts TYP1 as IN;
        try eapply in_app_iff in IN as [ABS1 | [EQ |ABS2]];
          try eapply in_g_in_domain in ABS1;
        try inv EQ;
        try eapply in_g_in_domain in ABS2;
        try contradiction;
          try inverts TYP2 as IN;
        try eapply in_app_iff in IN as [ABS1 | [EQ |ABS2]];
          try eapply in_g_in_domain in ABS1;
        try inv EQ;
        try eapply in_g_in_domain in ABS2;
        try contradiction...

      econstructor; eapply in_app_iff; right...
      eapply un_is_unrestricted...

      eapply tsub_top with (a1 := b1) (a2 := b2) in TS as ABS;
         try inverts ABS as IN;
        try eapply in_app_iff in IN as [ABS1 | [EQ |ABS2]];
          try eapply in_g_in_domain in ABS1;
        try inv EQ;
        try eapply in_g_in_domain in ABS2;
        try contradiction...

      eapply in_app_iff; right...

      assert (NDPF1 := nd_pf1).
      assert (NDPF2 := nd_pf2).
      assert (NDPF := nd_pf).
      eapply no_dup_removeEntry_no_dup with (a := (b1, b2)), no_dup_isMap in nd_pf1;
        eapply no_dup_removeEntry_no_dup  with (a := (b1, b2)),no_dup_isMap in nd_pf2;
        eapply no_dup_removeEntry_no_dup  with (a := (b1, b2)),no_dup_isMap in nd_pf.
               
      eapply split_remove
        with (b := (b1,b2))
             (pf1' := nd_pf1)
             (pf2' := nd_pf2)
             (pf3' := nd_pf) in TS;
        try assumption.

      gen nd_pf1 nd_pf2 nd_pf.
      repeat rewrite removeEntry_app_shift;
        simpl; repeat rewrite pairEq_eq_true;
        intros...
      eapply split_rewrite_pf_gen...

      
     intros; split; try eapply Permutation_in...
     try eapply Permutation_sym...

      
     intros; split; try eapply Permutation_in...
     try eapply Permutation_sym...

    
     
     intros; split; try eapply Permutation_in...
     try eapply Permutation_sym...

     Unshelve.
     simpl in *; inv nd_prf1; try eapply no_dup_isMap...
     simpl in *; inv nd_prf2; try eapply no_dup_isMap...
     simpl in *; inv nd_prf; try eapply no_dup_isMap...
Qed. 
      
  Lemma split_lts_exists_remove_l :
  forall g1 g2 g pf1 pf2 pf p g' p' nd_pf
         x1 x2 y1 y2 m q t,
    typeOf g1 (x1, x2) (Chan m q t) ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    lts g p (aIn x1 x2 y1 y2) g' p' nd_pf ->
    exists ty t',
      typeOf g1 (y1, y2) ty /\
        type_plus t ty t'.
Proof with eauto using no_dup_isMap, split_hid_vis.
  intros g1 g2 g pf1 pf2 pf p g' p' nd_pf
    x1 x2 y1 y2 m q t TYP TSPLIT LTS.
  gen g1 g2.
  dependent induction LTS.
  - intros.
    assert (IH : aIn x1 x2 y1 y2 = aIn x1 x2 y1 y2)...
  (* eapply IHLTS in IH as (ty &tt &TYP1 &TP1)...
      eexists; split...*)
  - intros; inversion TYP; clear TYP; subst...
    apply tsub_payload with
      g1 g2 g pf1 pf2 pf x1 x2 f0 m q t
      in H3 as TYPx.
    destruct TYPx as [r TYP2x]; inversion TYP2x; subst.
    apply type_of_map with
      g (x1, x2) (Chan lin inp t0) (Chan m r t)
      in pf as ASSERT. inversion ASSERT; subst.
    destruct t1.
    + apply tsuper_payload
        with (g1 := g1) (g2 := g2) (pf1 := pf1)
             (pf2 := pf2) (pf := pf) in H2
          as TYP1y.
      destruct TYP1y as [p1 TYP1y].
      inversion TYP1y; clear TYP1y; subst...
      apply tsub_payload with
        g1 g2 g pf1 pf2 pf y1 y2 f2 m p1 t1
        in H5 as TYPmy.
      destruct TYPmy as [p2 TYPmy]; inversion TYPmy; subst.
      clear ASSERT.
      apply type_of_map with
        g (y1, y2) (Chan m p0 t1) (Chan m p2 t1)
        in pf as ASSERT. inversion ASSERT.
      subst.
      clear TYPmy ASSERT H3 H4 TYP2x H6.
      exists (Chan m p1 t1).
      assert (TYPx := H1); clear H1.
      assert (TYPy := H5); clear H5.
      assert (H1 := TYPy).
      destruct m.
      * destruct p1.
        ** exists t. split. eauto...
           inversion H; subst...
        ** apply tsub_in with
             (g2 := g2) (g1 := g1) (pf1 := pf1)
             (pf2 := pf2) (pf := pf) in H1.
           destruct H1 as [ABS | ABS].
           apply type_of_map with
             g (y1, y2) (Chan lin p2 t1) (Chan lin inp t1)
             in pf as ABS2. inversion ABS2; subst...
           exists t2; eauto.
           split.
           all:eauto.
           apply type_plus_comm...
           apply type_of_map with
             g (y1, y2) (Chan lin p2 t1) (Chan lin io t1)
             in pf as ABS2. inversion ABS2; subst...
           inversion H; inversion H6; subst...
           all:eauto.
        **  apply tsub_out with
              (g2 := g2) (g1 := g1) (pf1 := pf1)
              (pf2 := pf2) (pf := pf) in H1.
            destruct H1 as [ABS | ABS].
            apply type_of_map with
              g (y1, y2) (Chan lin p2 t1) (Chan lin out t1)
              in pf as ABS2. inversion ABS2; subst...
            exists t2; eauto.
            split.
            all:eauto.
            apply type_plus_comm...
            apply type_of_map with
              g (y1, y2) (Chan lin p2 t1) (Chan lin io t1)
              in pf as ABS2. inversion ABS2; subst...
            inversion H; inversion H6; subst...
            all:eauto.
        **  apply tsub_io with
              (g2 := g2) (g1 := g1) (pf1 := pf1)
              (pf2 := pf2) (pf := pf) in H1.
            apply type_of_map with
              g (y1, y2) (Chan lin p2 t1) (Chan lin io t1)
              in pf as ABS2. inversion ABS2; subst...
            exists t2; eauto.
            split.
            all:eauto.
            apply type_plus_comm...
      * apply tsub_un with
          (g2 := g2) (g1 := g1) (pf1 := pf1)
          (pf2 := pf2) (pf := pf) in H1.
        apply type_of_map with
          g (y1, y2) (Chan un p2 t1) (Chan un p1 t1)
          in pf as ABS2. inversion ABS2; subst...
        all:eauto.
        exists t2; split. eauto.
        apply type_plus_comm...
      * eauto.
      * eauto.
      * eauto.
      * eauto.
    + inversion H...
    + eauto.
    + eauto.
    + eauto.
  - intros; inversion TYP; clear TYP; subst...
    apply tsub_payload with
      g1 g2 g pf1 pf2 pf x1 x2 f0 m q t
      in H4 as TYPx.
    destruct TYPx as [r TYP2x]; inversion TYP2x; subst.
    apply type_of_map with
      g (x1, x2) (Chan un pol t0) (Chan m r t)
      in pf as ASSERT. inversion ASSERT; subst.
    destruct t1.
    + apply tsuper_payload
        with (g1 := g1) (g2 := g2) (pf1 := pf1)
             (pf2 := pf2) (pf := pf) in H3
          as TYP1y.
      destruct TYP1y as [p1 TYP1y].
      inversion TYP1y; clear TYP1y; subst...
      exists (Chan m p1 t1).
      destruct m.
      clear H; assert (H := H0); clear H0.
      remember p0 as p2; subst p0.
      assert (K1 := H1); clear H1;assert (H1 := H6); clear H6.
      * destruct p1.
        ** exists t. split. eauto.
           inversion H; subst...
        ** apply tsub_in with
             (g2 := g2) (g1 := g1) (pf1 := pf1)
             (pf2 := pf2) (pf := pf)
             in H1 as M1.
           destruct M1 as [ABS | ABS].
           apply type_of_map with
             g (y1, y2) (Chan lin p2 t1) (Chan lin inp t1)
             in pf as ABS2. inversion ABS2; subst...
           exists t2; eauto.
           split.
           all:eauto.
           apply type_plus_comm...
           apply type_of_map with
             g (y1, y2) (Chan lin p2 t1) (Chan lin io t1)
             in pf as ABS2. inversion ABS2; subst...
           inversion H; inversion H6; subst...
           all:eauto.
           inversion H9...
        **  apply tsub_out with
              (g2 := g2) (g1 := g1) (pf1 := pf1)
              (pf2 := pf2) (pf := pf) in H1 as M1.
            destruct M1 as [ABS | ABS].
            apply type_of_map with
              g (y1, y2) (Chan lin p2 t1) (Chan lin out t1)
              in pf as ABS2. inversion ABS2; subst...
            exists t2; eauto.
            split.
            all:eauto.
            apply type_plus_comm...
            apply type_of_map with
              g (y1, y2) (Chan lin p2 t1) (Chan lin io t1)
              in pf as ABS2. inversion ABS2; subst...
            inversion H; inversion H6; subst...
            all:eauto.
            inversion H9...
        **  apply tsub_io with
              (g2 := g2) (g1 := g1) (pf1 := pf1)
              (pf2 := pf2) (pf := pf) in H1 as M1.
            apply type_of_map with
              g (y1, y2) (Chan lin p2 t1) (Chan lin io t1)
              in pf as ABS2. inversion ABS2; subst...
            exists t2; eauto.
            split.
            all:eauto.
            apply type_plus_comm...
      *
        clear H; assert (H := H0); clear H0.
        remember p0 as p2; subst p0.
        assert (K1 := H1); clear H1;assert (H1 := H6); clear H6.
        apply tsub_un with
          (g2 := g2) (g1 := g1) (pf1 := pf1)
          (pf2 := pf2) (pf := pf) in H1 as M1.
        apply type_of_map with
          g (y1, y2) (Chan un p2 t1) (Chan un p1 t1)
          in pf as ABS2. inversion ABS2; subst...
        all:eauto.
        exists t2; split. eauto.
        apply type_plus_comm...
      * eauto.
    + inversion H0...
    + eauto.
    + eauto.
    + eauto.
  - intros; inversion TYP; clear TYP; subst...
    apply tsub_payload with
      g1 g2 g pf1 pf2 pf x1 x2 f0 m q t
      in H4 as TYPx.
    destruct TYPx as [r TYP2x]; inversion TYP2x; subst.
    apply type_of_map with
      g (x1, x2) (Chan un pol t0) (Chan m r t)
      in pf as ASSERT. inversion ASSERT; subst.
    destruct t1.
    + apply tsuper_payload
        with (g1 := g1) (g2 := g2) (pf1 := pf1)
             (pf2 := pf2) (pf := pf) in H3
          as TYP1y.
      destruct TYP1y as [p1 TYP1y].
      inversion TYP1y; clear TYP1y; subst...
      exists (Chan m p1 t1).
      destruct m.
      clear H; assert (H := H0); clear H0.
      remember p0 as p2; subst p0.
      assert (K1 := H1); clear H1;assert (H1 := H6); clear H6.
      * destruct p1.
        ** exists t. split. eauto.
           inversion H; subst...
        ** apply tsub_in with
             (g2 := g2) (g1 := g1) (pf1 := pf1)
             (pf2 := pf2) (pf := pf)
             in H1 as M1.
           destruct M1 as [ABS | ABS].
           apply type_of_map with
             g (y1, y2) (Chan lin p2 t1) (Chan lin inp t1)
             in pf as ABS2. inversion ABS2; subst...
           exists t2; eauto.
           split.
           all:eauto.
           apply type_plus_comm...
           apply type_of_map with
             g (y1, y2) (Chan lin p2 t1) (Chan lin io t1)
             in pf as ABS2. inversion ABS2; subst...
           inversion H; inversion H6; subst...
           all:eauto.
           inversion H9...
        **  apply tsub_out with
              (g2 := g2) (g1 := g1) (pf1 := pf1)
              (pf2 := pf2) (pf := pf) in H1 as M1.
            destruct M1 as [ABS | ABS].
            apply type_of_map with
              g (y1, y2) (Chan lin p2 t1) (Chan lin out t1)
              in pf as ABS2. inversion ABS2; subst...
            exists t2; eauto.
            split.
            all:eauto.
            apply type_plus_comm...
            apply type_of_map with
              g (y1, y2) (Chan lin p2 t1) (Chan lin io t1)
              in pf as ABS2. inversion ABS2; subst...
            inversion H; inversion H6; subst...
            all:eauto.
            inversion H9...
        **  apply tsub_io with
              (g2 := g2) (g1 := g1) (pf1 := pf1)
              (pf2 := pf2) (pf := pf) in H1 as M1.
            apply type_of_map with
              g (y1, y2) (Chan lin p2 t1) (Chan lin io t1)
              in pf as ABS2. inversion ABS2; subst...
            exists t2; eauto.
            split.
            all:eauto.
            apply type_plus_comm...
      *
        clear H; assert (H := H0); clear H0.
        remember p0 as p2; subst p0.
        assert (K1 := H1); clear H1;assert (H1 := H6); clear H6.
        apply tsub_un with
          (g2 := g2) (g1 := g1) (pf1 := pf1)
          (pf2 := pf2) (pf := pf) in H1 as M1.
        apply type_of_map with
          g (y1, y2) (Chan un p2 t1) (Chan un p1 t1)
          in pf as ABS2. inversion ABS2; subst...
        all:eauto.
        exists t2; split. eauto.
        apply type_plus_comm...
      * eauto.
    + inversion H0...
    + eauto.
    + eauto.
    + eauto.
  -  intros.
     assert (IH : aIn x1 x2 y1 y2 = aIn x1 x2 y1 y2)...
     destruct H as (DIFF1 &DIFF2).
     assert (Inb: In (b1, b2, hid, t0) (h1 ++ (b1, b2, hid, t0) :: h2)).
     try eapply in_app_iff; try right...
     assert (TS2 := TSPLIT).
     eapply fsuper_hid 
       in TS2 as [[FYP1 FYP2] | [FYP1 FYP2]];
       try inverts FYP1 as IN1; try inverts  FYP2 as IN2;
       try eapply in_split in IN1 as (l1 &l2 &IN1);
       try eapply in_split in IN2 as (m1 &m2 &IN2)...
     subst.
     assert (pfl1 : isMap(l1 ++ (b1, b2, vis, t1) :: l2)).
     eapply no_dup_isMap;
       eapply no_dup_split_no_dup_l in TSPLIT;
     rewrite domain_distr in *; simpl in *...
     eapply IHLTS
       with (g1 :=  l1 ++ (b1, b2, vis, t1) :: l2)
            (g2 := (m1 ++ (b1, b2, vis, t2) :: m2))
       in IH as (ty &tt &TYP1 &TP1)...
     inverts TYP1 as IN1.
     repeat eexists; intuition...
     
     eapply in_app_iff in IN1 as [IN1 |CONT1]; try eapply in_app_iff; try inv CONT1 as [IN2 | CONT2];
       try inv IN2;
       try contradiction...
     repeat right...

     inverts TYP as IN1;      econstructor.

     eapply in_app_iff in IN1 as [IN1 |CONT1]; try eapply in_app_iff; try inv CONT1 as [IN2 | CONT2];
       try inv IN2;
       try contradiction...
     repeat right...

     subst.
      assert (pfl1 : isMap(l1 ++ (b1, b2, vis, t1) :: l2)).
     eapply no_dup_isMap;
       eapply no_dup_split_no_dup_l in TSPLIT;
       rewrite domain_distr in *; simpl in *...
     assert (pfm1 : isMap(m1 ++ (b1, b2, vis, t2) :: m2)).
     eapply no_dup_isMap;
       eapply no_dup_split_no_dup_r in TSPLIT;
       rewrite domain_distr in *; simpl in *...
     assert (pfh1:  isMap (h1 ++ (b1, b2, vis, t0) :: h2)).
      eapply no_dup_split_no_dup_l in TSPLIT;
       rewrite domain_distr in *; simpl in *...
     eapply IHLTS
       with (g1 :=  l1 ++ (b1, b2, vis, t1) :: l2)
            (g2 := (m1 ++ (b1, b2, vis, t2) :: m2))
       in IH as (ty &tt &TYP1 &TP1)...
     inverts TYP1 as IN1.
     repeat eexists; intuition...
     
     eapply in_app_iff in IN1 as [IN1 |CONT1]; try eapply in_app_iff; try inv CONT1 as [IN2 | CONT2];
       try inv IN2;
       try contradiction...
     repeat right...

     inverts TYP as IN1;      econstructor.

     eapply in_app_iff in IN1 as [IN1 |CONT1]; try eapply in_app_iff; try inv CONT1 as [IN2 | CONT2];
       try inv IN2;
       try contradiction...
     repeat right...

     eapply split_comm in TSPLIT;
       eapply split_comm...
     Unshelve.
     eapply no_dup_isMap; try assumption.
     eapply no_dup_isMap;
       eapply no_dup_split_no_dup_l in TSPLIT;
       rewrite domain_distr in *; simpl in *...
     eapply no_dup_isMap;
       eapply no_dup_split_no_dup_r in TSPLIT;
       rewrite domain_distr in *; simpl in *...
     assumption.
     assumption.
     assumption.
Qed.

Lemma lts_inp_obj_not_hid:
  forall g p a1 a2 b1 b2 g' p' nd_pf,
    lts g p (aIn a1 a2 b1 b2) g' p' nd_pf ->
    ~flagOf g (b1, b2) hid.
Proof with eauto.
  intros. intro ABS.  inversion ABS.
  dependent induction H. 
  specialize IHlts with a1 a2 b1 b2 g (b1, b2) hid t.
  intuition.
  inversion ABS. subst.
  assert (EQ: f = hid /\ t1 = t3).
  apply in_isMap with (x := (b1, b2)) (g := g)...
  intuition.
  assert (DISEQ: f<> hid)...
  assert (DISEQ: f<> hid)...
  destruct H0 as (DIFF1 &DIFF2).
  subst;eapply IHlts; try eapply in_app_iff in H1 as [HD|TL]; try econstructor;
    try eapply in_app_iff...
  inversion TL as [EQ | TL2];
    try inversion EQ; subst; try contradiction.
  repeat right...
  inversion TL as [EQ | TL2];
    try inversion EQ; subst; try contradiction.
  repeat right...
Qed. 

Hint Resolve in_eq.

Lemma split_eq_flag:
  forall g1 g2 g pf1 pf2 pf a1 a2 f1 t1 f t,
    tEnv_split g1 g2 g pf1 pf2 pf ->
    f <> hid ->
    In ((a1, a2), f, t) g->
    In ((a1, a2), f1, t1) g1->
    f = f1.
Proof with eauto.
  intros g1 g2 g pf1 pf2 pf a1 a2 f1 t1 f t
    TS DIFF IN IN1.
  apply fsuper_flag with g1 g2 g pf1 pf2 pf (a1, a2) t t1...
Qed.

Hint Resolve split_eq_flag.


Lemma finv_hid_r :
  forall g1 g2 g pf1 pf2 pf a1 a2 t,
    In (a1, a2, hid, t) g2 ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    flagOf g1 (a1, a2) ill.
Proof with eauto.
  intros g1 g2 g pf1 pf2 pf a1 a2 t IN TS.
  specialize fsub_hid_r with
    g1 g2 g pf1 pf2 pf a1 a2 t.
  intuition.
  inversion H; subst. 
  specialize fsuper_hid with
    g1 g2 g pf1 pf2 pf (a1, a2) t0.
  intuition. inversion H3. subst. 
  assert (hid = ill /\ t = t1).
  apply in_isMap with (x := (a1, a2)) (g := g2)...
  intuition.
  discriminate.
Qed.


Hint Resolve finv_hid_r.
Hint Resolve pairEq_eq.
Hint Resolve pairEq_neq.
(*Hint Resolve pair_equal_bool.*)

Lemma isMap_cons_2 : forall n f t g,
    isMap g -> In (n, f, t) g ->
    isMap ((n,f,t) ::  removeEntry n g).
Proof with eauto.
  intros n f t g pf IN.
  induction g. 
  - inversion IN.
  - inversion IN.
    subst. unfold removeEntry.
    destruct n. 
    specialize pairEq_eq_true with n n0 as PEQ.
    rewrite PEQ...
    assert (pf1 := pf).
    apply isMap_cons in pf. intuition.
    destruct a as [[a f1] t1].
    case_eq (pair_eq a n).
    + intros PEQ.
      unfold removeEntry; rewrite PEQ.
      unfold isMap; intros.
      destruct H0 as [IN1 IN2].
      apply in_app_iff with (l := (n, f, t) :: nil) in IN1.
      apply in_app_iff with (l := (n, f, t) :: nil) in IN2.
      destruct IN1 as [IN1 | IN1].
      destruct IN2 as [IN2 | IN2].
      inversion IN1. inversion IN2.
      inversion H0; inversion H2. subst...
      inversion H2. inversion H0.
      inversion IN1. inversion H0; subst.
      unfold isMap in pf. specialize pf with x f0 t0 f2 t2; intuition.
      inversion H0.
      destruct IN2 as [IN2 | IN2].
      inversion IN2; inversion H0; subst...
      unfold isMap in pf. specialize pf with x f0 t0 f2 t2; intuition.
    + intros PNEQ. apply pairEq_neq in PNEQ.
      assert (REMEQ:   removeEntry n ((a, f1, t1) :: g) =  (a, f1, t1) :: removeEntry n g). destruct n. destruct a as [a1 a2].
      specialize removeEntry_shift with n n0 a1 a2 f1 t1 g as REMS. intuition.
      rewrite REMEQ.
      unfold isMap; intros.
      destruct H0 as [IN1 IN2].
      apply in_app_iff with (l := (n, f, t) :: nil) in IN1.
      apply in_app_iff with (l := (n, f, t) :: nil) in IN2.
      destruct IN1 as [IN1 | IN1].
      * destruct IN2 as [IN2 | IN2].
        ** inversion IN1. inversion IN2.
           inversion H0; inversion H2. subst...
           inversion H2. inversion H0.
        ** inversion IN1. inversion H0; subst.
           apply in_app_iff with (l := (a, f1, t1) :: nil) in IN2.
           destruct IN2 as [IN2 | IN2].
           inversion IN2. inversion H2; subst. contradiction.
           inversion H2.
           unfold isMap in H1. 
           specialize H1 with x f0 t0 f2 t2. intuition.
           assert (In (x, f0, t0) ((x, f0, t0) :: removeEntry x g))...
           assert (In (x, f0, t0) ((x, f0, t0) :: removeEntry x g))...
           inversion H0.
      * destruct IN2 as [IN2 | IN2].
        ** inversion IN2. inversion H0; subst.
           apply in_app_iff with (l := (a, f1, t1) :: nil) in IN1.
           destruct IN1 as [IN1 | IN1].
           inversion IN1. inversion H2; subst; contradiction.
           inversion H2.
           
           unfold isMap in H1. 
           specialize H1 with x f0 t0 f2 t2. intuition.
           assert (In (x, f0, t0) ((x, f0, t0) :: removeEntry x g))...
           assert (In (x, f0, t0) ((x, f0, t0) :: removeEntry x g))...
           inversion H0.
        ** apply in_app_iff with (l := (a, f1, t1) :: nil) in IN1.
           destruct IN1 as [IN1 | IN1].
           *** inversion IN1. inversion H0; subst.
               apply in_app_iff with (l :=(x, f0, t0) :: nil) in IN2.
               destruct IN2 as [IN2 | IN2].
               **** inversion IN2. inversion H2... inversion H2.
               **** unfold isMap in pf1. 
                    specialize pf1 with x f0 t0 f2 t2. 
                    
                    assert (In (x, f0, t0) ((x, f0, t0) :: g)).
                    eauto.
                    assert (In (x, f2, t2) g).
                    apply in_removeEntry with (y := n)...
                    assert (In (x, f2, t2) ((x, f0, t0) :: g)).
                    apply in_cons...
                    intuition.
               **** inversion H0.
           ***  apply in_app_iff with (l :=(a, f1, t1) :: nil) in IN2.
                destruct IN2 as [IN2 | IN2].
                **** inversion IN2. inversion H0. subst.
                     unfold isMap in pf1. 
                     specialize pf1 with x f2 t2 f0 t0. 
                     
                     assert (In (x, f2, t2) ((x, f2, t2) :: g)).
                     eauto.
                     assert (In (x, f0, t0) g).
                     apply in_removeEntry with (y := n)...
                     assert (In (x, f0, t0) ((x, f2, t2) :: g)).
                     apply in_cons...
                     intuition.
                     inversion H0.
                **** apply isMap_cons in H1.
                     unfold isMap in H1. 
                     specialize H1 with x f0 t0 f2 t2; intuition.
Qed.

Hint Resolve isMap_cons_2.

Lemma split_cons: forall g1 g2 g pf1 pf2 pf b1 b2 f s pf',
    tEnv_split g1 g2 g pf1 pf2 pf ->
    In (b1, b2, f, s) g ->
    tEnv_split g1 g2 ((b1, b2, f, s) :: removeEntry (b1, b2) g)
      pf1 pf2 pf'.
Proof with eauto.
  intros g1 g2 g pf1 pf2 pf b1 b2 f s pf' TS IN.
  dependent induction TS. 
  - subst; inversion IN.
  - case_eq (pair_eq n (b1, b2)). intros PEQ. 
    rewrite <-pairEq_eq in PEQ; subst.
    inversion H4. subst.
    assert (f = f' /\ s = t0).
    apply in_isMap  with (x := (b1, b2)) (g := g3)...
    destruct H6; subst.
    inversion H5. subst.
    assert (f' = f /\ t0 = Chan lin p' t).
    apply in_isMap  with (x := (b1, b2)) (g := g3)...
    destruct H7; subst.
    apply SpLin with
      (n := (b1, b2)) (f := f0) (g :=g ) (f' := f)
      (p := p) (q := q) (p' := p') (t := t)
      (pf' := pf'0) (pf'' := pf'') (pf''' := pf''').
    eauto. eauto. eauto. eauto.
    eauto. eauto. eauto. eauto.
    intros PNEQ. assert (PEQ2 := PNEQ). 
    rewrite <-pairEq_neq in PNEQ.
    assert (IN2: In (b1, b2, f, s) (removeEntry n g3)).
    apply removeEntry_in...
    assert (pf'''' :  isMap ((b1, b2, f, s) :: removeEntry (b1, b2) g''')). rewrite <-H3.
    apply isMap_cons_2.
    apply isMap_removeEntry...
    eauto.
    apply SpLin with
      (n := n) (f := f0) (g :=g ) (f' := f')
      (p := p) (q := q) (p' := p') (t := t)
      (pf' := pf'0) (pf'' := pf'') (pf''' := pf'''').
    eauto. eauto. eauto. eauto.
    specialize IHTS with pf''''; subst; intuition.
    subst.
    assert (REMEQ:  removeEntry n ((b1, b2, f, s) :: removeEntry (b1, b2) g3) =  (b1, b2, f, s) :: removeEntry n (removeEntry (b1, b2) g3)). destruct n. 
    specialize removeEntry_shift with n n0 b1 b2 f s (removeEntry (b1, b2) g3) as REMS. intuition.
    rewrite REMEQ. rewrite removeEntry_swap...
    inversion H4; subst. apply F_Entry with (t := t0).
    apply in_app_iff with (l := (b1, b2, f, s) :: nil).
    right. apply removeEntry_in...
    inversion H5; subst. apply T_Entry with (f := f1).
    apply in_app_iff with (l := (b1, b2, f, s) :: nil).
    right. apply removeEntry_in...
  - case_eq (pair_eq n (b1, b2)). intros PEQ. 
    rewrite <-pairEq_eq in PEQ; subst.
    inversion H3. subst.
    assert (f = f' /\ s = t0).
    apply in_isMap  with (x := (b1, b2)) (g := g3)...
    destruct H5; subst.
    inversion H4. subst.
    assert (f' = f /\ t0 = Chan un p t).
    apply in_isMap  with (x := (b1, b2)) (g := g3)...
    destruct H6; subst.
    apply SpUn with
      (n := (b1, b2)) (f := f0) (g :=g ) (f' := f)
      (p := p) (t := t)
      (pf' := pf'0) (pf'' := pf'') (pf''' := pf''').
    eauto. eauto. eauto. eauto.
    eauto. eauto. eauto. eauto.
    intros PNEQ. assert (PEQ2 := PNEQ). 
    rewrite <-pairEq_neq in PNEQ.
    assert (IN2: In (b1, b2, f, s) (removeEntry n g3)).
    apply removeEntry_in...
    assert (pf'''' :  isMap ((b1, b2, f, s) :: removeEntry (b1, b2) g''')). rewrite <-H2.
    apply isMap_cons_2.
    apply isMap_removeEntry...
    eauto.
    apply SpUn with
      (n := n) (f := f0) (g :=g ) (f' := f')
      (p := p) (t := t)
      (pf' := pf'0) (pf'' := pf'') (pf''' := pf'''').
    eauto. eauto. eauto. 
    specialize IHTS with pf''''; subst; intuition.
    subst.
    assert (REMEQ:  removeEntry n ((b1, b2, f, s) :: removeEntry (b1, b2) g3) =  (b1, b2, f, s) :: removeEntry n (removeEntry (b1, b2) g3)). destruct n. 
    specialize removeEntry_shift with n n0 b1 b2 f s (removeEntry (b1, b2) g3) as REMS. intuition.
    rewrite REMEQ. rewrite removeEntry_swap...
    inversion H3; subst. apply F_Entry with (t := t0).
    apply in_app_iff with (l := (b1, b2, f, s) :: nil).
    right. apply removeEntry_in...
    inversion H4; subst. apply T_Entry with (f := f1).
    apply in_app_iff with (l := (b1, b2, f, s) :: nil).
    right. apply removeEntry_in...
  - case_eq (pair_eq n (b1, b2)). intros PEQ. 
    rewrite <-pairEq_eq in PEQ; subst.
    inversion H3. subst.
    assert (f = f' /\ s = t).
    apply in_isMap  with (x := (b1, b2)) (g := g3)...
    destruct H5; subst.
    inversion H4. subst.
    assert (f' = f /\ t = Top).
    apply in_isMap  with (x := (b1, b2)) (g := g3)...
    destruct H6; subst.
    apply SpTop with
      (n := (b1, b2)) (f := f0) (g :=g ) (f' := f)
      (pf' := pf'0) (pf'' := pf'') (pf''' := pf''').
    eauto. eauto. eauto. eauto.
    eauto. eauto. eauto. 
    intros PNEQ. assert (PEQ2 := PNEQ). 
    rewrite <-pairEq_neq in PNEQ.
    assert (IN2: In (b1, b2, f, s) (removeEntry n g3)).
    apply removeEntry_in...
    assert (pf'''' :  isMap ((b1, b2, f, s) :: removeEntry (b1, b2) g''')). rewrite <-H2.
    apply isMap_cons_2.
    apply isMap_removeEntry...
    eauto.
    apply SpTop with
      (n := n) (f := f0) (g :=g ) (f' := f')
      (pf' := pf'0) (pf'' := pf'') (pf''' := pf'''').
    eauto. eauto. eauto. 
    specialize IHTS with pf''''; subst; intuition.
    subst.
    assert (REMEQ:  removeEntry n ((b1, b2, f, s) :: removeEntry (b1, b2) g3) =  (b1, b2, f, s) :: removeEntry n (removeEntry (b1, b2) g3)). destruct n. 
    specialize removeEntry_shift with n n0 b1 b2 f s (removeEntry (b1, b2) g3) as REMS. intuition.
    rewrite REMEQ. rewrite removeEntry_swap...
    inversion H3; subst. apply F_Entry with (t := t).
    apply in_app_iff with (l := (b1, b2, f, s) :: nil).
    right. apply removeEntry_in...
    inversion H4; subst. apply T_Entry with (f := f1).
    apply in_app_iff with (l := (b1, b2, f, s) :: nil).
    right. apply removeEntry_in...
Qed.


Lemma remove_exists: forall b1 b2 s m q t g p  a1 a2 g' p' nd_pf,
    typeOf g (a1, a2) (Chan m q t) ->
    typeOf g (b1, b2) s ->
    lts g p (aOut a1 a2 b1 b2) g' p' nd_pf ->
    exists r,
      type_remove s t r.       
Proof with eauto.
  intros b1 b2 s m q t g p  a1 a2 g' p' nd_pf TYPa TYPb LTS.
  (*generalize dependent m.
  generalize dependent q.
  generalize dependent t.
  generalize dependent s.*)
  dependent induction LTS.
  - specialize IHLTS with b1 b2 a1 a2; intuition. 
  - inversion TYPa; inversion TYPb; subst. 
    assert (TEQ: vis = f /\ Chan lin out t0 = Chan m q t).
    apply in_isMap with (x := (a1, a2)) (g := g)...
    destruct TEQ as [FEQ TEQ]; inversion TEQ. subst. 
    assert (TEQ2: vis = f0 /\ t1 = s).
    apply in_isMap with (x := (b1, b2)) (g := g)...
    destruct TEQ2 as [FEQ TEQ2]; inversion TEQ2. subst.
    exists t2...
  - intros. inversion TYPa; inversion TYPb; subst. 
    assert (TEQ: vis = f /\ Chan un pol t0 = Chan m q t).
    apply in_isMap with (x := (a1, a2)) (g := g)...
    destruct TEQ as [FEQ TEQ]; inversion TEQ. subst. 
    assert (TEQ2: vis = f0 /\ t1 = s).
    apply in_isMap with (x := (b1, b2)) (g := g)...
    destruct TEQ2 as [FEQ TEQ2]; inversion TEQ2. subst.
    exists t2...
  - specialize IHLTS with b1 b2 a1 a2; intuition. 
    inversion TYPa; inversion TYPb; subst.
    assert (TEQ2: hid = f0 /\ t0 = s).
    apply in_isMap with (x := (b1, b2)) (g := g)...
    destruct TEQ2 as [FEQ TEQ2]; inversion TEQ2. subst.
    assert (In (a1, a2, f, Chan m q t) ( removeEntry (b1, b2) g)). apply removeEntry_in...
    assert  (In (a1, a2, f, Chan m q t) ((b1, b2, vis, s) ::removeEntry (b1, b2) g)). apply in_cons...
    apply T_Entry in H3 as IHH.
    apply IHLTS in IHH...

  -  destruct H as (DIFF1 &DIFF2).
     subst;eapply IHLTS...
     inversion TYPa; subst;
       try eapply in_app_iff in H as [HD|TL];
       try econstructor;
       try eapply in_app_iff...
     inversion TL as [EQ | TL2];
       try inversion EQ; subst; try contradiction.
     repeat right...
     inversion TYPb; subst;
       try eapply in_app_iff in H as [HD|TL];
       try econstructor;
       try eapply in_app_iff...
     inversion TL as [EQ | TL2];
       try inversion EQ; subst; try contradiction.
     repeat right...
Qed.


Lemma pol_plus_type_sub : forall p q p' t,
    pol_plus p q p' ->
    type_sub (Chan lin p t) (Chan lin p' t).
Proof with eauto.
  intros  p q p' t PP.
  destruct p.
  - apply Ts_empty...
  - inversion PP. subst. apply Ts_id.
    subst. apply Ts_inp.
  - inversion PP. subst. apply Ts_id.
    subst. apply Ts_out.
  - inversion PP. subst. apply Ts_id.
Qed.

Hint Resolve pol_plus_type_sub.

Lemma split_sub : forall g1 g2 g pf1 pf2 pf a t1 t,
    typeOf g1 a t1 ->
    typeOf g a t ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    type_sub t1 t.
Proof with eauto.
  intros g1 g2 g pf1 pf2 pf a t1 t TYP1 TYP TS.
  dependent induction TS.
  - subst; inversion TYP1; inversion H...
  - destruct a as [a1 a2]; destruct n as [n1 n2].
    case_eq (pair_eq (n1, n2) (a1, a2)). intros PEQ. 
    rewrite <-pairEq_eq in PEQ; inversion PEQ; subst.
    inversion TYP1 ; inversion TYP; inversion H5; subst.
    assert (f = f0 /\ Chan lin p t0 = t1).
    apply in_isMap with (x := (a1, a2)) (g := g1)...
    assert (f2 = f1 /\ Chan lin p' t0 = t).
    apply in_isMap with (x := (a1, a2)) (g := g3)...
    destruct H6; destruct H7; subst.
    eauto.
    intros PNEQ. assert (PNEQ2 := PNEQ).
    rewrite <-pairEq_neq in PNEQ.
    inversion TYP1; subst. 
    assert (IH: In  (a1, a2, f0, t1) (removeEntry  (n1, n2) g1)).
    apply removeEntry_in...
    apply T_Entry in IH; apply IHTS in IH.
    eauto. inversion TYP; subst. apply removeEntry_in with (y := (n1, n2)) in H3...
  -  destruct a as [a1 a2]; destruct n as [n1 n2].
     case_eq (pair_eq (n1, n2) (a1, a2)). intros PEQ. 
     rewrite <-pairEq_eq in PEQ; inversion PEQ; subst.
     inversion TYP1 ; inversion TYP; inversion H4; subst.
     assert (f = f0 /\ Chan un p t0 = t1).
     apply in_isMap with (x := (a1, a2)) (g := g1)...
     assert (f2 = f1 /\ Chan un p t0 = t).
     apply in_isMap with (x := (a1, a2)) (g := g3)...
     destruct H5; destruct H6; subst.
     apply Ts_id.
     intros PNEQ. assert (PNEQ2 := PNEQ).
     rewrite <-pairEq_neq in PNEQ.
     inversion TYP1; subst. 
     assert (IH: In  (a1, a2, f0, t1) (removeEntry  (n1, n2) g1)).
     apply removeEntry_in...
     apply T_Entry in IH; apply IHTS in IH.
     eauto. inversion TYP; subst. apply removeEntry_in with (y := (n1, n2)) in H2...
  -  destruct a as [a1 a2]; destruct n as [n1 n2].
     case_eq (pair_eq (n1, n2) (a1, a2)). intros PEQ. 
     rewrite <-pairEq_eq in PEQ; inversion PEQ; subst.
     inversion TYP1 ; inversion TYP; inversion H4; subst.
     assert (f = f0 /\ Top = t1).
     apply in_isMap with (x := (a1, a2)) (g := g1)...
     assert (f2 = f1 /\ Top = t).
     apply in_isMap with (x := (a1, a2)) (g := g3)...
     destruct H5; destruct H6; subst.
     apply Ts_id.
     intros PNEQ. assert (PNEQ2 := PNEQ).
     rewrite <-pairEq_neq in PNEQ.
     inversion TYP1; subst. 
     assert (IH: In  (a1, a2, f0, t1) (removeEntry  (n1, n2) g1)).
     apply removeEntry_in...
     apply T_Entry in IH; apply IHTS in IH.
     eauto. inversion TYP; subst. apply removeEntry_in with (y := (n1, n2)) in H2...
Qed.

Lemma type_plus_exists: forall s t s1 s4 s3 s', 
    type_remove s t s1 ->
    type_plus s4 s3 s' ->
    type_sub t s3 ->
    type_sub s' s ->
    exists r2,
      type_plus s4 r2 s1.
Proof with eauto.
  intros  s t s1 s4 s3 s' H TP TYP3 TYP1.
  destruct s'.
  - assert (S1 : exists q1, s1 = Chan m q1 s').
    assert (S3 : exists q3, s3 = Chan m q3 s').
    inversion TP; subst; eauto.
    destruct S3 as [q3 S3]; subst. 
    assert (ST : exists qt, t = Chan m qt s').
    inversion TYP3; subst; eauto.
    destruct ST as [qT ST]; subst.
    assert (SS : exists qs, s = Chan m qs s').
    inversion TYP1; subst; eauto.
    destruct SS as [qs SS]; subst.
    inversion H; subst. destruct H1 as [TP1 ISUN].
    inversion TP1; subst; eauto.
    
    destruct m.
    + destruct p.
      * inversion TP. inversion H3. subst.
        exists s1.
        destruct S1 as [q1' S1]; subst; apply Tp_LinPlus...
        exists s1.
        destruct S1 as [q1' S1]; subst; apply Tp_LinPlus...
      * inversion TYP1; subst.  
        inversion TP; subst. 
        inversion H3; subst.
        exists s1.
        destruct S1 as [q1' S1]; subst; apply Tp_LinPlus...
        inversion TYP3; subst.
        inversion H. destruct H1 as [TP1 ISUN]; inversion TP1; subst.
        exists (Chan lin empty s'). 
        apply Tp_LinPlus...
        inversion H5; subst...
        inversion H. destruct H1 as [TP1 ISUN]; inversion TP1; subst.
        exists (Chan lin empty s'). 
        apply Tp_LinPlus...
        inversion H5; subst...

        inversion TP; subst. 
        inversion H3; subst.
        exists s1.
        destruct S1 as [q1' S1]; subst; apply Tp_LinPlus...
        inversion TYP3; subst.
        inversion H. destruct H1 as [TP1 ISUN]; inversion TP1; subst.
        exists (Chan lin out s'). 
        apply Tp_LinPlus...
        inversion H5; subst...
        inversion H. destruct H1 as [TP1 ISUN]; inversion TP1; subst.
        exists (Chan lin out s'). 
        apply Tp_LinPlus...
        inversion H5; subst...
      * inversion TYP1; subst.  
        inversion TP; subst. 
        inversion H3; subst.
        exists s1.
        destruct S1 as [q1' S1]; subst; apply Tp_LinPlus...
        inversion TYP3; subst.
        inversion H. destruct H1 as [TP1 ISUN]; inversion TP1; subst.
        exists (Chan lin empty s'). 
        apply Tp_LinPlus...
        inversion H5; subst...
        inversion H. destruct H1 as [TP1 ISUN]; inversion TP1; subst.
        exists (Chan lin empty s'). 
        apply Tp_LinPlus...
        inversion H5; subst...

        inversion TP; subst. 
        inversion H3; subst.
        exists s1.
        destruct S1 as [q1' S1]; subst; apply Tp_LinPlus...
        inversion TYP3; subst.
        inversion H. destruct H1 as [TP1 ISUN]; inversion TP1; subst.
        exists (Chan lin inp s'). 
        apply Tp_LinPlus...
        inversion H5; subst...
        inversion H. destruct H1 as [TP1 ISUN]; inversion TP1; subst.
        exists (Chan lin inp s'). 
        apply Tp_LinPlus...
        inversion H5; subst...
      * inversion TYP1; subst.  
        inversion TP; subst. 
        inversion H3; subst.
        exists s1.
        destruct S1 as [q1' S1]; subst; apply Tp_LinPlus...
        inversion TYP3; subst.
        inversion H. destruct H1 as [TP1 ISUN]; inversion TP1; subst.
        exists (Chan lin empty s'). 
        apply Tp_LinPlus...
        inversion H5; subst...
        inversion H. destruct H1 as [TP1 ISUN]; inversion TP1; subst.
        exists (Chan lin empty s'). 
        apply Tp_LinPlus...
        inversion H5; subst...

        inversion TYP3; subst.
        inversion H. destruct H1 as [TP1 ISUN]; inversion TP1; subst.
        exists (Chan lin empty s'). 
        apply Tp_LinPlus...
        inversion H5; subst...
        
        inversion H. destruct H1 as [TP1 ISUN]; inversion TP1; subst.
        exists (Chan lin out s'). 
        apply Tp_LinPlus...
        inversion H5; subst...

        inversion TYP3; subst.
        inversion H. destruct H1 as [TP1 ISUN]; inversion TP1; subst.
        exists (Chan lin empty s'). 
        apply Tp_LinPlus...
        inversion H5; subst...
        
        inversion H. destruct H1 as [TP1 ISUN]; inversion TP1; subst.
        exists (Chan lin inp s'). 
        apply Tp_LinPlus...
        inversion H5; subst...
    + inversion H. clear H.
      destruct H1 as [TP1 ISUN].
      assert (K: is_unrestricted s).
      inversion TYP1; unfold is_unrestricted...
      apply ISUN in K; subst. clear ISUN.
      inversion TP1; subst.
      destruct S1 as [q1 S1]; inversion S1. 
      destruct S1 as [q1 S1]; inversion S1.
      rewrite H3.
      inversion TYP1. subst. 
      destruct p2.
      * exists (Chan un empty t0).
        assert (S4: s4 = Chan un empty t0).
        inversion TP; subst.
        assert (p0 = empty /\ p2 = empty).
        apply pol_cup_empty_res... destruct H; subst...
        subst. apply Tp_UnPlus...
      * inversion TP. subst. 
        exists (Chan un p2 t0)...
      * inversion TP. subst. 
        exists (Chan un p2 t0)...
      * inversion TP. subst. 
        exists (Chan un p2 t0)...
      * inversion TP. subst.
        assert (p0 = empty /\ p3 = empty).
        apply pol_cup_empty_res... destruct H; subst.
        exists (Chan un p2 t0).
        apply Tp_UnPlus...
      * inversion TP. subst.
        destruct p0.
        exists (Chan un io t0). apply Tp_UnPlus...
        exists (Chan un out t0). apply Tp_UnPlus...
        inversion H9.  destruct p3; inversion H1.
        inversion H9.
      * inversion TP. subst.
        destruct p0.
        exists (Chan un io t0). apply Tp_UnPlus...
        exists (Chan un out t0). apply Tp_UnPlus...
        exists (Chan un inp t0). apply Tp_UnPlus...
        exists (Chan un empty t0). apply Tp_UnPlus...
  -  inversion TP; inversion TYP1; inversion H.
     destruct H5 as [TP1 ABS]; subst. 
     inversion TP1; subst. 
     exists Top...
Qed.


Lemma split_lin_capab : forall g1 g2 g pf1 pf2 pf a1 a2 m1 m2
                               p t t1 t2,
    (typeOf g1 (a1, a2) (Chan m1 inp t1) \/ 
       typeOf g1 (a1, a2) (Chan m1 io t1)) ->
    (typeOf g2 (a1, a2) (Chan m2 out t2) \/ 
       typeOf g2 (a1, a2) (Chan m2 io t2)) ->
    In (a1, a2, vis, Chan lin p t) g->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    In (a1, a2, vis, Chan lin inp t) g1 /\
      In (a1, a2, vis, Chan lin out t) g2.
Proof with eauto.
  intros g1 g2 g pf1 pf2 pf a1 a2 m1 m2
    p t t1 t2 T1 T2 IN TS.
  apply tsuper_payload with
    (pf1 := pf1) (pf2 := pf2) (pf := pf) in IN
      as TYP1.
  apply tsuper_payload_r with
    (pf1 := pf1) (pf2 := pf2) (pf := pf) in IN
      as TYP2.
  specialize fsuper_vis with
    g1 g2 g pf1 pf2 pf (a1, a2) (Chan lin io t) as FSUP.
  apply FSUP in TS as FSUP2. destruct FSUP2 as [FS1 FS2]. clear FSUP.
  destruct TYP1 as [q1 TYP1]. destruct TYP2 as [q2 TYP2].
  inversion TYP1. inversion TYP2. inversion FS1. inversion FS2. subst.
  destruct T1 as [T1 | ABS1].
  destruct T2 as [T2 | ABS2].
  inversion T1; inversion T2; subst. 
  assert (vis = f1 /\ t4 = Chan m1 inp t1).
  apply in_isMap with (x := (a1, a2)) (g := g1)...
  assert (vis = f2 /\ t5 = Chan m2 out t2).
  apply in_isMap with (x := (a1, a2)) (g := g2)...
  destruct H1; destruct H2; subst. 
  assert (f = vis  /\  Chan lin q1 t = Chan m1 inp t1).
  apply in_isMap with (x := (a1, a2)) (g := g1)...
  assert (f0 = vis /\ Chan lin q2 t = Chan m2 out t2).
  apply in_isMap with (x := (a1, a2)) (g := g2)...
  destruct H1; destruct H2. inversion H4; inversion H6; subst... 
  specialize split_type_plus_r with
    g1 g2 g pf1 pf2 pf (a1, a2) (Chan m1 inp t1) (Chan m2 io t2) as ABS3.
  apply ABS3 in ABS2. clear ABS3.
  inversion T1. subst. 
  assert (f1 = f /\ Chan m1 inp t1 = Chan lin q1 t).
  apply in_isMap with (x := (a1, a2)) (g := g1)...
  destruct H1. inversion H2; subst.
  destruct ABS2 as [t3 [T ABS2]].
  inversion ABS2. inversion H10.
  eauto. eauto.

  specialize split_type_plus_r with
    g1 g2 g pf1 pf2 pf (a1, a2) (Chan m1 io t1) (Chan lin q2 t) as ABS3.
  apply ABS3 in ABS1. clear ABS3.
  destruct ABS1 as [t3 [T ABS1]].
  inversion ABS1. subst.
  inversion H8. subst.
  destruct T2 as [AABS1 | AABS2].
  inversion AABS1; subst.
  assert (f0 = f1 /\ Chan lin empty t = Chan m2 out t2).
  apply in_isMap with (x := (a1, a2)) (g := g2)...
  destruct H1. inversion H2; subst.
  inversion AABS2; subst.
  assert (f0 = f1 /\ Chan lin empty t = Chan m2 io t2).
  apply in_isMap with (x := (a1, a2)) (g := g2)...
  destruct H1. inversion H2; subst.
  eauto. eauto. clear FSUP.
  inversion T1. inversion H. subst.
  inversion T2. inversion H1. subst.
  apply tsub_in with (pf1 := pf1) (pf2 := pf2) (pf := pf)
    in H0 as K0.
  apply tsub_out_r with (pf1 := pf1) (pf2 := pf2) (pf := pf)
    in H2 as K2.
  inversion K0. inversion K2.
  inversion H3; inversion H4; subst. 
  assert (f1 = f2 /\ Chan m1 inp t1 =  Chan m2 out t2).
  apply in_isMap with (x := (a1, a2)) (g := g)...
  destruct H6. inversion H7.
  inversion H4; subst. 
  assert (vis = f1 /\ Chan lin p t =  Chan m2 io t2).
  apply in_isMap with (x := (a1, a2)) (g := g)...
  destruct H6. inversion H7; subst...
  inversion H3; subst. 
  assert (vis = f1 /\ Chan lin p t =  Chan m1 io t1).
  apply in_isMap with (x := (a1, a2)) (g := g)...
  destruct H5. inversion H6; subst...
  eauto. eauto.

  inversion H1; subst.
  apply tsub_io_r with (pf1 := pf1) (pf2 := pf2) (pf := pf)
    in H2 as K2.
  inversion K2. subst.  
  assert (vis = f1 /\ Chan lin p t =  Chan m2 io t2).
  apply in_isMap with (x := (a1, a2)) (g := g)...
  destruct H4. inversion H5; subst...
  eauto.

  inversion H; subst.
  apply tsub_io with (pf1 := pf1) (pf2 := pf2) (pf := pf)
    in H0 as K0.
  inversion K0. subst.  
  assert (vis = f0 /\ Chan lin p t =  Chan m1 io t1).
  apply in_isMap with (x := (a1, a2)) (g := g)...
  destruct H2. inversion H3; subst...
  all:eauto.
Qed.


