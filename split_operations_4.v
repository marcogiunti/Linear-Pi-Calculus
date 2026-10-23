Require Import
        Bool List Lia PeanoNat Program.Equality
        ListAddOns Max RemoveEntry Domain NewEntries
        header
        operations pi_syntax 
        pairEq type_system
        semantics  
        type_operations_1 
        split_exists_neutral
        sub_split
        no_dup_split_no_dup
        proposition27
        disjoint_newEntries
        Replication
        type_system_rules.

Require Import CpdtTactics LibTactics.

#[global] Hint Constructors cons.




Lemma neutral_is_cons: forall g neutral pf pfn pf1,
    tEnv_split g neutral g pf pfn pf1 ->
    cons neutral pfn.
Proof with eauto.
  introv TS;
    dependent induction TS...
  assert (EQ: Chan lin p t = Chan lin p' t).
  eapply type_of_map with (x := n) (g := g1)...
  inv EQ.
  assert (q = empty).
  destruct p', q; inv H0...
  subst; specialize IHTS with pf'''; intuition;
    eapply Co_lin...
Qed.

Lemma split_rewrite_pf_r: forall g1 g2 g pf1 pf2 pf pf2',
    tEnv_split g1 g2 g pf1 pf2 pf ->
    tEnv_split g1 g2 g pf1 pf2' pf.
Proof with eauto.
  intros g1 g2 g pf1 pf2 pf pf' TS. 
  dependent induction TS.
  - subst; apply SpNil...
  - assert (pfk :  isMap (removeEntry n g2)).
    apply isMap_removeEntry...
    eapply SpLin with (pf'' := pfk)... 
    all:eauto.
  -  assert (pfk :  isMap (removeEntry n g2)).
     apply isMap_removeEntry...
     eapply SpUn with (pf'' := pfk)... 
     all:eauto.
  - assert (pfk :  isMap (removeEntry n g2)).
    apply isMap_removeEntry...
    eapply SpTop with (pf'' := pfk)...
Qed.



Lemma  newEntries_nil : forall g h l n (pf: isMap h),
    (forall x, In x (domain g) <-> In x (domain h)) ->
    newEntries g l n  = nil ->
    newEntries h l n  = nil.
Proof with eauto.
  intros  g h l n pf DOM NIL.
  induction l. unfold newEntries...
  destruct a as [a1 a2].
  unfold newEntries; fold newEntries.
  unfold newEntries in NIL; fold newEntries in NIL.
  case_eq (InB (a1, a2) g). intros.
  case_eq b. intros. subst. 
  case_eq (InB (a1, a2) h). intros.
  case_eq b. intros. subst.
  rewrite H in NIL. intuition.
  intros. subst. 
  apply inB_implies_In in H.
  destruct H as [f [t H]].
  apply in_g_in_domain in H.
  specialize DOM with (a1, a2).
  assert (K: In (a1, a2) (domain h)). intuition.
  apply in_domain_in_g in K.
  destruct K as [f1 [t1 K]].
  eapply in_implies_InB in K. rewrite K in H0.
  inversion H0... assumption.
  intros. subst.
  rewrite H in NIL. destruct (InB (a1, a2 - n) g).
  inversion NIL.
Qed.


#[global] Hint Resolve incl_incl.

Lemma typeEnv_eq_change_flag a1 a2 f1 f2 t1 t2 f3 (h1 h2 k1 k2 : typeEnv):
  h1 ++ ((a1, a2, f1, t1) :: h2) =
  k1 ++ ((a1, a2, f2, t2) :: k2) ->
  ~In (a1, a2) (domain k1) ->
  ~In (a1, a2) (domain k2) ->
  f1 = f2 /\ t1 = t2 /\
  h1 ++ ((a1, a2, f3, t1) :: h2) =
  k1 ++ ((a1, a2, f3, t2) :: k2).
Proof with eauto.
  introv EQ NIN1 NIN2.
  assert (IN: In (a1, a2, f1, t1)
                 (k1 ++ (a1, a2, f2, t2) :: k2)).
  try rewrite <-EQ,in_app_iff; try right...
  try eapply in_app_iff in IN as [ABS | IN2];
    try eapply in_g_in_domain in ABS;
    try contradiction...
  inv IN2 as [EQ2 | ABS]; try inv EQ2.
  repeat split; try tauto.
  eapply app_eq_middle in EQ; intuition; subst;
    try eapply in_g_in_domain in H; try contradiction...
  eapply in_g_in_domain in ABS; try contradiction...
Qed.

Lemma typeEnv_eq_change_flag_removeEntry
      b1 b2 f r c1 c2 f1 f2 t1 t2  (h h1 h2 k1 k2 : typeEnv):
  (b1, b2) <> (c1, c2) ->
  NoDup (domain (h1 ++ (c1, c2, f2, t2) :: h2)) ->
  disjoint (domain h) (domain (h1 ++ (c1, c2, f2, t2) :: h2)) ->
  k1 ++ (c1, c2, f1, t1) :: k2 =
  h ++ (b1, b2, f, r) :: removeEntry (b1, b2) (h1 ++ (c1, c2, f1, t2) :: h2) ->
  k1 ++ (c1, c2, f2, t1) :: k2 =
  h ++ (b1, b2, f, r) :: removeEntry (b1, b2) (h1 ++ (c1, c2, f2, t2) :: h2).
Proof with eauto using app_comm_cons,
           typeEnv_eq_change_flag,
           in_g_in_domain.
  introv DIFF ND DIS EQ.
  case_eq (In2 (b1,b2) (domain ((h1 ++ (c1, c2, f1, t2) :: h2)))); intros IN;
    try rewrite in2_In_iff,domain_distr in IN;
    unfold domain in IN; fold domain in IN;
      try eapply in_app_iff in IN as [EQ2 | IN2].
  - erewrite removeEntry_app_shift2 in *...
    assert (EQ3:
              h ++ (b1, b2, f, r) :: removeEntry (b1, b2) h1 ++ (c1, c2, f1, t2) :: h2 =
              (h ++ (b1, b2, f, r) :: removeEntry (b1, b2) h1) ++ (c1, c2, f1, t2) :: h2)...
    erewrite app_comm_cons,app_assoc...
    erewrite EQ3 in *.
    eapply typeEnv_eq_change_flag
      with (f3 := f2) in EQ as (_&_&EQ);
      try erewrite app_comm_cons,app_assoc...
    erewrite domain_distr in *; intros ABS.
    eapply in_app_iff in ABS as [ABS1 | ABS2].
    eapply disjoint_absurd...
    simpl; try eapply in_app_iff; right...
    simpl in ABS2; inv ABS2 as [ABS3 | ABS4];
      try inv ABS2; try contradiction...
    eapply in_domain_in_g in ABS4 as (ff2&tt2&ABS4);
      eapply in_removeEntry in ABS4;
      eapply disjoint_absurd
        with (x := (c1, c2))
             (m:=domain ((c1, c2, f2, t2) :: h2));
      try eapply no_dup_disjoint...
    intros ABS;
      rewrite domain_distr in *;
      simpl in ND; 
      eapply NoDup_remove_2 with
          (l := domain h1)
          (l' := domain h2)
          (a := (c1, c2));
      try eapply in_app_iff...
  - inv IN2 as [ABS | IN3]; intuition...
    assert (NIN: ~In (b1, b2) (domain h1)).
    intros ABS.
    assert (Nd2:=ND);
    rewrite domain_distr,no_dup_iff
      in ND; destruct ND  as (_&_&DIS2).
     eapply disjoint_absurd
        with (x := (b1, b2))
             (m:=domain ((c1, c2, f2, t2) :: h2));
       try eapply no_dup_disjoint...
     erewrite <-domain_distr...
     simpl; right...
     erewrite removeEntry_app_shift in *...
     simpl in EQ.
     assert (DIFF2: (c1, c2)<>(b1,b2))...
     erewrite pairEq_neq in DIFF2;
       erewrite DIFF2 in *.
     assert (EQ3:
              h ++ (b1, b2, f, r) ::  h1 ++ (c1, c2, f1, t2) :: removeEntry (b1, b2)  h2 =
              (h ++ (b1, b2, f, r) :: h1) ++ (c1, c2, f1, t2) :: removeEntry (b1, b2)  h2)...
    erewrite app_comm_cons,app_assoc...
    erewrite EQ3 in *.
    eapply typeEnv_eq_change_flag
      with (f3 := f2) in EQ as (_&_&EQ);
      simpl; try rewrite DIFF2;
      try erewrite app_comm_cons,app_assoc...
    erewrite domain_distr in *; intros ABS.
    eapply in_app_iff in ABS as [ABS1 | ABS2].
    eapply disjoint_absurd...
    simpl; try eapply in_app_iff; right...
     simpl in ABS2; inv ABS2 as [ABS3 | ABS4];
      try inv ABS2; try contradiction...
     eapply in_domain_in_g in ABS4 as (ff2&tt2&ABS4);
      eapply disjoint_absurd
        with (x := (c1, c2))
             (m:=domain ((c1, c2, f2, t2) :: h2));
      try eapply no_dup_disjoint...
    intros ABS;
      rewrite domain_distr in *;
      simpl in ND; 
      eapply NoDup_remove_2 with
          (l := domain h1)
          (l' := domain h2)
          (a := (c1, c2));
      try eapply in_app_iff; try right...
    eapply in_domain_in_g in ABS as (ff2&tt2&ABS);
      eapply in_removeEntry in ABS...
  -   assert (NIN: ~In (b1, b2) (domain h1)).
      intros ABS.
      assert (In2 (b1, b2) (domain (h1 ++ (c1, c2, f1, t2) :: h2)) = true).
      rewrite domain_distr,in2_In_iff,in_app_iff...
      rewrite IN in *; try discriminate...  
      erewrite removeEntry_app_shift in *...
      assert (NIN2: ~In (b1, b2) (domain h2)).
      intros ABS.
      assert (In2 (b1, b2) (domain (h1 ++ (c1, c2, f1, t2) :: h2)) = true).
      rewrite domain_distr,in2_In_iff,in_app_iff;
        simpl...
      rewrite IN in *; try discriminate...
      simpl.
      assert (DIFF2: (c1, c2)<>(b1,b2))...
     erewrite pairEq_neq in DIFF2;
       unfold removeEntry in EQ;
       fold removeEntry in EQ;
       erewrite DIFF2,removeEntry_idempot in *...
       assert (EQ3:
              h ++ (b1, b2, f, r) ::  h1 ++ (c1, c2, f1, t2) ::  h2 =
              (h ++ (b1, b2, f, r) :: h1) ++ (c1, c2, f1, t2) ::h2)...
    erewrite app_comm_cons,app_assoc...
    erewrite EQ3 in *.
    eapply typeEnv_eq_change_flag
      with (f3 := f2) in EQ as (_&_&EQ);
      simpl; try rewrite DIFF2;
      try erewrite app_comm_cons,app_assoc...
     erewrite domain_distr in *; intros ABS.
    eapply in_app_iff in ABS as [ABS1 | ABS2].
    eapply disjoint_absurd...
    simpl; try eapply in_app_iff; right...
     simpl in ABS2; inv ABS2 as [ABS3 | ABS4];
      try inv ABS2; try contradiction...
     eapply in_domain_in_g in ABS4 as (ff2&tt2&ABS4);
      eapply disjoint_absurd
        with (x := (c1, c2))
             (m:=domain ((c1, c2, f2, t2) :: h2));
      try eapply no_dup_disjoint...
    intros ABS;
      rewrite domain_distr in *;
      simpl in ND; 
      eapply NoDup_remove_2 with
          (l := domain h1)
          (l' := domain h2)
          (a := (c1, c2));
      try eapply in_app_iff; try right...
Qed.
Lemma removeEntry_double g a1 a2 (nd_pf: NoDup (domain g)):
  removeEntry (a1, a2) (removeEntry (a1, a2) g) =
    removeEntry (a1, a2) g.
Proof with eauto.
  introv; induction g; simpl...
  destruct a as [[[b1 b2] ff]tt].
  assert (ND:=nd_pf); simpl in nd_pf; eapply no_dup_cont,IHg in nd_pf as IH;
    clear IHg.
  case_eq (pair_eq (b1,b2) (a1,a2)); introv PEQ;
    try rewrite PEQ;
    try rewrite <-pairEq_eq in PEQ; inv PEQ.
  eapply removeEntry_idempot; try intros ABS...
  simpl in ND; inversion ND...
  simpl; rewrite H0; erewrite IH...
Qed.

Lemma typeEnv_eq_change_flag_removeEntry_app
      a1 a2 f0 s b1 b2 f r c1 c2 f1 f2 t1 t2  (h1 h2 k1 k2 : typeEnv):
  (a1, a2) <> (c1, c2) ->
  (b1, b2) <> (c1, c2) ->
  (a1, a2) <> (b1, b2) ->
  NoDup (domain (h1 ++ (c1, c2, f2, t2) :: h2)) ->
  k1 ++ (c1, c2, f1, t1) :: k2 =
  (a1, a2, f0, s) :: (b1, b2, f, r) ::
    removeEntry (a1, a2) (removeEntry (b1, b2) (h1 ++ (c1, c2, f1, t2) :: h2)) ->
  k1 ++ (c1, c2, f2, t1) :: k2 =
  (a1, a2, f0, s) :: (b1, b2, f, r) ::
    removeEntry (a1, a2) (removeEntry (b1, b2) (h1 ++ (c1, c2, f2, t2) :: h2)).
Proof with eauto using app_comm_cons,
    typeEnv_eq_change_flag,
           in_g_in_domain.
  introv DIFF1 DIFF2 DIFF3 ND EQ.

  assert (NIN1: ~In (c1, c2) (domain h1)).
  intros ABS; rewrite domain_distr in ND; simpl in ND;
    eapply no_dup_iff in ND as (ND1 &ND2 &DIS);
    try eapply disjoint_absurd...
  assert (NIN2: ~In (c1, c2) (domain h2)).
  intros ABS; rewrite domain_distr in ND; simpl in ND;
    eapply no_dup_iff in ND as (ND1 &ND2 &_);
    try inv ND2...

  assert (K1:exists k', k1 = (a1, a2, f0, s)
       :: (b1, b2, f, r) :: k').
  destruct k1; try inv EQ; try contradiction.
  destruct k1; try inv H1; try contradiction...

  destruct K1 as [k' CONT]; subst; try inverts EQ as K.
  assert (EQ:  ((a1, a2, f0, s) :: (b1, b2, f, r) :: k') ++ (c1, c2, f2, t1) :: k2 =
                  ((a1, a2, f0, s) :: (b1, b2, f, r) :: (k' ++ (c1, c2, f2, t1) :: k2)))...
  rewrite EQ.
  assert (IH:  k' ++ (c1, c2, f2, t1) :: k2 =
                 removeEntry (a1, a2) (removeEntry (b1, b2) (h1 ++ (c1, c2, f2, t2) :: h2)) ->
                (a1, a2, f0, s) :: (b1, b2, f, r) :: k' ++ (c1, c2, f2, t1) :: k2 =
  (a1, a2, f0, s)
  :: (b1, b2, f, r)
     :: removeEntry (a1, a2) (removeEntry (b1, b2) (h1 ++ (c1, c2, f2, t2) :: h2))).
introv EQ2; rewrite EQ2...
eapply IH; clear EQ IH...

case_eq (In2 (b1,b2) (domain ((h1 ++ (c1, c2, f1, t2) :: h2)))); intros IN. 
case_eq (In2 (a1,a2) (domain (removeEntry (b1, b2) (h1 ++ (c1, c2, f1, t2) :: h2)))); intros INa. 
try rewrite in2_In_iff,domain_distr in IN;
  try rewrite in2_In_iff in INa;
    unfold domain in IN; fold domain in IN;
  try eapply in_app_iff in IN as [EQ2 | [ABS4 | IN2]];
  try inv ABS4; try contradiction...
eapply in_domain_in_g in INa as (ff &tt &INa);
  eapply in_removeEntry,in_app_iff in INa;
  destruct INa as [INa1 | [ABS1 | INa2]];
  try inv ABS1; try contradiction...

  * erewrite removeEntry_app_shift2,removeEntry_app_shift2 in *;
      try eapply in_domain_in_g...
    eapply typeEnv_eq_change_flag;
    try introv ABS...
    eapply in_domain_in_g in ABS as (ff2 &tt2 &ABS);
      eapply in_removeEntry, in_removeEntry,in_g_in_domain in ABS...
    
    all:eapply removeEntry_in,in_g_in_domain in INa1...

  *  erewrite removeEntry_app_shift2,removeEntry_app_shift in *;
     try introv ABS...
     simpl in *.
     assert (PNEQ: (c1,c2)<> (a1,a2))...
     erewrite pairEq_neq in PNEQ; try rewrite PNEQ in *...

      eapply typeEnv_eq_change_flag;
    try introv ABS...
    eapply in_domain_in_g in ABS as (ff2 &tt2 &ABS);
      eapply in_removeEntry, in_g_in_domain in ABS...

     eapply in_domain_in_g in ABS as (ff2 &tt2 &ABS);
      eapply in_removeEntry, in_g_in_domain in ABS...
    
     eapply in_domain_in_g in ABS as (ff1 &tt1 &ABS);
       eapply in_removeEntry, in_g_in_domain in ABS...
     eapply in_g_in_domain in INa2.
     rewrite domain_distr in ND; eapply no_dup_iff in ND as (ND1 &ND2 &DIS); try eapply disjoint_absurd...
     right...

      eapply in_domain_in_g in ABS as (ff1 &tt1 &ABS);
       eapply in_removeEntry, in_g_in_domain in ABS...
     eapply in_g_in_domain in INa2.
     rewrite domain_distr in ND; eapply no_dup_iff in ND as (ND1 &ND2 &DIS); try eapply disjoint_absurd...
     right...

  * eapply in_domain_in_g in INa as (ff &tt &INa);
  eapply in_removeEntry,in_app_iff in INa;
  destruct INa as [INa1 | [ABS1 | INa2]];
      try inv ABS1; try contradiction...

    erewrite removeEntry_app_shift,removeEntry_app_shift2 in *;
     try introv ABS...
     simpl in *.
     assert (PNEQ: (c1,c2)<> (b1,b2))...
     erewrite pairEq_neq in PNEQ; try rewrite PNEQ in *...

       eapply typeEnv_eq_change_flag;
    try introv ABS...
    eapply in_domain_in_g in ABS as (ff2 &tt2 &ABS);
      eapply in_removeEntry, in_g_in_domain in ABS...

     eapply in_domain_in_g in ABS as (ff2 &tt2 &ABS);
      eapply in_removeEntry, in_g_in_domain in ABS...
    
     rewrite domain_distr in ND; eapply no_dup_iff in ND as (ND1 &ND2 &DIS); try eapply disjoint_absurd...
     right...

      rewrite domain_distr in ND; eapply no_dup_iff in ND as (ND1 &ND2 &DIS); try eapply disjoint_absurd...
     right...

     erewrite removeEntry_app_shift,removeEntry_app_shift in *;
     try introv ABS...
     simpl in *.
     assert (PNEQ: (c1,c2)<> (b1,b2))...
     erewrite pairEq_neq in PNEQ; try rewrite PNEQ in *...
     assert (PNEQ2: (c1,c2)<> (a1,a2))...
     simpl in *; 
     erewrite pairEq_neq in PNEQ2; try rewrite PNEQ2 in *...
      

       eapply typeEnv_eq_change_flag;
    try introv ABS...
    eapply in_domain_in_g in ABS as (ff2 &tt2 &ABS);
      eapply in_removeEntry,in_removeEntry, in_g_in_domain in ABS...

     
    
     rewrite domain_distr in ND; eapply no_dup_iff in ND as (ND1 &ND2 &DIS); try eapply disjoint_absurd...
     right...

      rewrite domain_distr in ND; eapply no_dup_iff in ND as (ND1 &ND2 &DIS); try eapply disjoint_absurd...
      right...

       rewrite domain_distr in ND; eapply no_dup_iff in ND as (ND1 &ND2 &DIS); try eapply disjoint_absurd...
     right...
     

     rewrite domain_distr in ND; eapply no_dup_iff in ND as (ND1 &ND2 &DIS); try eapply disjoint_absurd...
     right...

  * eapply in2_nIn_iff in INa.
    eapply in2_In_iff in IN; rewrite domain_distr in IN; simpl in IN; eapply in_app_iff in IN as [IN | [ABS | CONT]];
      try inv ABS; try contradiction;
    try rewrite removeEntry_idempot with (b1:= a1)(b2:= a2) in *...
    rewrite removeEntry_app_shift2 in *; try introv ABS...
        eapply typeEnv_eq_change_flag;
    try introv ABS...
    eapply in_domain_in_g in ABS as (ff2 &tt2 &ABS);
      eapply in_removeEntry, in_g_in_domain in ABS...

    (* ~ In (a1, a2) (domain (removeEntry (b1, b2) (h1 ++ (c1, c2, f2, t2) :: h2)))*)
    introv ABS; eapply in_domain_in_g in ABS as (ff &tt&ABS);
      eapply in_removeEntry,in_g_in_domain in ABS;
      rewrite domain_distr in ABS;
      simpl in ABS; eapply in_app_iff in ABS
        as [ABS1 | [ABS2 | ABS3]]; try inv ABS2; try contradiction.
    assert (In (a1, a2) (domain (removeEntry (b1, b2) (h1 ++ (c1, c2, f1, t2) :: h2)))).
    eapply in_domain_in_g in ABS1 as (ff2 &tt2 &ABS1);
      eapply in_g_in_domain,removeEntry_in,in_app_iff...
    contradiction.
    assert (In (a1, a2) (domain (removeEntry (b1, b2) (h1 ++ (c1, c2, f1, t2) :: h2)))).
    eapply in_domain_in_g in ABS3 as (ff2 &tt2 &ABS1);
      eapply in_g_in_domain,removeEntry_in,in_app_iff...
    repeat right...
    contradiction.
    
    rewrite removeEntry_app_shift in *; try introv ABS...
    simpl in *.
     assert (PNEQ: (c1,c2)<> (b1,b2))...
     erewrite pairEq_neq in PNEQ; try rewrite PNEQ in *...
     
    
        eapply typeEnv_eq_change_flag;
    try introv ABS...
    eapply in_domain_in_g in ABS as (ff2 &tt2 &ABS);
      eapply in_removeEntry, in_g_in_domain in ABS...

     rewrite domain_distr in ND; eapply no_dup_iff in ND as (ND1 &ND2 &DIS); try eapply disjoint_absurd...
     right...

      rewrite domain_distr in ND; eapply no_dup_iff in ND as (ND1 &ND2 &DIS); try eapply disjoint_absurd...
      right...

       rewrite domain_distr in ND; eapply no_dup_iff in ND as (ND1 &ND2 &DIS); try eapply disjoint_absurd...
     right...

      (* ~ In (a1, a2) (domain (removeEntry (b1, b2) (h1 ++ (c1, c2, f2, t2) :: h2)))*)
      introv ABS; eapply in_domain_in_g in ABS as (ff &tt&ABS);
      eapply in_removeEntry,in_g_in_domain in ABS;
      rewrite domain_distr in ABS;
      simpl in ABS; eapply in_app_iff in ABS
        as [ABS1 | [ABS2 | ABS3]]; try inv ABS2; try contradiction.
    assert (In (a1, a2) (domain (removeEntry (b1, b2) (h1 ++ (c1, c2, f1, t2) :: h2)))).
    eapply in_domain_in_g in ABS1 as (ff2 &tt2 &ABS1);
      eapply in_g_in_domain,removeEntry_in,in_app_iff...
    contradiction.
    assert (In (a1, a2) (domain (removeEntry (b1, b2) (h1 ++ (c1, c2, f1, t2) :: h2)))).
    eapply in_domain_in_g in ABS3 as (ff2 &tt2 &ABS1);
      eapply in_g_in_domain,removeEntry_in,in_app_iff...
    repeat right...
    contradiction.

     *  eapply in2_nIn_iff in IN.
    try rewrite removeEntry_idempot with (b1:= b1)(b2:= b2) in *...
    case_eq (In2 (a1,a2) (domain (h1 ++ (c1, c2, f1, t2) :: h2))); intros INa. 
    eapply in2_In_iff in INa; rewrite domain_distr in INa; simpl in INa; try eapply in_app_iff in INa as
          [INa | [ABS | CONT]];
      try inv ABS; try contradiction...

     rewrite removeEntry_app_shift2 in *; try introv ABS...
        eapply typeEnv_eq_change_flag;
    try introv ABS...
    eapply in_domain_in_g in ABS as (ff2 &tt2 &ABS);
      eapply in_removeEntry, in_g_in_domain in ABS...

    rewrite removeEntry_app_shift in *; try introv ABS...
    simpl in *.
     assert (PNEQ: (c1,c2)<> (a1,a2))...
     erewrite pairEq_neq in PNEQ; try rewrite PNEQ in *...
     
    
        eapply typeEnv_eq_change_flag;
    try introv ABS...
    eapply in_domain_in_g in ABS as (ff2 &tt2 &ABS);
      eapply in_removeEntry, in_g_in_domain in ABS...

     rewrite domain_distr in ND; eapply no_dup_iff in ND as (ND1 &ND2 &DIS); try eapply disjoint_absurd...
     right...

      rewrite domain_distr in ND; eapply no_dup_iff in ND as (ND1 &ND2 &DIS); try eapply disjoint_absurd...
      right...

      try rewrite removeEntry_idempot with (b1:= a1)(b2:= a2) in *; try introv ABS...

      eapply typeEnv_eq_change_flag; try introv ABS...
      eapply in2_nIn_iff in INa...
      eapply in2_nIn_iff in INa;simpl in *; rewrite domain_distr in *...

      simpl in *; rewrite domain_distr in *...
      
Qed.


Lemma typeOf_hide_app h1 h2 c1 c2 f1 f2 t1 t2 a1 a2 t:
  (a1,a2) <> (c1, c2) ->
  typeOf (h1 ++ (c1, c2, f1, t1) :: h2) (a1, a2) t ->
  typeOf (h1 ++ (c1, c2, f2, t2) :: h2) (a1, a2) t.
Proof with eauto.
  introv DIFF TYP; try inverts TYP as IN;
    try eapply in_app_iff in IN as [IN1 | [ABS | IN2]];
    try econstructor; try eapply in_app_iff;
    try inv ABS; try contradiction...
  repeat right...
  Unshelve. all:eauto.
Qed.

Lemma disjoint_hide_app  k h1 h2 c1 c2 f1 f2 t1 t2 :
  disjoint (domain k) (domain (h1 ++ (c1, c2, f1, t1) :: h2)) ->
  disjoint (domain k) (domain (h1 ++ (c1, c2, f2, t2) :: h2)).
Proof with eauto.
  introv DIS; rewrite domain_distr in *; simpl in *...
Qed.

Lemma lts_un_input_action_replication: forall g p a1 a2 b1 b2 r g1 p1 nd_pf pol t k,
    lts g p (aIn a1 a2 b1 b2) g1 p1 nd_pf ->
    g1 = k ++ (b1, b2, vis, r) :: removeEntry (b1, b2) g ->
    k <> nil ->
    disjoint (domain k) (domain g)->
    typeOf g (a1, a2) (Chan un pol t) ->
    exists q,
      replication p p1 q /\
      incl (secLabs q) (secLabs p). 
Proof with eauto using
           incl_appl, typeOf_hide_app,
           disjoint_hide_app,
           typeEnv_eq_change_flag_removeEntry.
  introv LTS EQ DIFF DIS TYP.
  gen k r.
  dependent induction LTS.
  
  - intros; specialize IHLTS with a1 a2 b1 b2 k r. intuition.
    destruct H as [q' [INCL REPL]].
    exists q'. split. eapply replParL...
    unfold secLabs; fold secLabs.
    eapply incl_appr...
  - inversion TYP. subst.
    assert (Chan lin inp t0 = Chan un pol t).
    eapply in_isMap... inversion H4.
  - assert (TL: forall t2,
               (b1, b2, vis, t2) :: removeEntry (b1, b2) g =
               ((b1, b2, vis, t2) :: nil) ++ removeEntry (b1, b2) g). intuition.
    intros. erewrite TL in EQ.  erewrite TL with (t2 := r) in EQ.
    assert (EQ1: k ++ ((b1, b2, vis, r) :: nil) ++ removeEntry (b1, b2) g =  (k ++ ((b1, b2, vis, r) :: nil)) ++ removeEntry (b1, b2) g). intuition. rewrite EQ1 in EQ. clear EQ1.
    apply app_inv_tail with
        (l := removeEntry (b1, b2) g) in EQ.
    assert (ABS: List.length (k ++ (b1, b2, vis, r) :: nil) =
                 List.length k + List.length((b1, b2, vis, r) :: nil)).
    eapply List.app_length.
    unfold  List.length at 3 in ABS.
    rewrite <-EQ in ABS.
    rewrite <-app_nil_l with (l := (b1, b2, vis, t2) :: nil) in ABS. rewrite last_length with (l := nil) in ABS.
    unfold  List.length at 1 in ABS.
    assert (ABS2: Datatypes.length k = 0). lia.
    rewrite length_zero_iff_nil in ABS2; contradiction.
  - exists p. split. eapply replInp...
    unfold secLabs; fold secLabs...
  - Case hide. remember b0 as c1. remember b3 as c2. subst b0 b3.
    introv DIFF3 EQ1.
    
    destruct H as (DIFF1 &DIFF2).
    intros.
     assert (EQact: aIn a1 a2 b1 b2 = aIn a1 a2 b1 b2) by tauto.
     eapply IHLTS with (r := r) in EQact as (q &(REPL &INCL))...
     exists q; split; try econstructor...
Qed.

Lemma dep_relabel_rewrite_pf : forall p g pf (pf1 : NoDup (domain g)),
    dep_relabel p (domain g) pf =
    dep_relabel p (domain g) pf1.
Proof with eauto.
  intros. induction p.
  all:unfold dep_relabel; fold dep_relabel; eauto.
  rewrite IHp...
  rewrite IHp1; rewrite IHp2...
  rewrite IHp...
  rewrite IHp...
  rewrite IHp...
Qed.

#[global] Hint Rewrite newEntries_swap.



Lemma lts_un_input_action_newEntries_2: forall g p a1 a2 b1 b2 r g1 p1 nd_pf pf q k,
    lts g p (aIn a1 a2 b1 b2) g1 p1 nd_pf ->
    g1 = k ++ (b1, b2, vis, r) :: removeEntry (b1, b2) g ->
    sl_pos p ->
    NoDup (secLabs p) ->
    disjoint (domain k) (domain ((b1, b2, vis, r) :: removeEntry (b1, b2) g)) ->
    replication p p1 q ->
    k = newEntries g (secLabs (dep_relabel q (domain g) pf)) (max (domain g)).
Proof with eauto using
           typeEnv_eq_change_flag_removeEntry,
           in_iff_middle,
           no_dup_distr.
  introv LTS EQ SLP WF DIS REPL.
  eapply sl_pos_repl in SLP...
  generalize dependent q;
    dependent induction LTS. 
  - intros;inversion REPL. subst.
    simpl in WF; eapply  no_dup_distr in WF as (WF1&WF2);
    eapply IHLTS...
    assert (False); try eapply replication_diff;eauto; try contradiction.
  - intros; inversion REPL;assert (False); try eapply replication_diff;eauto; try contradiction.
  - intros; inversion REPL;assert (False); try eapply replication_diff;eauto; try contradiction.
  - intros. 
    assert (TL: forall t2,
               (b1, b2, vis, t2) :: removeEntry (b1, b2) g =
               ((b1, b2, vis, t2) :: nil) ++ removeEntry (b1, b2) g). intuition. erewrite TL in EQ.  erewrite TL with (t2 := r) in EQ.
    assert (EQ1 :
              newEntries g (secLabs q) (max (domain g)) ++
                         ((b1, b2, vis, t2) :: nil) ++ removeEntry (b1, b2) g =
              (newEntries g (secLabs q) (max (domain g)) ++
                          ((b1, b2, vis, t2) :: nil)) ++ removeEntry (b1, b2) g).
    intuition.
    assert  (EQ2: k ++ ((b1, b2, vis, r) :: nil) ++ removeEntry (b1, b2) g =
                  (k ++ ((b1, b2, vis, r) :: nil)) ++ removeEntry (b1, b2) g). intuition. 
    rewrite EQ1, EQ2 in EQ.
    apply app_inv_tail with
        (l := removeEntry (b1, b2) g) in EQ.
    clear TL EQ1 EQ2.
    eapply app_inj_tail in EQ. destruct EQ as [K1 K2]. subst...
    
    inversion REPL; subst...
    rewrite H11.
    erewrite <-dep_relabel_rewrite_pf with (pf := pf0)...
  - intros; inv REPL.
    simpl in WF.
    assert (IH : aIn a1 a2 b1 b2 = aIn a1 a2 b1 b2)...
    gen pf. 
    try rewrite domain_distr in *; simpl in *...
    intros.
    eapply IHLTS with (pf := pf) in IH...
    subst k.

    assert (nd_pf1 : NoDup((b0,b3)::domain h1 ++domain h2)).
    assert (pf' := pf).
    erewrite no_dup_iff in pf'; destruct pf' as (A&B&C);
      eapply NoDup_cons_iff in B as (B1 &B2);
      eapply disjoint_r_cons in C as (C1&C2).
    erewrite NoDup_cons_iff,no_dup_iff; split; try intros ABS;
      try eapply in_app_iff in ABS as [ABS|ABS];
      try inv ABS; try contradiction...
      
    erewrite newEntries_iff with
        (g2 := (b0, b3, vis, t) :: h1  ++ h2)...
    assert (EQ2: newEntries (h1 ++ (b0, b3, hid, t) :: h2) (secLabs (dep_relabel q (domain h1 ++ (b0, b3) :: domain h2) pf))
                           (max (domain h1 ++ (b0, b3) :: domain h2)) =
               newEntries ((b0, b3, hid, t) ::h1 ++  h2) (secLabs (dep_relabel q (domain h1 ++ (b0, b3) :: domain h2) pf))
                          (max (domain h1 ++ (b0, b3) :: domain h2))).
    erewrite newEntries_iff;
      simpl; try rewrite domain_distr...
    simpl; rewrite domain_distr...
    rewrite EQ2.

    eapply newEntries_swap with (p:=q)...
    repeat erewrite identif_seclabs_of_dep_relabel...
    
    assert (EQ3: max(domain h1 ++ (b0, b3) :: domain h2)=
                 max(domain ((b0, b3, vis, t) :: h1 ++ h2))).
    eapply max_same_domain; unfold domain; fold domain;
      rewrite domain_distr...
    unfold domain; fold domain;rewrite domain_distr...
    rewrite EQ3; repeat unfold domain; fold domain;rewrite domain_distr...
    unfold domain; fold domain;rewrite domain_distr...
     eapply max_same_domain; unfold domain; fold domain;
      try rewrite domain_distr...
     intros ABS.
     eapply secLabs_of_repl with (p :=p) in ABS...
     erewrite no_dup_iff in WF;
       destruct WF as (ND1 &ND2&DIS2);
       eapply disjoint_r_cons in DIS2; intuition...
     unfold domain; fold domain; rewrite domain_distr...
     eapply  typeEnv_eq_change_flag_removeEntry;
       try intros ABS; try inv ABS; intuition...

     eapply disjoint_r_cons in DIS as (DIS&NIN);
       eapply disjoint_removeEntry_eqd in DIS...
     simpl; try rewrite domain_distr...
     simpl; repeat rewrite domain_distr...
     eapply no_dup_distr in WF; intuition.

     eapply disjoint_r_cons in DIS as (DIS&NIN);
       eapply disjoint_cons_r; intuition.
     assert (DIS2: disjoint (domain k) (domain ( (h1 ++ (b0, b3, hid, t) :: h2)))).
    eapply disjoint_removeEntry_eqd in DIS...
    simpl; repeat rewrite domain_distr...
    eapply disjoint_eqd_removeEntry...
    simpl in*; repeat rewrite domain_distr in *...
    Unshelve.
    simpl; repeat rewrite domain_distr...
Qed.


Lemma lts_un_input_action_newEntries: forall g p a1 a2 b1 b2 r g1 p1 nd_pf pf pol t k,
    lts g p (aIn a1 a2 b1 b2) g1 p1 nd_pf ->
    g1 = k ++ (b1, b2, vis, r) :: removeEntry (b1, b2) g ->
    typeOf g (a1, a2) (Chan un pol t) ->
    disjoint (domain k) (domain((b1, b2, vis, r) :: removeEntry (b1, b2) g)) ->
    sl_pos p ->
    NoDup (secLabs p) ->
    k = nil \/
    exists q,
      replication p p1 q /\
      incl (secLabs q) (secLabs p) /\
      k = newEntries g (secLabs (dep_relabel q (domain g) pf)) (max (domain g)).
Proof with eauto using  lts_un_input_action_newEntries_2.
  introv LTS EQ TYP DIS SLP ND; destruct k; try destruct p0 as [[[c1 c2]f1]t1]...
  right.
  assert (REPL: exists q : dproc,
             replication p p1 q /\ incl (secLabs q) (secLabs p)). 
  eapply lts_un_input_action_replication...
  try discriminate...

  unfold domain in DIS at 2; fold domain in DIS.
  eapply disjoint_r_cons in DIS as [DIS  NIN].
  eapply disjoint_removeEntry_eqd...
  
  destruct REPL as [q' [REPL SL]]; eexists...
Qed.
