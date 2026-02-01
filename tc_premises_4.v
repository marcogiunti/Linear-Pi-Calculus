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
  split_operations_2.


Require Import CpdtTactics LibTactics.

Hint Constructors Permutation.



Lemma ne_illEC_var : forall x f t g k (pfk : NoDup (domain k))
                            l m,
    k = (x, f, t) :: g ->
    ~ In x l ->
    (forall z, In z l -> In (fst z, snd z - m) (domain g)) ->
    (forall y,
        In y
          (newEntries k l m ++ illECast k) <->
          In y (cast (x, f, t) :: newEntries g l m ++ illECast g)).
Proof with eauto.
  intros [x1 x2] f t g k pfk l m EQ NIN DOM [[[a1 a2] ff] tt].
  subst k.
  induction l.
  split; intros; simpl...
  assert (IH: ~ In (x1, x2) l ).
  intros ABS. assert (In (x1, x2) (a:: l)). right... contradiction.
  eapply IHl in IH; clear IHl.
  destruct a as [c1 c2].
  simpl.
  case_eq (pair_eq (c1, c2) (x1, x2)). intros ABS; rewrite <-pairEq_eq in ABS; inversion ABS; subst.
  assert (In (x1, x2) ((x1, x2) :: l))...
  contradiction.
  intros DIFF.
  destruct IH as (IH1 & IH2).
  case_eq (InB (c1, c2) g). intros. case_eq b; intros. simpl in *; intuition.
  case_eq (pair_eq (c1, c2 - m) (x1, x2)); intros EQ. rewrite <-pairEq_eq in EQ; inversion EQ;   simpl in *.
  specialize DOM with (c1, c2).
  assert (MIN2: (c1, c2) = (c1, c2) \/In (c1, c2) l)...
  eapply DOM in MIN2. simpl in MIN2. rewrite EQ in MIN2.
  inversion pfk. contradiction.

  destruct (InB (c1, c2 - m) g).
  split; intros.
  inversion H1. inversion H2; subst. right. eapply in_app_iff; left...
  eapply in_app_iff in H2 as [NE | CONT].
  assert (IHA : In (a1, a2, ff, tt)
                  (newEntries ((x1, x2, f, t) :: g) l m ++ illECast ((x1, x2, f, t) :: g))). eapply in_app_iff; left...
  eapply IH1 in IHA.
  inversion IHA. unfold cast in H2. left...
  repeat right...
  inversion CONT...
  repeat right. eapply in_app_iff; right...
  destruct H1 as [EQ2 | CONT]. inversion EQ2; subst; repeat right. eapply in_app_iff. right...
  inversion CONT. inversion H1; eapply in_app_iff; left...
  
  assert (IHB: In (a1, a2, ff, tt) (cast (x1, x2, f, t) :: newEntries g l m ++ illECast g)). right...
  eapply IH2 in IHB. simpl in IHB.
  erewrite in_app_iff  in IHB.  destruct IHB as [NE | CONT2].
  eapply in_app_iff; left; right...
  inversion CONT2. inversion H2; subst.
  eapply in_app_iff. right...
  eapply in_app_iff. repeat right...

  intros. specialize DOM with z; assert (In z (a :: l)). right... intuition.
Qed.


Lemma split_distr :
  forall g1 g2 g h1 h2 h pf1 pf2 pf pfh1 pfh2 pfh
         pfd1 pfd2 pfd
         (*nd_pf : NoDup (domain h ++ domain g)*)
  ,
    tEnv_split g1 g2 g pf1 pf2 pf->
    tEnv_split h1 h2 h pfh1 pfh2 pfh ->
    tEnv_split (g1 ++ h1) (g2 ++ h2) (g ++ h) pfd1 pfd2 pfd.
Proof with eauto using in_g_in_domain.
  introv (*nd_pf*) TS1 TS2.
  dependent induction TS1;
    subst; simpl.

  - eapply split_operations_2.split_rewrite_pf_gen...

  - assert (prf1: isMap (removeEntry n (g1 ++ h1))).
    eapply isMap_removeEntry... 
    assert (prf2: isMap (removeEntry n (g2 ++ h2))).
    eapply isMap_removeEntry... 
    assert (prf3: isMap (removeEntry n (g3 ++ h))).
    eapply isMap_removeEntry... 
    try eapply SpLin with (pf' := prf1)
                          (pf'' := prf2) (pf''' := prf3); try eassumption;
      try eapply in_app_iff; try tauto.
    left...
    left...
    gen prf1 prf2 prf3.
    destruct n; repeat erewrite removeEntry_app_shift2; intros.
    eapply IHTS1...
    (*    eapply no_dup_iff;
      eapply no_dup_iff in nd_pf as (ND1 &ND2 &DIS);
      repeat split;
      try assumption;
      try eapply no_dup_removeEntry_no_dup;
    try eapply disjoint_eqd_removeEntry...
     *)
    inv H4; try eapply in_g_in_domain...
    try eapply in_g_in_domain...
    try eapply in_g_in_domain...

    inv H4; econstructor; try eapply in_app_iff;  try left...
    inv H5; econstructor; try eapply in_app_iff;  try left...

  - assert (prf1: isMap (removeEntry n (g1 ++ h1))).
    eapply isMap_removeEntry... 
    assert (prf2: isMap (removeEntry n (g2 ++ h2))).
    eapply isMap_removeEntry... 
    assert (prf3: isMap (removeEntry n (g3 ++ h))).
    eapply isMap_removeEntry... 
    try eapply SpUn with (pf' := prf1)
                         (pf'' := prf2) (pf''' := prf3); try eassumption;
      try eapply in_app_iff; try tauto.
    left...
    left...
    gen prf1 prf2 prf3.
    destruct n; repeat erewrite removeEntry_app_shift2; intros.
    eapply IHTS1...
    (*    eapply no_dup_iff;
      eapply no_dup_iff in nd_pf as (ND1 &ND2 &DIS);
      repeat split;
      try assumption;
      try eapply no_dup_removeEntry_no_dup;
    try eapply disjoint_eqd_removeEntry...
     *)
    inv H4; try eapply in_g_in_domain...
    try eapply in_g_in_domain...
    try eapply in_g_in_domain...
    inv H3; econstructor; try eapply in_app_iff;  try left...
    inv H4; econstructor; try eapply in_app_iff;  try left...

  - assert (prf1: isMap (removeEntry n (g1 ++ h1))).
    eapply isMap_removeEntry... 
    assert (prf2: isMap (removeEntry n (g2 ++ h2))).
    eapply isMap_removeEntry... 
    assert (prf3: isMap (removeEntry n (g3 ++ h))).
    eapply isMap_removeEntry... 
    try eapply SpTop with (pf' := prf1)
                          (pf'' := prf2) (pf''' := prf3); try eassumption;
      try eapply in_app_iff; try tauto.
    gen prf1 prf2 prf3.
    destruct n; repeat erewrite removeEntry_app_shift2; intros.
    eapply IHTS1...
    (* eapply no_dup_iff;
      eapply no_dup_iff in nd_pf as (ND1 &ND2 &DIS);
      repeat split;
      try assumption;
      try eapply no_dup_removeEntry_no_dup;
    try eapply disjoint_eqd_removeEntry...
     *)
    inv H4; try eapply in_g_in_domain...
    try eapply in_g_in_domain...
    try eapply in_g_in_domain...
    inv H3; econstructor; try eapply in_app_iff;  try left...
    inv H4; econstructor; try eapply in_app_iff;  try left...
Qed.

Lemma split_gcons g1 g2 g pf1 pf2 pf k pfk :
  tEnv_split g1 g2 g pf1 pf2 pf ->
  NoDup (domain k ++ domain g) ->
  cons k pfk ->
  exists k1 k2 pfk1 pfk2 pf' pf'' pf''',
    cons k1 pfk1 /\
      cons k2 pfk2 /\
      tEnv_split (k1++g1) (k2++g2) (k++g) pf' pf'' pf'''.
Proof with eauto using split_distr,neutral_is_cons.
  introv TS ND CONS.
  assert (nd_pfk : NoDup (domain k)).
  eapply no_dup_iff in ND; intuition.
  eapply split_exists_neutral
    in nd_pfk
      as (k1 &pfk1 &nd_pfk &TS1).
  exists k k1.
  repeat eexists; try eassumption.
  eapply neutral_is_cons...
  eapply split_distr...
  (*  eapply no_dup_iff in ND;  eapply no_dup_iff; intuition.
  eapply disjoint_commute...
   *)
  Unshelve.
  eapply no_dup_isMap; rewrite domain_distr in *; eapply no_dup_iff;
    eapply no_dup_iff in ND; intuition;
    try eapply no_dup_split_no_dup_l;
    try eapply disjoint_commute;
    try eapply disjoint_iff;
    try eapply disjoint_commute...

  eapply no_dup_isMap; rewrite domain_distr in *; eapply no_dup_iff;
    eapply no_dup_iff in ND; intuition.
  try eapply no_dup_split_no_dup_r...
  eapply  disjoint_iff with (l1 := domain k)...
  eapply disjoint_commute, disjoint_iff with (l1 := domain g);
    try eapply disjoint_commute...
  intros; eapply split_domain_r with (x := x)in TS; try rewrite TS; try tauto...
  intros; eapply split_domain_r with (x := x)in TS1; try rewrite TS1; try tauto...

  eapply no_dup_isMap; rewrite domain_distr in *; eapply no_dup_iff;
    eapply no_dup_iff in ND; intuition;
    try eapply no_dup_split_no_dup_l;
    try eapply disjoint_commute;
    try eapply disjoint_iff;
    try eapply disjoint_commute...

  assumption.
Qed.

Lemma min_max: forall l,
    (forall x1 x2, In (x1, x2) l -> x2 <= max l).
Proof with eauto.
  intros; dependent induction l; simpl;
    try inversion H;
    try destruct a as [a1 a2];
    try inversion H0; subst;
    case_eq ( x2 <? max l); intros;
    try rewrite Nat.ltb_lt in *; try omega;
    try eapply IHl in H0;
    case_eq ( a2 <? max l); intros;
    try rewrite Nat.ltb_nlt in *;try omega...
Qed.

Lemma max_distr: forall x l1 l2,
    x < max l2 -> x < max (l1 ++ l2).
Proof with eauto.
  intros. rewrite max_app.
  case_eq (max l1 <? max l2 ); intros...
  erewrite Nat.ltb_ge in H0; omega.
Qed.

Lemma rewrite_max_var : forall x v t g,
    snd x < max (domain g) ->
    max (domain g) = max (domain ((x, v, t) :: g)).
Proof with omega.
  introv LT; induction g; destruct x as [x1 x2];
    simpl in *; intuition;
    try destruct a as [[[a1 a2]f1]t1].
  try rewrite <-Nat.ltb_lt in *;
    try rewrite LT...
Qed.


Lemma proj_isMap: forall f g (pf : isMap g),
    f= vis_proj \/ f = ill_proj ->
    isMap (f g).
Proof with eauto using in_map.
  introv pf [EQ | EQ]; subst; econstructor; intuition;
    try eapply proj_in in H0;
    try eapply proj_in in H1;
    try eapply isMap...
Qed.

Hint Resolve proj_isMap.


Lemma proj_cons : forall f g pf pf1,
    cons g pf ->
    f= vis_proj \/ f = ill_proj ->
    cons (f g) pf1.
Proof with eauto using cons2_rewrite_pf, proj_isMap.
  introv CONS [EQ |EQ]; subst; induction g; simpl.
  - econstructor...
  -  
    try destruct a as [[[a1 a2] f] t], f, t;
      eapply gcons_cons in CONS as K;
      try destruct f; simpl in pf1;
      try eapply isMap_cons in pf1;
      try destruct m; try eapply IHg.
    try eapply cons2_rewrite_pf...
    try eapply cons2_rewrite_pf...
    try eapply cons2_rewrite_pf...
    try eapply cons2_rewrite_pf...
    try eapply cons2_rewrite_pf...
    try eapply cons2_rewrite_pf...
    assert (p = empty).
    eapply cons_lin with (a1 := a1) (pf := pf);
      try eapply
        cons2_rewrite_pf...
    assert (pf2 : isMap (removeEntry (a1, a2) ((a1, a2, vis, Chan lin p t) :: vis_proj g))).
    eapply isMap_removeEntry...
    subst p; eapply Co_lin with (pf' := pf2).
    simpl...
    revert dependent pf2; simpl; try rewrite pairEq_eq_true...

    assert (pf2 : isMap (removeEntry (a1, a2) ((a1, a2, vis, Chan un p t) :: vis_proj g))).
    eapply isMap_removeEntry...
    eapply Co_un with (pf' := pf2).
    simpl...
    revert dependent pf2; simpl; try rewrite pairEq_eq_true...

    assert (pf2 : isMap (removeEntry (a1, a2) ((a1, a2, vis, Top) :: vis_proj g))).
    eapply isMap_removeEntry...
    eapply Co_top with (pf' := pf2).
    simpl...
    revert dependent pf2; simpl; try rewrite pairEq_eq_true...
  - econstructor...
  - try destruct a as [[[a1 a2] f] t], f, t;
      eapply gcons_cons in CONS as K;
      try destruct f; simpl in pf1;
      try eapply isMap_cons in pf1;
      try destruct m; try eapply IHg.
    try eapply cons2_rewrite_pf...
    try eapply cons2_rewrite_pf...
    try eapply cons2_rewrite_pf...
    assert (p = empty).
    eapply cons_lin with (a1 := a1) (pf := pf);
      try eapply
        cons2_rewrite_pf...
    assert (pf2 : isMap (removeEntry (a1, a2) ((a1, a2, ill, Chan lin p t) :: ill_proj g))).
    eapply isMap_removeEntry...
    subst p; eapply Co_lin with (pf' := pf2).
    simpl...
    revert dependent pf2; simpl; try rewrite pairEq_eq_true...

    assert (pf2 : isMap (removeEntry (a1, a2) ((a1, a2, ill, Chan un p t) :: ill_proj g))).
    eapply isMap_removeEntry...
    eapply Co_un with (pf' := pf2).
    simpl...
    revert dependent pf2; simpl; try rewrite pairEq_eq_true...

    assert (pf2 : isMap (removeEntry (a1, a2) ((a1, a2, ill, Top) :: ill_proj g))).
    eapply isMap_removeEntry...
    eapply Co_top with (pf' := pf2).
    simpl...
    revert dependent pf2; simpl; try rewrite pairEq_eq_true...
    all:eauto.
    
    Unshelve.
    all:
      match goal with
      | [ _ : _ |- isMap (vis_proj _) ] =>
          eapply isMap_cons in pf as W; eapply proj_isMap; eauto
      | [ _ : _ |- isMap (ill_proj _) ] =>
          eapply isMap_cons in pf as W; eapply proj_isMap; eauto
      | [ _ : _ |- _ ] => eapply isMap_cons in pf as W; trivial
      end.
Qed.


Lemma disjoint_projections  (g : typeEnv):
  NoDup (domain g)->
  disjoint (domain (vis_proj g)) (domain (ill_proj g)).
Proof with eauto.
  intros pf; induction g; try econstructor;
    try destruct a as [[[a1 a2] f] t];
    try destruct f; simpl;
    try eapply disjoint_cons_r;
    intuition...
  all: simpl in pf; inv pf;
    try eapply in_domain_in_g in H as (ff &tt &IN);
    eapply proj_in,in_g_in_domain in IN;
    try contradiction...
Qed.

Hint Resolve in_removeEntry_cons_iff
  in_removeEntry_cons_iff_2.

Hint Constructors NoDup.
Hint Resolve in_hid_proj.
Hint Resolve isMap_not_in incl_cons inB_implies_In_2.

 Lemma max_distr_2: forall x l1 l2,
                 x < max l1 -> x < max (l1 ++ l2).
Proof with
eauto.
   intros. rewrite max_app.
   case_eq (max l1 <? max l2 ); intros...
   erewrite Nat.ltb_lt in H0; omega.
Qed.

Hint Resolve in_g_in_domain.

Lemma typeCheck_weak2: forall g pf p k pfk pf1 (nd_pf : NoDup (domain g ++ domain k)),
    typeCheck g pf p ->
    cons k pfk ->
    disjoint (bv p) (domain k) ->
    typeCheck (g ++ k) pf1 p.
Proof with eauto.
  intros  g pf p k pfk pf1 nd_pf TC CONS BVDIS.
  generalize dependent k.
  dependent induction TC.
  - intros. eapply TNil,cons_distr...
  - intros.
    assert (removeEntry n (g ++ k) = removeEntry n g ++ k).
    apply in_g_in_domain in H.
    apply no_dup_iff in nd_pf as K.
    destruct K as [nd_pf1 [nd_pf2 DIS]].
    (*  removeEntry n (g ++ k) = removeEntry n g ++ k *)
    destruct n; eapply removeEntry_app_shift2...
    assert (nd_pf1: NoDup (domain (((n, vis, t) :: removeEntry n (g ++ k))))).
    apply no_dup_cons_removeEntry.
    rewrite domain_distr...
    apply no_dup_isMap in nd_pf1 as pf1'.
    rewrite H0 in pf1'.
    apply no_dup_isMap in nd_pf1 as pf'.
    eapply TNew with (t := t) (pf1 := pf'). apply in_app_iff; left...
    specialize IHTC with (pfk := pfk) (pf1 := pf1').
    assert (NoDup (domain ((n, vis, t) :: removeEntry n g) ++ domain k)).
    rewrite <-domain_distr. rewrite H0 in nd_pf1.
    intuition. intuition.
    revert dependent pf'.
    rewrite H0; intros...
  - intros.
    assert (EX: exists (neutral : typeEnv) (pfn : isMap neutral) (_ : NoDup (domain neutral)),
         tEnv_split k neutral k pfk pfn pfk).
    eapply split_exists_neutral,no_dup_distr...
    destruct EX as (neutral &pfn &_ &TSN).
    assert (ND := nd_pf).
    eapply no_dup_distr in ND as (ND1 &ND2).
    assert (DIS := nd_pf).
    eapply no_dup_disjoint in DIS.
     assert (ND3: NoDup (domain (g1 ++ k))).
    erewrite domain_distr. eapply no_dup_iff.
    split. eapply no_dup_split_no_dup_l with (pf := pf)...
    split...
    case_eq g1; intros...
    eapply disjoint_iff...
    rewrite <-H0. intros. assert (In x (domain g1) <-> In x (domain g)). eapply split_domain_l... intuition.
    assert (ND4: NoDup (domain (g2 ++  neutral))).
    erewrite domain_distr.
    eapply no_dup_iff.
    split. eapply no_dup_split_no_dup_r with (pf := pf)...
    split. eapply no_dup_split_no_dup_r with (pf := pfk)...
    eapply disjoint_commute in DIS.
    eapply disjoint_commute.
    assert (disjoint (domain k) (domain g2)).
    eapply disjoint_iff...
    eapply disjoint_commute in DIS.
    eapply disjoint_commute.
    eapply disjoint_iff...
    intros.
    assert (In x (domain g2) <-> In x (domain g)).
    eapply split_domain_r... intuition.
     eapply disjoint_iff...
    intros.
    assert (In x (domain neutral) <-> In x (domain k)).
    eapply split_domain_r... intuition.
    eapply TPar.
    eapply split_distr...
   
    eapply IHTC1...
    erewrite <-domain_distr...
    eapply IHTC2.
     erewrite <-domain_distr...
     eapply split_operations_4.neutral_is_cons...
     simpl in *. eapply disjoint_app_r in BVDIS.
     eapply disjoint_commute; eapply disjoint_commute in BVDIS.
     eapply disjoint_iff with (l1 := domain k)...
     intros; eapply split_domain_m...
     
    Unshelve. all: eapply no_dup_isMap; eauto.
  - Case TOutL.
    intros.
     assert (ND := nd_pf).
     eapply no_dup_distr in ND as (ND1 &ND2).
     eapply no_dup_isMap in ND1 as pff1.
    assert (TOUTL: typeCheck
        g pf (dOut (fst u) (snd u) (fst v) (snd v) q)).
    eauto. 
     eapply typeCheck_object_neq_subject in TOUTL;
      simpl in TOUTL.
     assert (DIFF: u <> v). destruct u, v; intuition.
    assert (DIS := nd_pf).
    eapply no_dup_disjoint in DIS.
    assert (nd_pftc: NoDup (domain (((u, vis, t1) :: (v, vis, t2) :: removeEntry v (removeEntry u (g ++ k)))))).
   
    erewrite removeEntry_swap.
    eapply no_dup_cons_removeEntry_app.
    erewrite domain_distr...
    all: intuition.
     eapply no_dup_isMap in nd_pftc as pftc.
    econstructor...
    all: try eapply in_app_iff; try left...
    instantiate (1 := pftc).
    destruct u, v. revert dependent pftc. erewrite removeEntry_app_shift2. intros.
    
    assert (nd_pff: NoDup
   (domain
      ((n, n0, vis, t1) :: (n1, n2, vis, t2) :: removeEntry (n1, n2) (removeEntry (n, n0) g)) ++
      domain k)).
    eapply no_dup_iff; intuition.
    erewrite removeEntry_swap.
    eapply no_dup_cons_removeEntry_app...
    eauto.
    eapply disjoint_iff with (l1 := domain g)...
    intros. erewrite removeEntry_swap. eapply in_removeEntry_cons_iff_2; eauto; eapply in_g_in_domain; eauto. intuition.
    assert (nd_pfIH: NoDup (domain ((((n, n0, vis, t1)
                                        :: (n1, n2, vis, t2) :: removeEntry (n1, n2) (removeEntry (n, n0) g)) ++ k)))).
    erewrite domain_distr...
    eapply no_dup_isMap in nd_pfIH as pfIH.
    eapply IHTC   with (pf1 := pfIH) in CONS;
    move CONS at bottom.
    assert (EQ: (((n, n0, vis, t1)
             :: (n1, n2, vis, t2) :: removeEntry (n1, n2) (removeEntry (n, n0) g)) ++ k)   =
    ((n, n0, vis, t1)
       :: (n1, n2, vis, t2) :: removeEntry (n1, n2) (removeEntry (n, n0) g ++ k))).
    erewrite <-app_comm_cons,removeEntry_app_shift2...
    eapply in_g_in_domain,removeEntry_in...
     revert dependent pfIH.
     erewrite EQ. intros.
     apply typeCheck_rewrite_pf with (pf1 := pfIH)...
       eauto.
     eauto. 
     eapply in_g_in_domain;
       eauto.
     Unshelve. all:eauto.
  - Case TOutUn.
    intros.
     assert (ND := nd_pf).
     eapply no_dup_distr in ND as (ND1 &ND2).
     eapply no_dup_isMap in ND1 as pff1.
    assert (TOUTUn: typeCheck
        g pf (dOut (fst u) (snd u) (fst v) (snd v) q)).
    eauto. 
     eapply typeCheck_object_neq_subject in TOUTUn;
      simpl in TOUTUn.
     assert (DIFF: u <> v). destruct u, v; intuition.
    assert (DIS := nd_pf).
    eapply no_dup_disjoint in DIS.
    assert (nd_pftc: NoDup (domain ((v, vis, t2) :: (removeEntry v (g ++ k))))).
    eapply no_dup_cons_removeEntry.
    erewrite domain_distr...
     eapply no_dup_isMap in nd_pftc as pftc.
    eapply TOutUn...
    all: try eapply in_app_iff; try left...
    instantiate (1 := pftc).
    destruct u, v. revert dependent pftc. erewrite removeEntry_app_shift2. intros.
    
    assert (nd_pff: NoDup
   (domain
      ((n1, n2, vis, t2) :: removeEntry (n1, n2)  g) ++
      domain k)).
    eapply no_dup_iff.
    split. eapply no_dup_cons_removeEntry...
    split...
    eapply disjoint_iff with (l1 := domain g)...

    eapply IHTC  in CONS.

    
     move CONS at bottom.
     eapply typeCheck_rewrite_pf...
       eapply no_dup_iff.
    split. eapply no_dup_cons_removeEntry...
    split...
     simpl in *...
     eapply in_g_in_domain;
       eauto.
     Unshelve. all:eauto.
  - Case TInL.
    intros.
     assert (ND := nd_pf).
     eapply no_dup_distr in ND as (ND1 &ND2).
     eapply no_dup_isMap in ND1 as pff1.
    assert (TINL: typeCheck
        g pf (dInp (fst u) (snd u) (fst x) (snd x) q)).
    eauto. 
     eapply typeCheck_object_neq_subject in TINL;
      simpl in TINL.
     assert (DIFF: u <> x). destruct u, x; intuition.
    assert (DIS := nd_pf).
    eapply no_dup_disjoint in DIS.
    assert (NIN: ~In x (domain k)).
    intros ABS.
    simpl in *. destruct BVDIS as [BVDIS _].
    rewrite <-surjective_pairing in BVDIS. contradiction.

    assert (nd_pftc: NoDup (domain (((u, vis, t1) :: (x, vis, t) :: removeEntry u  (g ++ k))))).
    simpl.
    eapply NoDup_cons.
    eapply not_in_cons; intuition.
    eapply in_domain_in_g in H5 as (ff &tt &ABS).
    assert ( K := nd_pf); erewrite <-domain_distr in K; eapply no_dup_not_in_removeEntry with (a := u) (f := ff) (t := tt) in  K. contradiction.
    eapply NoDup_cons. intros ABS.
     eapply in_domain_in_g in ABS as (ff &tt &ABS);
       eapply in_removeEntry,in_app_iff in ABS.
     destruct ABS as [ABS1 | ABS2]; try eapply in_g_in_domain in ABS1; try contradiction;
       try eapply in_g_in_domain in ABS2; try contradiction.
     eapply no_dup_removeEntry_no_dup.
     erewrite domain_distr...
    
     eapply no_dup_isMap in nd_pftc as pftc.
    econstructor...
    all: try eapply in_app_iff; try left...
    intros ABS; eapply in_domain_in_g in ABS as (ff &tt &ABS);
       eapply in_app_iff in ABS.
     destruct ABS as [ABS1 | ABS2]; try eapply in_g_in_domain in ABS1; try contradiction;
       try eapply in_g_in_domain in ABS2; try contradiction.
    erewrite domain_distr. eapply max_distr_2...
    
    instantiate (1 := pftc).
    destruct u, x. revert dependent pftc. erewrite removeEntry_app_shift2. intros.
    
    assert (nd_pff: NoDup
   (domain
      ((n, n0, vis, t1) :: (n1, n2, vis, t) :: (removeEntry (n, n0) g)) ++
      domain k)).
    eapply no_dup_iff; intuition.
    simpl; eapply NoDup_cons.
    eapply not_in_cons; intuition.
    eapply in_domain_in_g in H5 as (ff &tt &ABS).
    assert (~In (n, n0, ff, tt) (removeEntry (n, n0) g)).
    eapply no_dup_not_in_removeEntry...  contradiction.
    eapply NoDup_cons.
    intros ABS.
    eapply in_domain_in_g in ABS as (ff &tt &ABS);
      eapply in_removeEntry,in_g_in_domain in ABS; contradiction.
    eapply no_dup_removeEntry_no_dup...
    rewrite <-disjoint_car. simpl; econstructor;split; try intros ABS. eapply disjoint_absurd...
    econstructor;split; try intros ABS; try contradiction.
    rewrite disjoint_car.
    assert (DIS2: 
        disjoint ((n, n0) :: domain (removeEntry (n, n0) g)) (domain k)).
    eapply disjoint_cons_removeEntry...
    intros ABS. eapply disjoint_absurd...
    rewrite <-disjoint_car; rewrite <-disjoint_car in DIS2; inversion DIS2;subst;
      intuition.
    
    eapply IHTC  in CONS.
     
     move CONS at bottom.
     eapply typeCheck_rewrite_pf...
     eauto.
     simpl in *; intuition.
     eapply in_g_in_domain... 
     Unshelve. all:eauto.
  - Case TInUn.
    intros.
     assert (ND := nd_pf).
     eapply no_dup_distr in ND as (ND1 &ND2).
     eapply no_dup_isMap in ND1 as pff1.
    assert (TINL: typeCheck
        g pf (dInp (fst u) (snd u) (fst x) (snd x) q)).
    eauto. 
     eapply typeCheck_object_neq_subject in TINL;
      simpl in TINL.
     assert (DIFF: u <> x). destruct u, x; intuition.
    assert (DIS := nd_pf).
    eapply no_dup_disjoint in DIS.
    assert (NIN: ~In x (domain k)).
    intros ABS.
    simpl in *. destruct BVDIS as [BVDIS _].
    rewrite <-surjective_pairing in BVDIS. contradiction.
    assert (NIN2: ~ In x (domain (g ++ k))).
    intros ABS. erewrite domain_distr,in_app_iff in ABS; destruct ABS as [ABS1 | ABS2]; contradiction.
    assert (nd_pftc: NoDup (domain (( (x, vis, t) :: (g ++ k))))).
    simpl.
    eapply NoDup_cons. eauto.
    erewrite domain_distr...
    eapply no_dup_isMap in nd_pftc as pftc.
    eapply TInUn...
    all: try eapply in_app_iff; try left...
     erewrite domain_distr. eapply max_distr_2...
    
    instantiate (1 := pftc).
    eapply IHTC  in CONS.
     
     move CONS at bottom.
     eapply typeCheck_rewrite_pf...
     erewrite <-domain_distr.
     all:simpl in *; intuition.
     Unshelve. all:eauto.
     - Case TInUn.
    intros.
     assert (ND := nd_pf).
     eapply no_dup_distr in ND as (ND1 &ND2).
     eapply no_dup_isMap in ND1 as pff1.
    assert (TINL: typeCheck
        g pf (dInp (fst u) (snd u) (fst x) (snd x) q)).
    eauto. 
     eapply typeCheck_object_neq_subject in TINL;
      simpl in TINL.
     assert (DIFF: u <> x). destruct u, x; intuition.
    assert (DIS := nd_pf).
    eapply no_dup_disjoint in DIS.
    assert (NIN: ~In x (domain k)).
    intros ABS.
    simpl in *. destruct BVDIS as [BVDIS _].
    rewrite <-surjective_pairing in BVDIS. contradiction.
    assert (NIN2: ~ In x (domain (g ++ k))).
    intros ABS. erewrite domain_distr,in_app_iff in ABS; destruct ABS as [ABS1 | ABS2]; contradiction.
    assert (nd_pftc: NoDup (domain (( (x, vis, t) :: (g ++ k))))).
    simpl.
    eapply NoDup_cons. eauto.
    erewrite domain_distr...
    eapply no_dup_isMap in nd_pftc as pftc.

    
    assert (pff : isMap ( vis_proj (g ++ k))).
    eapply proj_isMap...
    assert (pff2 : isMap ( ill_proj (g ++ k))).
    eapply proj_isMap...
    eapply TInU. eauto.
    
    try eapply in_app_iff; try left...
    eauto.
    erewrite domain_distr. eapply max_distr_2...
    (* cons (vis_proj (g ++ k) ++ ill_proj (g ++ k)) ?pf2 *)
    erewrite cons_distr; split.
    (* cons (vis_proj (g ++ k)) ?Goal0 *)
    instantiate (1 := pff).
    revert dependent pff. erewrite proj_distr. intros.
    erewrite cons_distr; split.
    eapply cons_distr in H3 as [C1 C2]...
    eapply proj_cons...
    eauto.
    
    instantiate (1 := pff2). revert dependent pff2. erewrite proj_distr. intros.
    erewrite cons_distr; split.
    eapply cons_distr in H3 as [C1 C2]...
    eapply proj_cons...
    eauto.
    
    
  
    
    instantiate (1 := pftc).
    eapply IHTC  in CONS.
     
     move CONS at bottom.
     eapply typeCheck_rewrite_pf...
     erewrite <-domain_distr.
     all:simpl in *; intuition.
     Unshelve. eauto. eauto. eauto.
     eapply no_dup_isMap. erewrite domain_distr,no_dup_iff.
     split. eapply no_dup_vis_proj...
     split. eapply no_dup_ill_proj...
     eapply disjoint_projections...
     all:eauto.
Qed.

Lemma isMap_remove a l1 l2:
  isMap (l1 ++ a :: l2) ->
  isMap (l1 ++ l2).
Proof with eauto.
  introv ISMAP.
   unfold isMap in *;
     introv [EQ1 EQ2];
       try specialize ISMAP with x f1 t1 f2 t2;
    try eapply ISMAP;
     try eapply in_app_iff in EQ1 as [L1 | R1];
     try eapply in_app_iff in EQ2 as [L2 | R2];
     split;
     try eapply in_app_iff...
   all:repeat right...
Qed.

Hint Resolve split_pf.
Hint Constructors tEnv_split.

Lemma split_illECast_cons: forall g pf pfic pfc,
    cons (vis_proj g ++ ill_proj g) pfc ->
    tEnv_split g (illECast g) g pf pfic pf.
Proof with eauto.
  introv CONS; induction g;simpl.
  eapply SpNil...
  assert (PF := pf).
  eapply isMap_cons in PF.
  assert (PFIC_ := pfic).
    unfold illECast in PFIC_;
    rewrite map_cons in PFIC_;
     eapply isMap_cons in PFIC_.
  assert (PFIC: isMap (illECast g)).
  unfold illECast...
  clear PFIC_.
  assert (PFC_ := pfc).
  assert (PFC: isMap (vis_proj g ++ ill_proj g)).
  destruct a as [[[a1 a2]f1]t1]; destruct f1;
    simpl in PFC_;
    try eassumption.
  eapply isMap_remove...
  eapply isMap_cons...
  clear PFC_.
  
  destruct a as [[[a1 a2]f1]t1].
  assert (prf1: isMap (removeEntry (a1, a2)
                   ((a1, a2, f1, t1) :: g))).
  eapply isMap_removeEntry...
  assert (prf2: forall t,
             isMap ((removeEntry (a1, a2) ((a1, a2, ill, t) :: illECast g)))).
  assert (TMP:=   pfic).
  intros; simpl; rewrite pairEq_eq_true;
    simpl in TMP; eapply isMap_cons...
  assert (prf3: forall t,
             isMap ((removeEntry (a1, a2) ((a1, a2, vis, t) :: illECast g)))).
  assert (TMP:=   pfic).
  intros; simpl; rewrite pairEq_eq_true; simpl in TMP
  ; eapply isMap_cons...
  destruct f1,t1;try destruct m; simpl.
  - specialize prf2 with (Chan lin empty t1).
    simpl in CONS;
      eapply IHg
      with (pf := PF) (pfic := PFIC) 
      in CONS.
    eapply SpLin with (n := (a1,a2)) (g''' :=g) (f := hid) (p := p) (pf' := prf1) (pf'' := prf2).
    eauto.
    eauto.
    eauto.
    eauto.
    gen prf1 prf2.    simpl; try rewrite pairEq_eq_true.
    introv.
    eauto.
    simpl; try rewrite pairEq_eq_true...
    all:econstructor...

  - specialize prf2 with (Chan un p t1).
    simpl in CONS; eapply IHg  with (pf := PF) (pfic := PFIC) in CONS.
    eapply SpUn with (n := (a1,a2)) (g''' :=g) (f := hid) (p := p) (pf' := prf1) (pf'' := prf2).
    eauto.
    eauto.
    eauto.
    gen prf1 prf2.    simpl; try rewrite pairEq_eq_true.
    introv.
    eauto.
    simpl; try rewrite pairEq_eq_true...
    all:econstructor...

  - specialize prf2 with Top.
    simpl in CONS; eapply IHg  with (pf := PF) (pfic := PFIC)  in CONS.
    eapply SpTop with (n := (a1,a2)) (g''' :=g) (f := hid) (pf' := prf1) (pf'' := prf2).
    eauto.
    eauto.
    eauto.
    gen prf1 prf2.    simpl; try rewrite pairEq_eq_true.
    introv.
    eauto.
    simpl; try rewrite pairEq_eq_true...
    all:econstructor...

  - specialize prf2 with (Chan lin empty t1).
    gen pfc; simpl; introv CONS.
    simpl in CONS; eapply cons_distr in CONS as (C1 &C2).
    eapply gcons_cons in C2.
    assert (pff: isMap (vis_proj g  ++ ill_proj g)).
    eapply isMap_remove...
    assert (CONS :  cons (vis_proj g ++ ill_proj g) pff).
    intros; eapply cons_distr...
    eapply IHg  with (pf := PF) (pfic := PFIC) in CONS.
    eapply SpLin with (n := (a1,a2)) (g''' :=g) (f := ill) (p := p) (pf' := prf1) (pf'' := prf2).
    eauto.
    eauto.
    eauto.
    eauto.
    gen prf1 prf2.    simpl; try rewrite pairEq_eq_true.
    introv.
    eauto.
    simpl; try rewrite pairEq_eq_true...
    all:econstructor...

  - specialize prf2 with (Chan un p t1).
      gen pfc; simpl; introv CONS.
    simpl in CONS; eapply cons_distr in CONS as (C1 &C2).
    eapply gcons_cons in C2.
    assert (pff: isMap (vis_proj g  ++ ill_proj g)).
    eapply isMap_remove...
    assert (CONS :  cons (vis_proj g ++ ill_proj g) pff).
    intros; eapply cons_distr...
    simpl in CONS; eapply IHg  with (pf := PF) (pfic := PFIC)  in CONS.
    eapply SpUn with (n := (a1,a2)) (g''' :=g) (f := ill) (p := p) (pf' := prf1) (pf'' := prf2).
    eauto.
    eauto.
    eauto.
    gen prf1 prf2.    simpl; try rewrite pairEq_eq_true.
    introv.
    eauto.
    simpl; try rewrite pairEq_eq_true...
    all:econstructor...

  - specialize prf2 with Top.

      gen pfc; simpl; introv CONS.
    simpl in CONS; eapply cons_distr in CONS as (C1 &C2).
    eapply gcons_cons in C2.
    assert (pff: isMap (vis_proj g  ++ ill_proj g)).
     eapply isMap_remove...
    assert (CONS :  cons (vis_proj g ++ ill_proj g) pff).
    intros; eapply cons_distr...
    simpl in CONS; eapply IHg  with (pf := PF) (pfic := PFIC) in CONS.
    eapply SpTop with (n := (a1,a2)) (g''' :=g) (f := ill) (pf' := prf1) (pf'' := prf2).
    eauto.
    eauto.
    eauto.
    gen prf1 prf2.    simpl; try rewrite pairEq_eq_true.
    introv.
    eauto.
    simpl; try rewrite pairEq_eq_true...
    all:econstructor...

  - assert (p = empty).
    simpl in CONS; eapply cons_lin in CONS...
    subst.
    specialize prf3 with (Chan lin empty t1).
    gen pfc; simpl; introv CONS; eapply gcons_cons in CONS.
    eapply IHg  with (pf := PF) (pfic := PFIC) in CONS.
    eapply SpLin with (n := (a1,a2)) (g''' :=g) (p := empty) (f := vis) (pf' := prf1) (pf'' := prf3).
    eauto.
    eauto.
    eauto.
    eauto.
    gen prf1 prf3.    simpl; try rewrite pairEq_eq_true.
    introv.
    eauto.
    simpl; try rewrite pairEq_eq_true...
    all:econstructor...

  - specialize prf3 with (Chan un p t1).
     gen pfc; simpl; introv CONS; eapply gcons_cons in CONS.
    simpl in CONS; eapply IHg  with (pf := PF) (pfic := PFIC)  in CONS.
    eapply SpUn with (n := (a1,a2)) (g''' :=g) (f := vis) (p := p) (pf' := prf1) (pf'' := prf3).
    eauto.
    eauto.
    eauto.
    gen prf1 prf3.    simpl; try rewrite pairEq_eq_true.
    introv.
    eauto.
    simpl; try rewrite pairEq_eq_true...
    all:econstructor...

  - specialize prf3 with Top.

    gen pfc; simpl; introv CONS; eapply gcons_cons in CONS.
    simpl in CONS; eapply IHg  with (pf := PF) (pfic := PFIC)  in CONS.
    eapply SpTop with (n := (a1,a2)) (g''' :=g) (f := vis) (pf' := prf1) (pf'' := prf3).
    eauto.
    eauto.
    eauto.
    gen prf1 prf3.    simpl; try rewrite pairEq_eq_true.
    introv.
    eauto.
    simpl; try rewrite pairEq_eq_true...
    all:econstructor...

    Unshelve.
    all:
      try match goal with
        | [ pf : isMap (_ :: ?g) |- isMap (?g)] =>
            try eapply isMap_cons in pf
        | [H : isMap (vis_proj _ ++ _) |- isMap (vis_proj _)] =>
            try eapply isMap_distr in H as [H1 _]
        | [H : isMap (_ ++ _ :: ill_proj _ ) |- isMap (ill_proj _)] =>
            try eapply isMap_distr in H as [_ H1];
            simpl in H1
        end;
      try eassumption.
    try eapply isMap_distr in pfc as [H1 H2]...
    all:
      try assert (PF2 := pfc);
      try eapply isMap_distr
      with (g2 := (a1, a2, ill, Chan lin p t1) :: ill_proj g) in PF2 as [H1 H2];
      try eapply isMap_cons in H2;
      try eassumption.
    all: try eapply isMap_distr in PF2 as [H1 H2];
         try eapply isMap_cons in H2;
      try eassumption.
    all:assert (PF2 := pfc);
      try eapply isMap_distr in PF2 as [K1 K2];
      try eassumption.
     

    
Qed.
  
  

Lemma disjoint_remove_inv : forall n n0 l1 l2,
    disjoint l1 l2 ->
    disjoint l1 (List.remove nat_pair_eq_dec (n, n0) l2).
Proof with eauto.
  introv DIS; induction l1; try econstructor;
    inv DIS; try intros ABS;
    try eapply in_remove in ABS; intuition...
Qed.

Lemma disjoint_remove_swap: forall n n0 l1 l2,
    disjoint (List.remove nat_pair_eq_dec (n, n0) l1) l2 ->
    disjoint l1 (List.remove nat_pair_eq_dec (n, n0) l2).
Proof with eauto.
  introv DIS; induction l1; try econstructor;
    case_eq (nat_pair_eq_dec (n, n0) a); intros; subst; simpl in DIS;
    try rewrite H in *;
    try eapply in_remove in H0;
    try eapply disjoint_l_cons in DIS;
    intuition.
Qed.  


Lemma open_free g1 p1 a1 a2 b1 b2 g2 p2 pf
  (nd : NoDup (secLabs p1)): 
  lts g1 p1 (aOut a1 a2 b1 b2) g2 p2 pf ->
  disjoint (fn p1) (secLabs p1) ->
  ~In (b1, b2) (secLabs p2).
Proof with eauto using payload_occurs, disjoint_commute.
  intros LTS DIS; dependent induction LTS; simpl in *...

  Case parL.
  assert (IH: ~ In (b1, b2) (secLabs p2)).
  eapply IHLTS...
  eapply no_dup_iff in nd; intuition.
  eapply disjoint_app_l,disjoint_commute,disjoint_app_r,
    disjoint_commute 
    in DIS...
  assert (~In (b1, b2) (secLabs q)).
  intros ABS.
  assert (PO: In (b1, b2) (fn p1) \/ In (b1, b2) (secLabs p1))...
  destruct PO as [FN | SL].
  eapply disjoint_absurd with (x := (b1, b2));
    try eapply in_app_iff...
  eapply no_dup_iff in nd as (ND1 &ND2 &DIS_SL);
    eapply  disjoint_absurd with (x := (b1, b2))...
  eapply not_in_and_app...

  all: intuition.

  Case open. 
  assert (ND :=nd).
  eapply IHLTS; eapply no_dup_distr in nd; intuition...

  eapply disjoint_commute,disjoint_app_l,disjoint_commute,
    disjoint_remove 
    in DIS;
    try intros ABS;
    eapply no_dup_iff in ND; intuition; 
    try eapply disjoint_absurd...

  Case hide.
  assert (ND :=nd).
  eapply IHLTS; eapply no_dup_distr in nd; intuition...
  eapply disjoint_commute,disjoint_app_l,disjoint_commute in DIS...
  eapply disjoint_remove in DIS; try intros ABS;
    eapply no_dup_iff in ND; intuition; try eapply disjoint_absurd...
  eapply in_app_iff in H0 as [OK | ABS]; 
    try inv ABS; try contradiction...
Qed.

Lemma identif_payload 
  k1 k2 k' k'' q1 q2 a1 a2 b1 b2 b3 b4 pf1 pf2
  (nd : NoDup (secLabs q1)) 
  (dis: disjoint (fn q1) (secLabs q1)):
  lts k1 q1 (aOut a1 a2 b1 b2) k' q2 pf1 ->
  lts k2 q1 (aOut a1 a2 b3 b4) k'' q2 pf2 ->
  b1 = b3 /\ b2 = b4.
Proof with eauto.
  intros.
  revert dependent b3. revert dependent b4. 
  revert dependent k2. revert dependent k''.
  dependent induction H; intros;
    assert (ND := nd);
    try simpl in *; 
    try eapply no_dup_distr in ND as [nd1 nd2]...
  inversion H0; subst; eapply IHlts;
    try eapply disjoint_app_l,disjoint_commute,
    disjoint_app_r,disjoint_commute in dis... 
  inversion H2; subst...
  inversion H3; subst...

  Case open.
  remember b1 as c1; remember b2 as c2.
  subst b1 b2.
  remember b3 as b1; remember b4 as b2.
  subst b3 b4.
  assert (ND := nd).
  assert (CONCL: 
           lts g (dNu c1 c2 p) 
             (aOut a1 a2 c1 c2) g' p' pf)...
  inv H1; eapply IHlts ...
  eapply disjoint_commute,disjoint_app_l,disjoint_commute,
    disjoint_remove in dis;
    try intros ABS;
    eapply no_dup_iff in nd; intuition; 
    try eapply disjoint_absurd...
  eapply disjoint_commute,disjoint_app_l,disjoint_commute,
    disjoint_remove in dis;
    try intros ABS;
    eapply no_dup_iff in nd; intuition; 
    try eapply disjoint_absurd...
  instantiate (1 := pf2).
  eapply open_free in CONCL; simpl in CONCL; intuition...
  assert (In (c1, c2) (secLabs p'0 ++ (c1, c2) :: nil)).
  eapply in_app_iff; right...
  intuition.


  

  Case hide.
  assert (ND := nd).
  inv H1; eapply IHlts ...
  eapply disjoint_commute,disjoint_app_l,disjoint_commute,
    disjoint_remove in dis;
    try intros ABS;
    eapply no_dup_iff in nd; intuition; 
    try eapply disjoint_absurd...
  instantiate (1 := pf2).
  assert (ABS_LTS := H13).
  eapply open_free in ABS_LTS; simpl in *; intuition...
  remember b5 as c1; remember b4 as c2.
  assert (In (c1, c2) (secLabs p' ++ (c1, c2) :: nil)).
  eapply in_app_iff; right...
  intuition.
  all:
    eapply disjoint_commute,disjoint_app_l,disjoint_commute,
      disjoint_remove in dis;
    try intros ABS;
    eapply no_dup_iff in nd; intuition; 
    try eapply disjoint_absurd...

  Unshelve.
  all:eauto.
Qed.





Lemma lts_after_inp: forall g1 p1 a1 a2 b1 b2 g2 p2 nd_pf,
    lts g1 p1
      (aIn a1 a2 b1 b2) g2 p2 nd_pf ->
    exists f m q t r tb,
      typeOf g1 (a1, a2) (Chan m q t) /\
        In ((b1, b2), f, tb) g1 /\
        f <> hid /\
        type_plus t tb r.
Proof with eauto.
  introv  LTS.
  dependent induction LTS.
  try eapply IHLTS...
  exists f lin inp t t2 t1. intuition. all:eauto. eapply type_plus_comm...
  exists f un pol t t2 t1. intuition. all:eauto. eapply type_plus_comm...  eapply type_plus_comm... 
  exists f un pol t t2 t1. intuition. all:eauto. eapply type_plus_comm...  eapply type_plus_comm... 
  destruct H as [DIFF_a DIFF_b].
  assert (IH : aIn a1 a2 b1 b2 = aIn a1 a2 b1 b2)...
  eapply IHLTS in IH as 
      (ff & mm &qq & tt0 &tr &ttb &TYP1 &IN1 &DIFF1 & TP1)...
  inv TYP1; repeat eexists...
  eapply in_app_iff in H as [HD | TL]; 
    try inverts HD; eapply in_app_iff;
    try inverts TL as EQ; try inv EQ; try contradiction...
  repeat right...
  eapply in_app_iff in IN1 as [HD | TL]; 
    try inverts HD; eapply in_app_iff;
    try inverts TL as EQ; try inv EQ; try contradiction...
  repeat right...

Qed.

Lemma lts_after_out: forall g1 p1 a1 a2 b1 b2 g2 p2 nd_pf,
    lts g1 p1
      (aOut a1 a2 b1 b2) g2 p2 nd_pf ->
    exists m q t r tb,
      typeOf g1 (a1, a2) (Chan m q t) /\
        typeOf g1 (b1, b2) tb  /\
        type_remove tb t r.
Proof with eauto.
  intros g1 p1 a1 a2 b1 b2 g2 p2 nd_pf LTS.
  dependent induction LTS.
  eapply IHLTS...
  exists lin out t t2 t1. intuition. all:eauto. 
  exists un pol t t2 t1. intuition. all:eauto. 
  specialize IHLTS with a1 a2 b1 b2.
  intuition.
  destruct H0 as [m [q [tt [rr [ttb [TYPa [INb [NI TREM]]]]]]]].
  exists m q tt rr ttb.
  eapply nonRecActions2 in LTS as DIFF.
  intuition.
  inversion TYPa. subst. 
  inversion H2. inversion H3; intuition.
  eapply in_removeEntry in H3...
  inversion INb.  inversion H2; subst.
  inversion H6. subst...
  eapply in_removeEntry in H6...
  unfold type_remove...
  destruct H as [DIFF_a DIFF_b].
  assert (IH : aOut a1 a2 b1 b2 = aOut a1 a2 b1 b2)...
  eapply IHLTS in IH as 
      (mm &qq & tt0 &tr &ttb &TYP1 &IN1 &DIFF1 & TP1)...
  destruct TP1 as [TP ISUN];
    inverts TYP1 as INa; 
    inverts IN1 as INb.
  (*repeat eexists. bad unification? *)
  exists mm qq tt0 tr ttb.
  split.
  eapply in_app_iff in INa as [HD | TL]; 
    econstructor; try eapply in_app_iff;
    try inverts TL as EQ; try inv EQ; try contradiction...
  repeat right...
  split.
  eapply in_app_iff in INb as [HD | TL]; 
    try inverts HD; econstructor; eapply in_app_iff;
    try inverts TL as EQ; try inv EQ; try contradiction...
  repeat right...
  econstructor...

Qed.


Lemma lts_out_not_ill : forall g1 p1 a1 a2 b1 b2 g2 p2 nd_pf,
    lts g1 p1 (aOut a1 a2 b1 b2) g2 p2 nd_pf ->
    flagOf g1 (b1, b2) ill ->
    False.
Proof with eauto.
  intros g1 p1 a1 a2 b1 b2 g2 p2 nd_pf LTS FY.
  dependent induction LTS.
  eapply IHLTS; eauto.
  assert (vis = ill). eapply flag_of_map with (g := g)... discriminate.
  assert (vis = ill). eapply flag_of_map with (g := g)... discriminate.
  assert (hid = ill). eapply flag_of_map with (g := g)... discriminate.
  eapply IHLTS; try tauto.
  inverts FY as INb;
    eapply in_app_iff in INb as [HD | TL]; 
    econstructor; try eapply in_app_iff;
    try inverts TL as EQ; try inv EQ; try contradiction...
 repeat right...
Qed.



Lemma not_lin_is_unrestricted:  forall p t,
    is_unrestricted (Chan lin p t) -> False.
Proof with eauto.
  unfold is_unrestricted; intros. destruct H as [pp [tt ABS]]; inversion ABS.
Qed.

Lemma replication_no_dup: forall p r q  (pf : NoDup (secLabs p)),
    replication p q r->
    NoDup(secLabs r).
Proof with eauto.     
  intros p q r pf REPL.
  dependent induction REPL.
  all: unfold secLabs in pf; fold secLabs in pf...
  all: erewrite no_dup_iff in pf; eauto; intuition auto.
Qed.


Lemma cons_char: forall g pf,
    (g = nil \/ forall (c1 c2 : name) (ff : flag) (tt : piType), In (c1, c2, ff, tt) g ->
                                                                 (tt = Top \/ (exists tt', tt = Chan lin empty tt') \/ exists pp tt', tt = Chan un pp tt')) ->
    cons g pf.
Proof with eauto.
  introv [NIL | IN]; subst.  
  simpl...
  induction g.
  simpl...
  assert (PF := pf).
  destruct a as [[[a1 a2]ff]tt].
  eapply isMap_removeEntry with (a := (a1, a2)) in PF.
  destruct tt;
    try destruct m.
  
  eapply Co_lin with (n := (a1, a2)) (pf' := PF).
  assert (IH: In (a1, a2, ff, (Chan lin p tt))
                 ((a1, a2, ff, Chan lin p tt) :: g))...
  eapply IN in IH as [ABS | [(tt2 &OK) | (tt3 &ABS)]];
    try inv OK; try discriminate...
  destruct ABS as (tt' &ABS); inv ABS...
  gen PF. simpl. rewrite pairEq_eq_true; introv.
  eapply IHg. intros; eapply IN; try repeat right...

  eapply Co_un with (n := (a1, a2)) (pf' := PF).
  assert (IH: In (a1, a2, ff, (Chan un p tt))
                 ((a1, a2, ff, Chan un p tt) :: g))...
  gen PF. simpl. rewrite pairEq_eq_true; introv.
  eapply IHg. intros; eapply IN; try repeat right...

  eapply Co_top with (n := (a1, a2)) (pf' := PF).
  assert (IH: In (a1, a2, ff, Top)
                 ((a1, a2, ff, Top) :: g))...
  gen PF. simpl. rewrite pairEq_eq_true; introv.
  eapply IHg. intros; eapply IN; try repeat right...
Qed.



Lemma tEnv_split_InB a1 a2 el1 b g1 g2 g pf1 pf2 pf:
      tEnv_split g1 g2 g pf1 pf2 pf ->
      InB (a1, a2) g1 = (el1, b) ->
      exists el2 el3,
      InB (a1, a2) g2 = (el2, b) /\
        InB (a1, a2) g = (el3, b).
Proof with eauto.
  introv TS INB.
  destruct b.
  eapply inB_implies_In_2,in_g_in_domain in INB.
   eapply split_domain_l_2 with (g :=g) in INB...
  assert (INB2:=INB).
  eapply split_domain_r with  (g2 := g2) (g := g)
    in INB2...
  eapply in_domain_in_g in INB as (ff &tt &INB);
    try eapply in_implies_InB in INB;
    eapply in_domain_in_g in INB2 as (ff2 &tt2 &INB2);
    try eapply in_implies_InB in INB2;
    try eassumption.
  repeat eexists; try split; try eassumption...
  
  case_eq (InB (a1, a2) g2). introv INB2.
  destruct b.
  eapply inB_implies_In_2,in_g_in_domain in INB2;
    erewrite split_domain_m  in INB2;
    try eapply in_domain_in_g in INB2 as (ff2 &tt2 &INB2);
    try eapply split_comm...
  try eapply in_implies_InB in INB2;
    try rewrite INB2 in INB; inv INB...

   case_eq (InB (a1, a2) g). introv INB3.
  destruct b.
  eapply inB_implies_In_2,in_g_in_domain in INB3;
    erewrite <-split_domain_r  in INB3;
    try eapply in_domain_in_g in INB3 as (ff2 &tt2 &INB3)...
  try eapply in_implies_InB in INB3;
    try rewrite INB3 in INB2; inv INB2...

  repeat eexists...
Qed.

Lemma split_newEntries0 g1 g2 g pf1 pf2 pf l M pf' pf'' pf''':
    tEnv_split g1 g2 g pf1 pf2 pf ->
    tEnv_split
      (newEntries g1 l M)
      (newEntries g2 l M)
      (newEntries g l M)
      pf' pf'' pf'''.
Proof with eauto.
  introv TS.
  induction l.
  gen pf' pf'' pf''';
  erewrite newEntries_nil;
    introv...
  destruct a as [a1 a2].
  gen pf' pf'' pf'''.
  simpl.
  case_eq (InB (a1, a2) g1).
  intros [f1 t1] b INB1.
  assert (INB_ := INB1).
  eapply tEnv_split_InB with (g2 := g2) (g := g)
    in INB_  as ([f2 t2] &[f t]  &INB2 &INB);
    try eassumption.
  rewrite INB2;
    rewrite INB.

  
  destruct b; introv.
  eapply IHl...
  gen pf' pf'' pf'''.
  case_eq (InB (a1, a2 - M) g1).
  intros [f1m t1m] b INB1M.
   assert (INB_ := INB1M).
  eapply tEnv_split_InB with (g2 := g2) (g := g)
    in INB_  as ([f2m t2m] &[fm tm]  &INB2M &INBM);
    try eassumption.
   rewrite INB2M;
  rewrite INBM.
   destruct b; simpl; introv.
   
   eapply inB_implies_In_2 in INB1M;
     eapply inB_implies_In_2 in INB2M;
     eapply inB_implies_In_2 in INBM;
     simpl in *.
   assert (TP:
            exists t2, typeOf g2 (a1, a2 - M) t2 /\
                         type_plus t1m t2 tm).
   eapply split_type_plus...
   assert (FP:
            exists t2, flagOf g2 (a1, a2 - M) t2 /\
                         flag_plus f1m t2 fm).
   eapply split_operations_3.split_flag_plus...
   destruct TP as (tt2 & TYP2 &TP);
     destruct FP as (ff2 &FYP2 &FP).
   assert (t2m = tt2).
   eapply type_of_map with (g := g2)...
   subst tt2.
   assert (f2m = ff2).
   eapply flag_of_map with (g := g2)...
   subst ff2.
   assert (ISUN:
            is_unrestricted t1m ->
            typeOf g2 (a1, a2 - M) t1m /\
              typeOf g (a1, a2 - M) t1m).
   intros; eapply split_plus_un_isrestricted...
   assert (EQ: forall  a1 a2 f t l,
              l = removeEntry (a1, a2) ((a1,a2, f,t) :: l)).
   intros; simpl; try rewrite pairEq_eq_true...
   assert (PF1 := pf').
   assert (PF2 := pf'').
   assert (PF3 := pf''').
   eapply isMap_cons in PF1;
     erewrite EQ with
     (a1 := a1) (a2 := a2) (f := f1m) (t := t1m) in PF1.
   eapply isMap_cons in PF2;
      erewrite EQ with
     (a1 := a1) (a2 := a2) (f := f2m) (t := t2m) in PF2.
   eapply isMap_cons in PF3;
      erewrite EQ with
     (a1 := a1) (a2 := a2) (f := fm) (t := tm) in PF3.
  
   destruct tm; try destruct m.

  + inv TP;
      eapply SpLin with (n := (a1, a2))
    (pf' := PF1) (pf'' := PF2) (pf''' := PF3);
      try eassumption.
    eauto.
    eauto.
    gen PF1 PF2 PF3.
    repeat rewrite <-EQ.
    introv...

    simpl; repeat rewrite pairEq_eq_true...
    all:econstructor...

     + inv TP.
      assert (TYPP:  typeOf g2 (a1, a2 - M) (Chan un p1 tm) /\
                       typeOf g (a1, a2 - M) (Chan un p1 tm)).
      eapply ISUN, un_is_unrestricted...
      destruct TYPP as (TYPP1 &TYPP2).
      assert (EQ1: Chan un p2 tm =
                Chan un p1 tm).
      eapply type_of_map with (g := g2)...
      inv EQ1.
       eapply SpUn with (n := (a1, a2))
    (pf' := PF1) (pf'' := PF2) (pf''' := PF3);
      try eassumption.
    eauto.
    eauto.
    gen PF1 PF2 PF3.
    repeat rewrite <-EQ.
    introv...

    simpl; repeat rewrite pairEq_eq_true...
    all:econstructor...
    rewrite pol_cup_id...

     + inv TP;
      eapply SpTop with (n := (a1, a2))
    (pf' := PF1) (pf'' := PF2) (pf''' := PF3);
      try eassumption.
    eauto.
    eauto.
    gen PF1 PF2 PF3.
    repeat rewrite <-EQ.
    introv...

    simpl; repeat rewrite pairEq_eq_true...
    all:econstructor...

     +

       assert (EQ: forall  a1 a2 f t l,
              l = removeEntry (a1, a2) ((a1,a2, f,t) :: l)).
   intros; simpl; try rewrite pairEq_eq_true...
   assert (PF1 := pf').
   assert (PF2 := pf'').
   assert (PF3 := pf''').
   eapply isMap_cons in PF1;
     erewrite EQ with
     (a1 := a1) (a2 := a2) (f := f1m) (t := t1m) in PF1.
   eapply isMap_cons in PF2;
      erewrite EQ with
     (a1 := a1) (a2 := a2) (f := f2m) (t := t2m) in PF2.
   eapply isMap_cons in PF3;
      erewrite EQ with
     (a1 := a1) (a2 := a2) (f := fm) (t := tm) in PF3.
  

   
       eapply InB_false in   INB1M;
          eapply InB_false in   INB2M;
          eapply InB_false in   INBM;
          intuition; subst.

  
         eapply SpTop with (n := (a1, a2))
    (pf' := PF1) (pf'' := PF2) (pf''' := PF3);
      try eassumption.
    eauto.
    eauto.
    eauto.
    gen PF1 PF2 PF3.
    repeat rewrite <-EQ.
    introv...

    simpl; repeat rewrite pairEq_eq_true...
    all:econstructor...

    Unshelve.
    all:eauto.
Qed.
   
Lemma split_newEntries: forall g1 g2 g pf1 pf2 pf p nd_pf1 nd_pf2 nd_pf pf' pf'' pf''',
    tEnv_split g1 g2 g pf1 pf2 pf ->
    tEnv_split
      (newEntries g1 (secLabs (dep_relabel p (domain g1) nd_pf1)) (max (domain g1)))
      (newEntries g2 (secLabs (dep_relabel p (domain g2) nd_pf2)) (max (domain g2)))
      (newEntries g (secLabs (dep_relabel p (domain g) nd_pf)) (max (domain g)))
      pf' pf'' pf'''.
Proof with eauto using split_newEntries0.
  introv TS.
  assert (M1: max (domain g1) = max (domain g)).
  eapply split_max...
  assert (M2: max (domain g2) = max (domain g)).
  eapply split_max,split_comm...
  gen pf' pf'' pf'''.
  repeat erewrite  identif_seclabs_of_dep_relabel;
    rewrite M1,M2; introv...

  Unshelve.
  all:eauto.
Qed.

Lemma incl_iff: forall A (l m1 m2 : list A),
    incl l m1 ->
    (forall x, In x m1 <-> In x m2) ->
    incl l m2.
Proof with eauto.
  introv INCL IFF; introv IN; try eapply IFF...
Qed.
