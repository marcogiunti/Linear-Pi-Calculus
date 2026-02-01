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
        disjoint_newEntries
        tc_premises_5
        split_operations
        split_operations_2
        sub_split
        tc_ill_vis
        tc_premises_6
        tc_premises2
        split_operations_2
        lts_no_dup
        substitution_prelim
        split_cons_remove
        lts_payload_un_inp.

Require Import CpdtTactics LibTactics.

Hint Resolve   split_comm.
Hint Constructors cons.
Hint Constructors type_sub.
Hint Constructors type_plus.

    

  Definition gcons_distr:= cons_distr.
                               
Lemma isMap_distr : forall g1 g2,
                 isMap (g1 ++ g2) ->
                 isMap g1 /\ isMap g2.
Proof with eauto.
  intros; split; unfold isMap in *; intros; specialize H with x f1 t1 f2 t2; eapply H.
  assert (In (x, f1, t1) (g1 ++ g2)). eapply in_or_app...
  assert (In (x, f2, t2) (g1 ++ g2)). eapply in_or_app...
  all:intuition auto; eapply in_or_app...
Qed.

  


Lemma in_illECast: forall a1 a2 f t g,
      In (a1, a2, f, t) g ->
      (f = vis \/
       (f <> hid /\
        ((exists s, t = Chan lin empty s)
        \/ (exists p s, t = Chan un p s) \/ t = Top))) -> 
       In (a1, a2, f, t) (illECast g).
Proof with eauto.
  introv IN [VIS | [DIFF [OPT1 | [OPT2 | OPT3]]]].
  eapply in2_false_illECast with (x := (a1, a2))...
  all: unfold illECast; try eapply in_map_iff...
  destruct OPT1 as (s &OPT1);
    exists (a1, a2, f, t); destruct f; subst;simpl;
      try contradiction...
   destruct OPT2 as (p &s &OPT2);
    exists (a1, a2, f, t); destruct f; subst;simpl;
      try contradiction...
   exists (a1, a2, f, t); destruct f; subst;simpl;
     try contradiction...
   (* MAKE AGAIN *)
Qed.

Lemma neutral_is_gcons: forall neutral w pfn pfw,
    tEnv_split neutral w w pfn pfw pfw ->
    cons neutral pfn.
Proof with eauto. intros; eapply neutral_is_cons, split_comm...
Qed.

Lemma in_app_removeEntry_iff_0:
  forall ne3 g3 b1 b2 f3 tb3,
    In (b1, b2, f3, tb3) g3 ->
    NoDup (domain (ne3 ++ g3)) ->
    forall x,
   In x (ne3 ++ g3) <-> In x (ne3 ++ (b1, b2, f3, tb3) :: removeEntry (b1, b2) g3).
Proof with eauto.
  intuition.
  eapply in_app_iff in H1 as [K | K]; eapply in_app_iff. left... right.
  erewrite domain_distr in H0; eapply no_dup_distr in H0 as [k1 K2].
  specialize lts_no_dup.in_removeEntry_cons_iff_0 with (x := (a, b3, b0, b)) as W; eapply W... simpl. rewrite pairEq_eq_true.
  case_eq ( pair_eq (b1, b2) (a, b3)); intros EQ; try rewrite <-pairEq_eq in EQ; inversion EQ; subst. left...
  assert (f3 = b0 /\ tb3 = b).
  eapply in_isMap... intuition; subst...
  right.
  eapply removeEntry_in; erewrite <-pairEq_neq in EQ; intuition.
  eapply in_app_iff in H1 as [K | K];
  eapply in_app_iff. left...
  right.
   erewrite domain_distr in H0; eapply no_dup_distr in H0 as [k1 K2].
  case_eq ( pair_eq (b1, b2) (a, b3)); intros EQ; try rewrite <-pairEq_eq in EQ; inversion EQ; subst.
  inversion K. inversion H0; subst...
  assert (~In (a, b3, b0, b) (removeEntry (a, b3) g3)).
  eapply no_dup_not_in_removeEntry...
  contradiction.
   inversion K. inversion H0; subst...
   eapply in_removeEntry; erewrite <-pairEq_neq in EQ; intuition auto...
Qed.
   
Lemma in_app_removeEntry_iff_01: forall ne3 g3 b1 b2 f3 f4 tb3,
      NoDup (domain ((ne3 ++ (b1, b2, f3, tb3) :: removeEntry (b1, b2) g3)))->
    forall x,
      In x (ne3 ++ (b1, b2, f3, tb3) :: removeEntry (b1, b2) g3) <-> In x ((b1, b2, f3, tb3) :: removeEntry (b1, b2) (ne3 ++  (b1, b2, f4, tb3) :: removeEntry (b1, b2)g3)).
Proof with eauto.
  intros ne3 g3 b1 b2 f3 f4 tb3 nd_pf [[[x1 x2] f] t].
  split; intros; try eapply in_app_iff in H as [K | K].
  case_eq (pair_eq (x1, x2) (b1, b2)); intros ABS; try rewrite <-pairEq_eq in ABS; inversion ABS; subst.
  erewrite domain_distr in nd_pf.
  eapply no_dup_disjoint in nd_pf.
  eapply disjoint_absurd with (x := (b1, b2)), in_g_in_domain... 
  right. eapply removeEntry_in; erewrite <-pairEq_neq in H0...  erewrite in_app_iff;left...
  inversion K. inversion H; subst...
  erewrite removeEntry_app_shift.
  right. eapply in_app_iff; right.
  simpl; rewrite pairEq_eq_true...
  intros ABS.
  erewrite domain_distr in nd_pf. eapply no_dup_disjoint in nd_pf.
  eapply disjoint_absurd with (x := (b1, b2)), in_g_in_domain...

  inversion H. inversion H0; subst.
  eapply in_app_iff; right...
   erewrite removeEntry_app_shift in H0.
   eapply in_app_iff in H0 as [K | K];
     eapply in_app_iff.
   left...
   simpl in K; rewrite pairEq_eq_true in K; right; right...
   intros ABS.
  erewrite domain_distr in nd_pf. eapply no_dup_disjoint in nd_pf.
  eapply disjoint_absurd with (x := (b1, b2)), in_g_in_domain...
  Qed.
  
Lemma in_app_removeEntry_iff: forall x b1 b2 f t w g,
    NoDup (domain (w ++ g)) ->
    ~In (b1, b2) (domain w) ->
    (In x ((b1, b2, f, t) :: removeEntry (b1, b2)(w ++ g)) <->
  In x (w ++ ((b1, b2, f, t) :: removeEntry (b1, b2) g))).
Proof with eauto.
  intros x b1 b2 f t w g nd_pf NIN.
  erewrite removeEntry_app_shift.
  split; intros.
  inversion H as [K | K]; subst.
  eapply in_app_iff; right...
  eapply in_app_iff in K as [K | K].
  eapply in_app_iff...
  eapply in_app_iff; right; right...
  eapply in_app_iff in H as [K | K]; subst.
  right;eapply in_app_iff...
  inversion K; subst...
  right; eapply in_app_iff...
  assumption.
Qed.
  
Lemma typeCheck_strength_vis:
  forall b1 b2 f g t pf p pf1
         (nd_pf : NoDup (domain g)),
    f <> hid ->
     In (b1, b2, f, t) g ->
    typeCheck g pf p ->
    typeCheck ((b1, b2, vis, t) :: removeEntry (b1, b2) g) pf1 p.
Proof with eauto.
  intros b1 b2 f g t pf p pf1 nd_pf DIFF IN TC.
  destruct f. contradiction.
  eapply typeCheck_ill_vis...
  eapply typeCheck_impl,lts_no_dup.in_removeEntry_cons_iff_0...
Qed.






Lemma not_in_sl: forall g pf a1 a2 b1 b2 x1 x2 p f t,
                 typeCheck g pf (dBang a1 a2 x1 x2 p) ->
                 In (b1, b2, f, t) g ->
                 f <> hid ->
                 ~In (b1, b2) (secLabs p).
Proof with eauto.
  intros g pf a1 a2 b1 b2 x1 x2 p f t TC IN DIFF ABS.
  eapply type_checking_0.typeCheck_hid with (n := (b1, b2))in TC as (tt&TC).
  assert (f = hid). eapply flag_of_map...
  contradiction.
  simpl...
Qed.
  




Hint Resolve pol_cup_type_sub.


Lemma type_sub_tran:  forall t1 t2 t,
    type_sub t1 t2 -> type_sub t2 t -> type_sub t1 t.
Proof with eauto.
  intros t1 t2 t TS1 TS2.
  dependent induction TS1; inversion TS2; subst...
Qed.

Hint Resolve type_plus_distr2 type_plus_type_sub type_sub_tran.

Lemma type_plus_middle: forall s1 s2 s r1 r3 t,
    type_plus t r1 s1 ->
    type_plus s1 s2 s ->
    type_plus r1 s2 r3 ->
    type_plus t r3 s.
  Proof with eauto.
    intros s1 s2 s r1 r3 t TP1 TP2 TP3.
    destruct s1. destruct m, p; inversion TP2; inversion H3; inversion TP1; try inversion H9; inversion TP3; subst; try discriminate; try inversion H15; try inversion H14; try inversion H16; subst;try discriminate; try inversion H13; subst...
    inversion H6; inversion H9; subst...
    assert (EQ: (pol_cup (pol_cup p0 p3) p2) =
            pol_cup p0 ((pol_cup p3 p2))).
    destruct p0,p3,p2...
    rewrite EQ...
    inversion H6; inversion H9; subst...
    assert (EQ: (pol_cup (pol_cup p0 p3) p2) =
            pol_cup p0 ((pol_cup p3 p2))).
    destruct p0,p3,p2...
    rewrite EQ...
    inversion H6; inversion H9; subst...
    assert (EQ: (pol_cup (pol_cup p0 p3) p2) =
            pol_cup p0 ((pol_cup p3 p2))).
    destruct p0,p3,p2...
    rewrite EQ...
     inversion H6; inversion H9; subst...
    assert (EQ: (pol_cup (pol_cup p0 p3) p2) =
            pol_cup p0 ((pol_cup p3 p2))).
    destruct p0,p3,p2...
    rewrite EQ...
    inversion TP1; inversion TP2; inversion TP3; subst...
    all:try discriminate.
  Qed.
    
Lemma typeCheck_lts_out_type_remove:
  forall g p a1 a2 b1 b2 m pol t f s g1 p' g' pf pf1,
    typeCheck g pf p ->
    In (a1, a2, vis, Chan m pol t) g ->
    In (b1, b2, f, s) g ->
    lts g1 p (aOut a1 a2 b1 b2) g' p' pf1 ->
    exists r, type_remove s t r.
Proof with eauto.
  intros g p a1 a2 b1 b2 m pol t f s g1 p' g' pf pf1 TC INa INb LTS.
  revert dependent m. revert dependent t.  revert dependent s. revert dependent f. revert dependent pol.
  revert dependent a1. revert dependent a2.
  revert dependent b1. revert dependent b2.
  revert dependent g1. revert dependent g'. revert dependent p'.
  dependent induction TC.
  all: intros; inversion LTS; subst.
  - destruct n as [b1 b2]; simpl in *.
    assert (s = t). eapply type_of_map with (g :=g)...
    subst. 
    eapply IHTC...
    right.
    eapply removeEntry_in. eapply nonRecActions2...
    eauto.
  - remember ((h1 ++ (fst n, snd n, vis, t1) :: h2)) as g1. eapply IHTC with (g1 := g1)...
    all:try right; try eapply removeEntry_in; try intros ABS; try rewrite <-ABS in *; simpl in *; intuition...
  - inversion LTS; subst.
    eapply tsuper_payload with (pf1 := pf1) in INa as K; try destruct K as (qq&IN1a); try inversion IN1a; subst.
    eapply fsuper_vis with (pf1 := pf1) in INa as [K _];
      try inversion K; subst.
    assert (f0 = vis). eapply flag_of_map with (g := g1)...
    subst.
     assert (IN1b: exists f1 s1, In (b1, b2, f1, s1) g1).
     destruct s. eapply tsuper_payload with (pf1 := pf1) in INb as (qqq&INb); try inversion INb; subst. exists f0 (Chan m0 qqq s)... eauto.
     eapply tsuper_top with (pf1 := pf1) in INb; try inversion INb; subst. exists f0 Top... eauto.
     destruct IN1b as (ff &s1 &IN1b).
     assert (TR1: exists r1 : piType, type_remove s1 t r1).
     eapply IHTC1...
     destruct TR1 as (r1 &TSUB &TP &ISUN).
     assert (TP2: exists s2 : piType, typeOf g2 (b1, b2) s2 /\ type_plus s1 s2 s).
     eapply split_type_plus...
     destruct TP2 as (s2 & TYP2 & TP2).
     unfold type_remove.
     assert (TP3: exists r2, type_plus r1 s2 r2)...
     destruct TP3 as (r3 & TP3).
     exists r3...
     split.
     eapply type_plus_type_sub in TP2...
     split.
     eapply type_plus_middle...
     intros (pp& tt &ISUN2); subst.
     inversion TP2; subst.
     assert (is_unrestricted (Chan un p0 tt)).
     eapply un_is_unrestricted... intuition; subst.
     inversion TP3...
     eauto. eauto.
  - destruct u as [u1 u2],v as [v1 v2]; simpl in *;inversion LTS. subst.
    assert (t4 = t7).
    eapply type_of_map with (g := g1)...
    assert (Chan m pol t0 = Chan lin p t).
    eapply type_of_map with (g := g)...
    inversion H4; 
      subst.
    assert (s = t').  eapply type_of_map with (g := g)...
    subst...
    subst.
    assert(ABS:Chan lin out t3 = Chan un pol0 t6).
    eapply type_of_map with (g := g1)...
    inversion ABS.
  -  destruct u as [u1 u2],v as [v1 v2]; simpl in *;inversion LTS. subst.
     assert(ABS:Chan lin out t6 = Chan un pol0 t3).
     eapply type_of_map with (g := g1)...
     inversion ABS.
     subst.
    assert (t4 = t7).
    eapply type_of_map with (g := g1)...
    assert (Chan m pol t0 = Chan lin p t).
    eapply type_of_map with (g := g)...
    inversion H4; 
      subst.
    assert (s = t').  eapply type_of_map with (g := g)...
    subst...
  - destruct u as [u1 u2],v as [v1 v2]; simpl in *;inversion LTS. subst.
    assert (t3 = t6).
    eapply type_of_map with (g := g1)...
    subst.
    assert (EQ: Chan m pol t0 = Chan un p t).
    eapply type_of_map with (g := g)...
    inversion EQ; subst.
     assert (t' = s). 
     eapply type_of_map with (g := g)...
     subst...
     subst.
     assert(ABS:Chan lin out t1 = Chan un pol0 t5).
     eapply type_of_map with (g := g1)...
     inversion ABS.
  - destruct u as [u1 u2],v as [v1 v2]; simpl in *;inversion LTS. subst.
     assert(ABS:Chan lin out t5 = Chan un pol0 t1).
     eapply type_of_map with (g := g1)...
     inversion ABS.
     subst.
    assert (t3 = t6).
    eapply type_of_map with (g := g1)...
    subst.
    assert (EQ: Chan m pol t0 = Chan un p t).
    eapply type_of_map with (g := g)...
    inversion EQ; subst.
     assert (t' = s). 
     eapply type_of_map with (g := g)...
     subst...
Qed.    
    



      
