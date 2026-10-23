Require Import
        Bool List Lia PeanoNat Program.Equality
        ListAddOns Max Domain RemoveEntry NewEntries Replication
        header
        operations pi_syntax 
        pairEq type_system semantics
        type_operations_1
        split_exists_neutral
        sub_split
        no_dup_split_no_dup
        split_existential
        split_not_exists
        split_operations
        split_operations_2
        type_system_rules
        type_checking_0
        disjoint_newEntries.



Lemma gcons_ill : forall n t g pf,
    In (n, ill, t) g ->
    cons g pf->
    (t = Top
     \/ (exists t', t = Chan lin empty t')
     \/ exists p t', t = Chan un p t').
Proof with eauto.
 intros. 
 generalize dependent n. 
 dependent induction H0.
 - intros. 
 subst. inversion H0.
 - intros. 
 case_eq (pair_eq n n0); intros PEQ.
 rewrite <-pairEq_eq in PEQ; subst.
 inversion H. subst.
 assert (ill = f /\ t = Top).
 eapply in_isMap...
 intuition; subst.
 rewrite <-pairEq_neq in PEQ.
 specialize IHcons with n0.
 assert (In (n0, ill, t) (removeEntry n g)).
 eapply removeEntry_in...
 intuition.
 - intros.
 case_eq (pair_eq n n0); intros PEQ.
 rewrite <-pairEq_eq in PEQ; subst.
 inversion H. subst.
  assert (ill = f /\ t = Chan un p t0).
 eapply in_isMap...
 intuition; subst.
 right. right. exists p, t0...
  rewrite <-pairEq_neq in PEQ.
 specialize IHcons with n0.
 assert (In (n0, ill, t) (removeEntry n g)).
 eapply removeEntry_in...
 intuition.
- intros.
 case_eq (pair_eq n n0); intros PEQ.
 rewrite <-pairEq_eq in PEQ; subst.
 inversion H. subst.
  assert (ill = f /\ t = Chan lin empty t0).
 eapply in_isMap...
 intuition; subst.
 right. left... 
  rewrite <-pairEq_neq in PEQ.
 specialize IHcons with n0.
 assert (In (n0, ill, t) (removeEntry n g)).
 eapply removeEntry_in...
 intuition.
Qed.

#[global] Hint Resolve gcons_ill.

Lemma typeCheck_ill: forall n t g pf p,
    typeCheck g pf p ->
    In (n, ill, t) g ->
    (t = Top
     \/ (exists t', t = Chan lin empty t')
     \/ exists p t', t = Chan un p t').
Proof with eauto.
  intros n t g pf p TC IN.
  generalize dependent n.
  generalize dependent t.
  dependent induction TC.
  - intros...
  - intros.
    assert (n = n0 -> False). intros; subst. 
    assert (hid = ill /\ t = t0).
    apply in_isMap with (x := n0) (g := g)...
    intuition. inversion H1.
    specialize IHTC with t0 n0.
    assert ( In (n0, ill, t0) (removeEntry n g)).
    apply removeEntry_in...
    assert ( In (n0, ill, t0) ((n, vis, t) :: removeEntry n g)).
    apply in_cons...
    intuition.
  - intros.
   assert (exists f1 t1 f2 t2,
      In (n, f1, t1) g1 /\ In (n, f2, t2) g2).
   eapply super_in_sub...
   destruct H0 as [f1 [t1 [f2 [t2 [IN1 IN2]]]]].
   specialize fsuper_flag with
       (pf1 := pf1) (pf2 := pf2) (pf := pf)
       (f := ill) (a := n) (t := t) (f1 := f1) (t1 := t1) as FY1.
   assert (ill <> hid) by discriminate. intuition; subst.
   specialize fsuper_flag_r with
       (pf1 := pf1) (pf2 := pf2) (pf := pf)
       (f := ill) (a := n) (t := t) (f1 := f2) (t1 := t2) as FY2.
   intuition; subst.
   destruct t. destruct n as [a1 a2].
    + right.
      destruct m.
      * left.
        eapply tsuper_payload with (g1 := g1) in IN as TYP1.
        eapply tsuper_payload_r with (g2 := g2) in IN as TYP2.
        destruct TYP1 as [p3 TYP1].
        destruct TYP2 as [p4 TYP2].
        inversion TYP1; inversion  TYP2; subst.
        assert (EQ1: ill = f /\ t1 = Chan lin p3 t).
        eapply in_isMap...
        assert (EQ2: ill = f0 /\ t2 = Chan lin p4 t).
        eapply in_isMap...
        destruct EQ1,EQ2; subst.
        (*specialize IHTC1 with (Chan lin p3 t) (a1, a2).
      specialize IHTC2 with (Chan lin p4 t) (a1, a2).*)
        eapply IHTC1 in IN1 as [ABS1 | [EQ1 | EQ2]]; try discriminate. 
        destruct EQ1 as (t' &EQ1);inversion EQ1; subst.
        eapply IHTC2 in IN2 as [ABS2 | [EQ3 | EQ4]]; try discriminate. 
        destruct EQ3 as (t'' &EQ3);inversion EQ3; subst.
        assert (PP: pol_plus empty empty p).
        eapply split_cons_remove.split_plus_lin with (pf1 := pf1)...
        inversion PP; subst; exists t''...
        destruct EQ4 as (t'' &EQ4);inversion EQ4;
          inversion H2.
        destruct EQ2 as (t'' &EQ2);inversion EQ2;
          inversion H2.
        eauto.
        eauto.
      * right.
         eapply tsuper_payload with (g1 := g1) in IN as TYP1.
        eapply tsuper_payload_r with (g2 := g2) in IN as TYP2.
        destruct TYP1 as [p3 TYP1].
        destruct TYP2 as [p4 TYP2].
        inversion TYP1; inversion  TYP2; subst.
        assert (EQ1: ill = f /\ t1 = Chan un p3 t).
        eapply in_isMap...
        assert (EQ2: ill = f0 /\ t2 = Chan un p4 t).
        eapply in_isMap...
        destruct EQ1,EQ2; subst.
        (*specialize IHTC1 with (Chan lin p3 t) (a1, a2).
      specialize IHTC2 with (Chan lin p4 t) (a1, a2).*)
        eapply IHTC1 in IN1 as [ABS1 | [EQ1 | EQ2]]; try discriminate. 
        destruct EQ1 as (t' &EQ1);inversion EQ1; subst.
        eapply IHTC2 in IN2 as [ABS2 | [EQ3 | EQ4]]; try discriminate.
        exists p,t...
        exists p,t...
        all:eauto.
    + left...
 (*       destruct EQ3 as (t'' &EQ3);inversion EQ3; subst.
        destruct EQ2 as (t' &EQ2);inversion EQ2. inversion H2; subst.
      
      
       
      assert (m = ill). 
      eapply tsuper_payload with (g1 := g1) in IN as TYP1.
      eapply tsuper_payload_r with (g2 := g2) in IN as TYP2.
      destruct TYP1 as [p3 TYP1].
      destruct TYP2 as [p4 TYP2].
      inversion TYP1; inversion  TYP2; subst.
      assert (ill = f /\ t1 = Chan m p3 t).
      eapply in_isMap...
      assert (ill = f0 /\ t2 = Chan m p4 t).
      eapply in_isMap...
      intuition; subst.
      right.
      specialize IHTC1 with (Chan m p3 t) (a1, a2).
      specialize IHTC2 with (Chan m p4 t) (a1, a2).
      intuition. all:try discriminate.
      destruct H3 as [t' EQ1].
      destruct H2 as [t'' EQ2].
      inversion EQ1; inversion EQ2; subst.
      assert (exists t2 : piType, typeOf g (a1, a2) t2 /\ type_plus (Chan lin empty t'') (Chan lin empty t'') t2).
      eapply split_type_plus_r with (g1 := g1) (g2 := g2)...
      destruct H2 as [t2 [TYP TP]].
      inversion TYP. subst. 
      assert (ill = f /\  Chan lin p t'' = t2).
      eapply in_isMap...
      intuition; subst. 
      inversion TP. subst. inversion H4; subst...
      right. destruct H3 as (p' &t' &EQ).
    + left...*)
  - intros.
    specialize IHTC with t0 n.
    assert (n = u -> False); intros; subst.
    assert (vis = ill /\ Chan lin p t = t0).
    eapply in_isMap...
    intuition; subst. inversion H4.
    assert (n = v -> False); intros; subst.
    assert (vis = ill /\ t' = t0).
    eapply in_isMap...
    intuition; subst. inversion H5.
    assert (In (n, ill, t0) (removeEntry u g)).
    eapply removeEntry_in...
    assert (In (n, ill, t0) (removeEntry v(removeEntry u g))).
    eapply removeEntry_in...
    assert ( In (n, ill, t0) ((v, vis, t2) :: removeEntry v (removeEntry u g))). apply in_cons...
    assert (In (n, ill, t0) ((u, vis, t1) :: (v, vis, t2) :: removeEntry v (removeEntry u g))). apply in_cons...
    intuition.
  - intros.
    specialize IHTC with t0 n.
    assert (n = v -> False); intros; subst.
    assert (vis = ill /\ t' = t0).
    eapply in_isMap...
    intuition; subst. inversion H4. inversion H4.
    assert (In (n, ill, t0) (removeEntry v  g)).
    eapply removeEntry_in...
    assert (In (n, ill, t0) ((v, vis, t2) :: removeEntry v g)).
    apply in_cons...
    intuition.
  - intros.
    specialize IHTC with t0 n.
    assert (n = u -> False); intros; subst.
    assert (vis = ill /\ Chan lin p t = t0).
    eapply in_isMap...
    intuition; subst; try discriminate. 
    assert (In (n, ill, t0) (removeEntry u g)).
    eapply removeEntry_in...
    assert ( In (n, ill, t0) ((x, vis, t) :: removeEntry u g)). apply in_cons...
    assert (In (n, ill, t0) ((u, vis, t1) :: (x, vis, t) :: removeEntry u g)). apply in_cons...
    intuition.
  - intros.
    specialize IHTC with t0 n.
    assert (n = u -> False); intros; subst.
    assert (vis = ill /\ Chan un p t = t0).
    eapply in_isMap...
    intuition; subst; try discriminate. 
    assert (In (n, ill, t0) ((x, vis, t) :: g)). apply in_cons...
    intuition.
  - intros.
    specialize IHTC with t0 n.
    assert (n = u -> False); intros; subst.
    assert (vis = ill /\ Chan un p t = t0).
    eapply in_isMap...
    intuition; subst. all: try discriminate. 
    assert (In (n, ill, t0) ((x, vis, t) :: g)). apply in_cons...
    intuition.
Qed.
