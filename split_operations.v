Require Import
       Bool List Omega PeanoNat Program.Equality
        ListAddOns Max RemoveEntry Domain
        header
        operations pi_syntax 
        pairEq type_system semantics
        type_operations_1
        split_exists_neutral
        sub_split
        no_dup_split_no_dup
	split_existential
        split_cons_remove
        disjoint_newEntries.

Lemma fsuper_hid: forall g1 g2 g pf1 pf2 pf n t,
    tEnv_split g1 g2 g pf1 pf2 pf ->
    In (n, hid, t) g ->
    ((flagOf g1 n hid /\ flagOf g2 n ill) \/
    (flagOf g1 n ill /\ flagOf g2 n hid)).
Proof with eauto.
  intros g1 g2 g pf1 pf2 pf n t TS IN.
  dependent induction TS.
  subst. inversion IN. 

  case_eq (pair_eq n n0). intros PEQ.
  apply pairEq_eq in PEQ as EQ. subst n0.
  inversion H4. subst.
  assert (f' = hid /\ t1 = t).
  apply in_isMap with (x := n) (g := g3)...
  intuition. subst.
  inversion H. subst... subst...
  intros PNEQ. apply pairEq_neq in PNEQ. 
  subst g'''.
  assert ( In (n, hid, t) (removeEntry n0 g3)).
  apply removeEntry_in...
  intuition.
  inversion H6; inversion H8; subst...
  left.  split...
  inversion H6; inversion H8; subst... right. split...

  inversion H3. subst.
  case_eq (pair_eq n n0). intros PEQ.
  apply pairEq_eq in PEQ as EQ. subst n0.
  inversion H4. subst.
  assert (f' = hid /\ t1 = t).
  apply in_isMap with (x := n) (g := g3)...
  intuition. subst.
  inversion H. subst... subst...
  intros PNEQ. apply pairEq_neq in PNEQ. 
  assert ( In (n, hid, t) (removeEntry n0 g3)).
  apply removeEntry_in...
  intuition.
  inversion H6; inversion H8; subst...
  left.  split...
  inversion H6; inversion H8; subst... right. split...
  
  inversion H3. subst.
  case_eq (pair_eq n n0). intros PEQ.
  apply pairEq_eq in PEQ as EQ. subst n0.
  inversion H4. subst.
  assert (f' = hid /\ t0 = t).
  apply in_isMap with (x := n) (g := g3)...
  intuition. subst.
  inversion H. subst... subst...
  intros PNEQ. apply pairEq_neq in PNEQ. 
  assert ( In (n, hid, t) (removeEntry n0 g3)).
  apply removeEntry_in...
  intuition.
  inversion H6; inversion H8; subst...
  left.  split...
  inversion H6; inversion H8; subst... right. split...
Qed.

Lemma fsuper_flag_r :
  forall g1 g2 g pf1 pf2 pf a f t f1 t1,
    tEnv_split g1 g2 g pf1 pf2 pf ->
    f <> hid ->
    In (a, f, t) g ->
    In (a, f1, t1) g2 ->
    f = f1.
Proof with eauto.
  intros. destruct a as [a1 a2]. destruct f1.
  apply fsub_hid_r with
      (a1 := a1) (a2 := a2) (t := t1) in H.
  inversion H; subst.
  apply flag_of_map with
      (x := (a1, a2)) (f1 := f) (f2 := hid)
    in pf; subst... 
  assumption.
  apply fsub_ill_r with
      (a1 := a1) (a2 := a2) (t := t1) in H.
  intuition.
  apply flag_of_map with
      (x := (a1, a2)) (f1 := f) (f2 := hid)
    in pf; subst. contradiction.
  all:eauto.
Qed.
  
Lemma flag_of_split_l : forall g1 g2 g pf1 pf2 pf n,
    tEnv_split g1 g2 g pf1 pf2 pf ->
    ((flagOf g1 n hid ->
      (flagOf g2 n ill /\ flagOf g n hid)) /\
     (flagOf g1 n vis ->
      (flagOf g2 n vis /\ flagOf g n vis)) /\
     (flagOf g1 n ill ->
      (flagOf g2 n ill /\ flagOf g n ill) \/
      (flagOf g2 n hid /\ flagOf g n hid))).
Proof with eauto.
  intros. split; intros...
  inversion H0; destruct n as [a1 a2]; subst...
  apply fsub_hid with
      g1 g2 g pf1 pf2 pf a1 a2 t
    in H1... split.
  inversion H1. subst.
  apply fsuper_hid with
      g1 g2 g pf1 pf2 pf (a1, a2) t0 in H2.
  intuition.
  inversion H0; inversion H2; subst.
  assert (ill = hid /\ t2 = t1).
  apply in_isMap with (x := (a1, a2)) (g := g1)...
  intuition. inversion H6.
  all:eauto.
  split; intros.
  inversion H0; subst.
  destruct n. 
  specialize fsub_vis with g1 g2 g pf1 pf2 pf n n0 t as FVIS.
  intuition.
  inversion H3. subst. 
  specialize fsuper_vis with g1 g2 g pf1 pf2 pf (n, n0) t0 as FVIS.
  intuition.
  destruct n. inversion H0. subst. 
  specialize fsub_ill with g1 g2 g pf1 pf2 pf n n0 t as FILL.
  intuition.
  right. inversion H2; subst. 
  specialize fsuper_hid with g1 g2 g pf1 pf2 pf (n, n0) t0 as FHID.
  intuition.
  inversion H5; subst. 
  assert (hid = ill /\ t1 = t).
  apply in_isMap with (x := (n, n0)) (g := g1)...  
  intuition. inversion H8.
  left. inversion H2; subst.
  assert (exists (f2 : flag) (t2 : piType), In (n, n0, f2, t2) g2).
  specialize split_in_ex with g1 g2 g pf1 pf2 pf (n, n0) ill t as SPIN; intuition.
  destruct H4 as [f2 [t2 IN2]].
  specialize fsuper_flag_r with
      g1 g2 g pf1 pf2 pf (n, n0) ill t0 f2 t2 as FHID.
  assert (ill <> hid) by discriminate; intuition.
  subst...
Qed.   

Hint Resolve flag_of_split_l.

Lemma split_not_in_not_ex_l: forall g1 g2 g pf1 pf2 pf a,
    tEnv_split g1 g2 g pf1 pf2 pf ->
    (~ exists f t, In (a, f, t) g) ->
    ~exists f2 t2,
        In (a, f2, t2) g2.
Proof with eauto.
  intros.
  unfold not; intros.
  elim H0.
  destruct H1 as [f1 [t1 ABS]].
  apply in_g_in_domain in ABS.
  specialize split_domain_r with g1 g2 g pf1 pf2 pf a as SPD.
  intuition.
  apply in_domain_in_g in H1...
Qed.

Lemma no_dup_split_no_dup:
  forall g1 g2 g pf1 pf2 pf,
    NoDup (domain g1) ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    NoDup (domain g).
Proof with eauto.
  intros g1 g2 g pf1 pf2 pf nd_pf TS.
  dependent induction TS.
  - subst...
  - apply no_dup_removeEntry_no_dup
      with (a := n) in nd_pf as nd_pf0. 
    subst; intuition.
    rewrite NoDup_count_occ'.
    intros x IN.
    case_eq (pair_eq n x).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst x.

    Existential 3:=nat_pair_eq_dec.
    apply count_occ_removeEntry in IN.

    assert (count_occ nat_pair_eq_dec
                      (domain (removeEntry n g3)) n > 0 ->
            False); unfold not. intros ABS.
    rewrite <-count_occ_In in ABS.
    apply in_domain_in_g in ABS.
    destruct ABS as [f1 [t1 ABS]].
    destruct t1.
    specialize tsuper_payload with
        (removeEntry n g1) (removeEntry n g2) (removeEntry n g3)
        pf' pf'' pf''' (fst n) (snd n) f1 m p0 t1
      as TSUB.
    rewrite <-surjective_pairing in TSUB; intuition.
    destruct H7 as [q1 ABS2].
    inversion ABS2; subst.
    apply no_dup_not_in_removeEntry with
        g1 n f0 (Chan m q1 t1)
      in nd_pf ; eauto.
    specialize tsuper_top with
        (removeEntry n g1) (removeEntry n g2) (removeEntry n g3)
        pf' pf'' pf''' (fst n) (snd n) f1
      as TSUB.
    rewrite <-surjective_pairing in TSUB; intuition.
    inversion H7; subst.
    apply no_dup_not_in_removeEntry with
        g1 n f0 Top
      in nd_pf ; eauto.
    intuition.

    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    assert (PNEQ2 : x <> n) by auto.
    apply count_occ_removeEntry_neq with (g := g3)
      in PNEQ2.
    rewrite <- PNEQ2.
    rewrite NoDup_count_occ' with
        (decA := nat_pair_eq_dec) in H3.
    specialize H3 with x.
    rewrite count_occ_In with
        (eq_dec := nat_pair_eq_dec) in IN.
    rewrite <-PNEQ2 in IN.
    rewrite <-count_occ_In with
        (eq_dec := nat_pair_eq_dec) in IN.
    intuition.
  - apply no_dup_removeEntry_no_dup
      with (a := n) in nd_pf as nd_pf0. 
    subst; intuition.

    rewrite NoDup_count_occ' with
        (decA := nat_pair_eq_dec).
    intros x IN.
    case_eq (pair_eq n x).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst x.
    apply count_occ_removeEntry in IN.

    assert (count_occ nat_pair_eq_dec
                      (domain (removeEntry n g3)) n > 0 ->
            False); unfold not. intros ABS.
    rewrite <-count_occ_In in ABS.
    apply in_domain_in_g in ABS.
    destruct ABS as [f1 [t1 ABS]].
    destruct t1.
    specialize tsuper_payload with
        (removeEntry n g1) (removeEntry n g2) (removeEntry n g3)
        pf' pf'' pf''' (fst n) (snd n) f1 m p0 t1
      as TSUB.
    rewrite <-surjective_pairing in TSUB; intuition.
    destruct H6 as [q1 ABS2].
    inversion ABS2; subst.
    apply no_dup_not_in_removeEntry with
        g1 n f0 (Chan m q1 t1)
      in nd_pf ; eauto.
    specialize tsuper_top with
        (removeEntry n g1) (removeEntry n g2) (removeEntry n g3)
        pf' pf'' pf''' (fst n) (snd n) f1
      as TSUB.
    rewrite <-surjective_pairing in TSUB; intuition.
    inversion H6; subst.
    apply no_dup_not_in_removeEntry with
        g1 n f0 Top
      in nd_pf ; eauto.
    intuition.

    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    assert (PNEQ2 : x <> n) by auto.
    apply count_occ_removeEntry_neq with (g := g3)
      in PNEQ2.
    rewrite <- PNEQ2.
    rewrite NoDup_count_occ' with
        (decA := nat_pair_eq_dec) in H2.
    specialize H2 with x.
    rewrite count_occ_In with
        (eq_dec := nat_pair_eq_dec) in IN.
    rewrite <-PNEQ2 in IN.
    rewrite <-count_occ_In with
        (eq_dec := nat_pair_eq_dec) in IN.
    intuition.
    
  - apply no_dup_removeEntry_no_dup
      with (a := n) in nd_pf as nd_pf0. 
    subst; intuition.

    rewrite NoDup_count_occ' with
        (decA := nat_pair_eq_dec).
    intros x IN.
    case_eq (pair_eq n x).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst x.
    apply count_occ_removeEntry in IN.

    assert (count_occ nat_pair_eq_dec
                      (domain (removeEntry n g3)) n > 0 ->
            False); unfold not. intros ABS.
    rewrite <-count_occ_In in ABS.
    apply in_domain_in_g in ABS.
    destruct ABS as [f1 [t1 ABS]].
    destruct t1.
    specialize tsuper_payload with
        (removeEntry n g1) (removeEntry n g2) (removeEntry n g3)
        pf' pf'' pf''' (fst n) (snd n) f1 m p t1
      as TSUB.
    rewrite <-surjective_pairing in TSUB; intuition.
    destruct H6 as [q1 ABS2].
    inversion ABS2; subst.
    apply no_dup_not_in_removeEntry with
        g1 n f0 (Chan m q1 t1)
      in nd_pf ; eauto.
    specialize tsuper_top with
        (removeEntry n g1) (removeEntry n g2) (removeEntry n g3)
        pf' pf'' pf''' (fst n) (snd n) f1
      as TSUB.
    rewrite <-surjective_pairing in TSUB; intuition.
    inversion H6; subst.
    apply no_dup_not_in_removeEntry with
        g1 n f0 Top
      in nd_pf ; eauto.
    intuition.

    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    assert (PNEQ2 : x <> n) by auto.
    apply count_occ_removeEntry_neq with (g := g3)
      in PNEQ2.
    rewrite <- PNEQ2.
    rewrite NoDup_count_occ' with
        (decA := nat_pair_eq_dec) in H2.
    specialize H2 with x.
    rewrite count_occ_In with
        (eq_dec := nat_pair_eq_dec) in IN.
    rewrite <-PNEQ2 in IN.
    rewrite <-count_occ_In with
        (eq_dec := nat_pair_eq_dec) in IN.
    intuition.
    
Qed.

Lemma pol_plus_of_pol_plus: forall p1 p2 p3 p4 p5,
    pol_plus p1 p2 p3 ->
    pol_plus p3 p4 p5 ->
    exists q,
      pol_plus p1 q p5.
Proof with eauto.
  intros.
  destruct p3.
  inversion H; subst. inversion H0; subst. exists p5...
  exists empty.
  eauto.
  exists p4...
  inversion H; subst.  inversion H0; subst.
  exists inp...
  exists io...
  inversion H0; subst.
  exists empty...
  exists out...
  inversion H; subst.  inversion H0; subst.
  exists out...
  exists io...
  inversion H0; subst.
  exists empty...
  exists inp...
  inversion H0; subst. exists p2...
Qed.  
  
Lemma split_of_split :
  forall g0 w0 g1 g2 g pf0 pfw0 pf1 pf2 pf
         (nd_pf1 : NoDup (domain g1)),
    tEnv_split g0 w0 g1 pf0 pfw0 pf1 ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    exists w2 pfw2,
      tEnv_split g0 w2 g pf0 pfw2 pf.
Proof with eauto.
  intros g0 w0 g1 g2 g pf0 pfw0 pf1 pf2 pf nd_pf1 TS0 TS1.
  generalize dependent g2.
  generalize dependent g.
  dependent induction TS0.
  - intros; subst. inversion TS1. subst.
    exists nil. exists pf1. apply SpNil...
    inversion H1. inversion H0. inversion H0.
  - subst. intros.
    assert (pfn0 : isMap (removeEntry n g0)).
    apply isMap_removeEntry...
    assert (pfn4 : isMap (removeEntry n g4)).
    apply isMap_removeEntry...
    specialize IHTS0 with
        (g2 :=removeEntry n g4) (g := removeEntry n g0)
        (pf := pfn0) (pf2 := pfn4).

    assert (tEnv_split g3 g4 g0 pf3 pf0 pf ->
            tEnv_split (removeEntry n g3) (removeEntry n g4) (removeEntry n g0) pf''' pfn4 pfn0).
    apply no_dup_split_no_dup with g3 g4 g0 pf3 pf0 pf in nd_pf1 as nd_pf0...
     apply no_dup_split_no_dup_r with g3 g4 g0 pf3 pf0 pf in nd_pf0 as nd_pf4...
     apply split_remove with
         (pf1 := pf3) (pf2 := pf0) (pf3 := pf)...
     
     assert (k :  NoDup (domain (removeEntry n g3))).
      apply no_dup_removeEntry_no_dup...
     
    intuition.
    destruct H7 as [w2 TSREM].
    destruct TSREM as [pfw2 TSREM].
    inversion H4; subst.

    assert (exists f0, flagOf g0 n f0).
    destruct t0.
    destruct p0.
    specialize tsub_empty with
        g3 g4 g0 pf3 pf0 pf (fst n) (snd n) f' m t0 
      as TSE.
    rewrite <-surjective_pairing in TSE.
    apply TSE in H3. destruct H3 as [p0 [T3 T0]].
    inversion T0; subst.
    exists f0; apply F_Entry with (Chan m p0 t0); auto...
    assumption.
    specialize tsub_in with
        g3 g4 g0 pf3 pf0 pf (fst n) (snd n) f' m t0 
      as TSE.
    rewrite <-surjective_pairing in TSE.
    apply TSE in H3. destruct H3 as [T0 | T0].
    inversion T0; subst.
    exists f0; apply F_Entry with (Chan m inp t0); auto...
    inversion T0; subst.
    exists f0; apply F_Entry with (Chan m io t0); auto...
    assumption.
    specialize tsub_out with
        g3 g4 g0 pf3 pf0 pf (fst n) (snd n) f' m t0 
      as TSE.
    rewrite <-surjective_pairing in TSE.
    apply TSE in H3. destruct H3 as [T0 | T0].
    inversion T0; subst.
    exists f0; apply F_Entry with (Chan m out t0); auto...
    inversion T0; subst.
    exists f0; apply F_Entry with (Chan m io t0); auto...
    assumption.
    specialize tsub_io with
        g3 g4 g0 pf3 pf0 pf (fst n) (snd n) f' m t0 
      as TSE.
    rewrite <-surjective_pairing in TSE.
    apply TSE in H3. inversion H3; subst.
    exists f0; apply F_Entry with (Chan m io t0); auto...
    assumption.
    specialize tsub_top with
        g3 g4 g0 pf3 pf0 pf (fst n) (snd n) f' as TSE.
    rewrite <-surjective_pairing in TSE.
    apply TSE in H3. inversion H3; subst.
    exists f0; apply F_Entry with Top; auto...
    assumption.

    destruct H7 as [f0 F0].
    assert (exists fw2, flag_plus f fw2 f0).
    destruct f.
    inversion H; subst.
    specialize fsub_hid with
        g3 g4 g0 pf3 pf0 pf (fst n) (snd n) t0 
      as TSE.
    rewrite <-surjective_pairing in TSE.
    apply TSE in H3.
    exists ill.
    inversion H3; inversion F0; subst; auto...
    assert (FMAP := pf).
    apply flag_of_map with
        g0 n hid f0 in FMAP; subst; auto...
    assumption.
    inversion H; subst.
    specialize fsub_hid with
        g3 g4 g0 pf3 pf0 pf (fst n) (snd n) t0 
      as TSE.
    rewrite <-surjective_pairing in TSE.
    apply TSE in H3.
    exists hid.
    inversion H3; inversion F0; subst; auto...
    assert (FMAP := pf).
    apply flag_of_map with
        g0 n hid f0 in FMAP; subst; auto...
    assumption.
    inversion H; subst.
    specialize fsub_ill with
        g3 g4 g0 pf3 pf0 pf (fst n) (snd n) t0 
      as TSE.
    rewrite <-surjective_pairing in TSE.
    apply TSE in H3.
    destruct H3 as [H3 | H3].
    exists hid.
    inversion H3; inversion F0; subst; auto...
    assert (FMAP := pf).
    apply flag_of_map with
        g0 n hid f0 in FMAP; subst; auto...
    apply Fp_ih.
    inversion H3; inversion F0; subst; auto...
    assert (FMAP := pf).
    apply flag_of_map with
        g0 n ill f0 in FMAP; subst; auto...
    assumption.
    inversion H; subst.
    specialize fsub_vis with
        g3 g4 g0 pf3 pf0 pf (fst n) (snd n) t0 
      as TSE.
    rewrite <-surjective_pairing in TSE.
    apply TSE in H3.
    exists vis.
    inversion H3; inversion F0; subst; auto...
    assert (FMAP := pf).
    apply flag_of_map with
        g0 n vis f0 in FMAP; subst; auto...
    assumption.
    

    
    destruct H7 as [fw2 FW2].
    inversion H5. subst.
    assert (EQn: n = (fst n, snd n)). apply surjective_pairing.
    rewrite EQn in H7. 
    apply tsub_payload with
        g3 g4 g0 pf3 pf0 pf (fst n) (snd n) f1 lin p' t
      in H7.
    destruct H7 as [p0 TYP0]. inversion TYP0. subst. 
    apply tsuper_payload_r with
        g3 g4 g0 pf3 pf0 pf (fst n) (snd n) f2 lin p0 t
      in H7 as K7.
    destruct K7 as [p4 TYP4]. inversion TYP4. subst.
    assert (pol_plus p' p4 p0).
    apply split_plus_lin with
        g3 g4 g0 pf3 pf0 pf (fst n) (snd n) t f' f3 f2.
    inversion H5; subst.
    assert (f' = f4 /\ t0 =  Chan lin p' t).
    apply in_isMap with (x := n) (g := g3)...
    inversion H10. subst.
    rewrite <-surjective_pairing...
    eauto.
    eauto. 
    eauto.

    specialize pol_plus_of_pol_plus with
        p q p' p4 p0 as EXPOL.
    apply EXPOL in H0 as K0.
    destruct K0 as [q2 POLPLUS].
    remember ((n, fw2, Chan lin q2  t) :: w2) as k2.
    exists k2.

    assert (pfk2 : isMap k2).
    assert (~exists f t, In (n, f, t) (removeEntry n g0)).
    intros ABS. destruct ABS as [fn [tn ABS]].
    specialize no_dup_not_in_removeEntry
      with g0 n fn tn  as NOTIN.
    apply no_dup_split_no_dup with g3 g4 g0 pf3 pf0 pf
      in nd_pf1 as nd_pf. 
    apply NOTIN in nd_pf as NOTIN2. 
    contradiction.
    eauto. 
    (*assert  (NOTIN: ~ (exists (f : flag) (t : piType), In (n, f, t) w2)).
    apply split_not_in_not_ex_l with
        (removeEntry n g1) (removeEntry n g0) pf' pfw2 pfn0...*)
    rewrite Heqk2; apply cons_isMap...
    intros ABS. destruct ABS as [fn [tn ABS]].
    apply in_g_in_domain in ABS.
    specialize split_domain_r with (removeEntry n g1) w2 (removeEntry n g0) pf' pfw2 pfn0 n as SPD. intuition. 
   apply in_domain_in_g in H11...
    
    exists pfk2.
    assert (pfnk2 : isMap (removeEntry n k2)).
    apply isMap_removeEntry...
    specialize SpLin with
        (g1 := g1) (g2 := k2) (g3 := g0)
        (pf1 := pf1) (pf2 := pfk2) (pf3 := pf) as SPLIN.
    apply SPLIN with
        (n := n) (p := p) (q := q2) (p' := p0)
        (t := t) (g''' := (removeEntry n g0))
        (f := f) (g := fw2) (f' := f0)
        (pf' := pf') (pf'' := pfnk2) (pf''' := pfn0)
      in FW2.
    + assumption.
    + assumption.
    + assumption.
    + rewrite  Heqk2... 
    + subst.
      revert dependent w2.
      unfold removeEntry. fold removeEntry.
      assert (pair_eq n n = true) by apply pairEq_eq_true...
      rewrite H10.
      intros.
      apply split_pf with
       (pf1 := pf') (pf2 := pfw2) (pf3 := pfn0)...
    + tauto.
    + induction H.
      apply flag_of_split_l with
          g3 g4 g0 pf3 pf0 pf n in H4.
      destruct H4; assumption.
      assumption.
      apply flag_of_split_l with
          g3 g4 g0 pf3 pf0 pf n in H4.
      destruct H4; assumption.
      assumption.
      apply flag_of_split_l with
          g3 g4 g0 pf3 pf0 pf n in H4.
      destruct H4; assumption.
      assumption.
      apply flag_of_split_l with
          g3 g4 g0 pf3 pf0 pf n in H4.
      destruct H4 as [[F1 F2] | [F1 F2]].
      assumption.
      assumption.
      assumption.
    +  rewrite EQn...
    + eauto.
    + eauto.
    + eauto.
  - intros.
    apply no_dup_removeEntry_no_dup with (a := n) in nd_pf1 as nd_pf1'.
    rewrite H2 in nd_pf1'. 
    intuition.
    assert (pf4: isMap (removeEntry n g4)).
    apply isMap_removeEntry...
     assert (pf0': isMap (removeEntry n g0)).
     apply isMap_removeEntry...
     specialize H5 with (pf2 := pf4) (pf := pf0').
     assert (TSREM:  tEnv_split g''' (removeEntry n g4) (removeEntry n g0) pf''' pf4 pf0').
     revert dependent pf'''.
     rewrite <-H2.
     intros.
     apply split_remove with (pf1 := pf3) (pf2 := pf0) (pf3 := pf)...
     specialize no_dup_split_no_dup with g3 g4 g0 pf3 pf0 pf as nd_pf0.
     specialize no_dup_split_no_dup_r with g3 g4 g0 pf3 pf0 pf as nd_pf3...
     specialize no_dup_split_no_dup with g3 g4 g0 pf3 pf0 pf as nd_pf0...
     intuition.
     destruct H6 as [w2 [pfw2 TSPLIT2]].
     destruct f.
    + inversion H. subst.
      specialize flag_of_split_l with
          g3 g4 g0 pf3 pf0 pf n as FSPLIT.
      intuition. 
      remember ((n, ill, (Chan un p t)) :: w2) as k2.
      exists k2.
      assert (pfk2 : isMap k2). 
      rewrite Heqk2. apply cons_isMap...
      apply split_not_in_not_ex with (removeEntry n g1)  (removeEntry n g0) pf' pfw2 pf0'...
      intros ABS; destruct ABS as [f1 [t1 ABS]].
      apply in_g_in_domain in ABS.
      specialize split_domain_l_2 with
          (removeEntry n g1) (removeEntry n g2) (removeEntry n g3) pf' pf'' pf''' n as SPD; intuition.
      apply in_domain_in_g in  H6...
      destruct H6 as [f2 [t2 ABS2]].
      apply no_dup_not_in_removeEntry in ABS2...
      exists pfk2.
      revert dependent pfw2.
      assert (ENVEQ: w2 = removeEntry n ( (n, ill, Chan un p t) :: w2)).
      rewrite removeEntry_head...
      rewrite ENVEQ. 
      intros.
      revert dependent pfk2.
      rewrite Heqk2. intros. 
      apply SpUn with
          (n := n)  (f := hid) (f' := hid) (g := ill)
          (p := p) (t := t)  
          (pf' :=  pf') (pf'' := pfw2) (pf''' := pf0').
      eauto.
      eauto.
      eauto.
      eauto.
      tauto.
      eauto.
      inversion H4; subst. destruct n. 
      specialize tsub_un with g3 g4 g0 pf3 pf0 pf n n0 f p t as TYP0.
      intuition.
    + inversion H. subst.
       specialize flag_of_split_l with
          g3 g4 g0 pf3 pf0 pf n as FSPLIT.
      intuition. 
      remember ((n, hid, (Chan un p t)) :: w2) as k2.
      exists k2.
      assert (pfk2 : isMap k2). 
      rewrite Heqk2. apply cons_isMap...
      apply split_not_in_not_ex with (removeEntry n g1)  (removeEntry n g0) pf' pfw2 pf0'...
      intros ABS; destruct ABS as [f1 [t1 ABS]].
      apply in_g_in_domain in ABS.
      specialize split_domain_l_2 with
          (removeEntry n g1) (removeEntry n g2) (removeEntry n g3) pf' pf'' pf''' n as SPD; intuition.
      apply in_domain_in_g in  H6...
      destruct H6 as [f2 [t2 ABS2]].
      apply no_dup_not_in_removeEntry in ABS2...
      exists pfk2.
      revert dependent pfw2.
      assert (ENVEQ: w2 = removeEntry n ( (n, hid, Chan un p t) :: w2)).
      rewrite removeEntry_head...
      rewrite ENVEQ. 
      intros.
      revert dependent pfk2.
      rewrite Heqk2. intros. 
      apply SpUn with
          (n := n)  (f := ill) (f' := hid) (g := hid)
          (p := p) (t := t)  
          (pf' :=  pf') (pf'' := pfw2) (pf''' := pf0').
      eauto.
      eauto.
      eauto.
      eauto. 
      tauto.
      eauto.
      inversion H4; subst. destruct n. 
      specialize tsub_un with g3 g4 g0 pf3 pf0 pf n n0 f p t as TYP0.
      intuition.
      subst.
      inversion H3; subst.
      assert (EQ: n = (fst n, snd n)) by apply surjective_pairing.
      rewrite EQ in H2. 
      apply fsub_ill with g3 g4 g0 pf3 pf0 pf (fst n) (snd n) t0 in H2 as [HID | ILL].
       remember ((n, hid, (Chan un p t)) :: w2) as k2.
      exists k2.
      assert (pfk2 : isMap k2). 
      rewrite Heqk2. apply cons_isMap...
      apply split_not_in_not_ex with (removeEntry n g1)  (removeEntry n g0) pf' pfw2 pf0'...
      intros ABS; destruct ABS as [f1 [t1 ABS]].
      apply in_g_in_domain in ABS.
      specialize split_domain_l_2 with
          (removeEntry n g1) (removeEntry n g2) (removeEntry n g3) pf' pf'' pf''' n as SPD; intuition.
      apply in_domain_in_g in  H2...
      destruct H2 as [f2 [t2 ABS2]].
      apply no_dup_not_in_removeEntry in ABS2...
      exists pfk2.
      revert dependent pfw2.
      assert (ENVEQ: w2 = removeEntry n ( (n, hid, Chan un p t) :: w2)).
      rewrite removeEntry_head...
      rewrite ENVEQ. 
      intros.
      revert dependent pfk2.
      rewrite Heqk2. intros. 
      apply SpUn with
          (n := n)  (f := ill) (f' := hid) (g := hid)
          (p := p) (t := t)  
          (pf' :=  pf') (pf'' := pfw2) (pf''' := pf0').
      apply Fp_ih.
      eauto.
      eauto.
      eauto. 
      tauto.
      rewrite EQ...
      inversion H4; subst. 
      specialize tsub_un with g3 g4 g0 pf3 pf0 pf (fst n) (snd n) f p t as TYP0. rewrite <-EQ in TYP0; intuition.

      remember ((n, ill, (Chan un p t)) :: w2) as k2.
      exists k2.
      assert (pfk2 : isMap k2). 
      rewrite Heqk2. apply cons_isMap...
      apply split_not_in_not_ex with (removeEntry n g1)  (removeEntry n g0) pf' pfw2 pf0'...
      intros ABS; destruct ABS as [f1 [t1 ABS]].
      apply in_g_in_domain in ABS.
      specialize split_domain_l_2 with
          (removeEntry n g1) (removeEntry n g2) (removeEntry n g3) pf' pf'' pf''' n as SPD; intuition.
      apply in_domain_in_g in  H2...
      destruct H2 as [f2 [t2 ABS2]].
      apply no_dup_not_in_removeEntry in ABS2...
      exists pfk2.
      revert dependent pfw2.
      assert (ENVEQ: w2 = removeEntry n ( (n, ill, Chan un p t) :: w2)).
      rewrite removeEntry_head...
      rewrite ENVEQ. 
      intros.
      revert dependent pfk2.
      rewrite Heqk2. intros. 
      apply SpUn with
          (n := n)  (f := ill) (f' := ill) (g := ill)
          (p := p) (t := t)  
          (pf' :=  pf') (pf'' := pfw2) (pf''' := pf0').
      eauto.
      eauto.
      eauto.
      eauto.
      tauto.
      rewrite EQ...
      inversion H4; subst. 
      specialize tsub_un with g3 g4 g0 pf3 pf0 pf (fst n) (snd n) f p t as TYP0. rewrite <-EQ in TYP0; intuition.
      eauto.
      +  remember ((n, vis, (Chan un p t)) :: w2) as k2.
      exists k2.
      assert (pfk2 : isMap k2). 
      rewrite Heqk2. apply cons_isMap...
      apply split_not_in_not_ex with (removeEntry n g1)  (removeEntry n g0) pf' pfw2 pf0'...
      intros ABS; destruct ABS as [f1 [t1 ABS]].
      apply in_g_in_domain in ABS.
      subst g'''.
      specialize split_domain_l_2 with
          (removeEntry n g1) (removeEntry n g2) (removeEntry n g3) pf' pf'' pf''' n as SPD; intuition.
      apply in_domain_in_g in  H2...
      destruct H2 as [f2 [t2 ABS2]].
      apply no_dup_not_in_removeEntry in ABS2...
      exists pfk2.
      revert dependent pfw2.
      assert (ENVEQ: w2 = removeEntry n ( (n, vis, Chan un p t) :: w2)).
      rewrite removeEntry_head...
      rewrite ENVEQ. 
      intros.
      revert dependent pfk2.
      rewrite Heqk2. intros. 
      apply SpUn with
          (n := n)  (f := vis) (f' := vis) (g := vis)
          (p := p) (t := t)  
          (pf' :=  pf') (pf'' := pfw2) (pf''' := pf0').
      apply Fp_vv.
      eauto.
      eauto.
      eauto.
      tauto.
      inversion H; subst. 
      inversion H3; subst.
      assert (EQ: n = (fst n, snd n)) by apply surjective_pairing.
      rewrite EQ in H2.
      apply fsub_vis with
           g3 g4 g0 pf3 pf0 pf (fst n) (snd n) t0 in H2.
      rewrite EQ...
      eauto.
      inversion H4; subst. 
      specialize tsub_un with g3 g4 g0 pf3 pf0 pf (fst n) (snd n) f p t as TYP0.
      assert (EQ: n = (fst n, snd n)) by apply surjective_pairing.
      rewrite <-EQ in TYP0; intuition.
  - intros.
    apply no_dup_removeEntry_no_dup with (a := n) in nd_pf1 as nd_pf1'.
    rewrite H2 in nd_pf1'. 
    intuition.
    assert (pf4: isMap (removeEntry n g4)).
    apply isMap_removeEntry...
     assert (pf0': isMap (removeEntry n g0)).
     apply isMap_removeEntry...
     specialize H5 with (pf2 := pf4) (pf := pf0').
     assert (TSREM:  tEnv_split g''' (removeEntry n g4) (removeEntry n g0) pf''' pf4 pf0').
     revert dependent pf'''.
     rewrite <-H2.
     intros.
     apply split_remove with (pf1 := pf3) (pf2 := pf0) (pf3 := pf)...
     specialize no_dup_split_no_dup with g3 g4 g0 pf3 pf0 pf as nd_pf0.
     specialize no_dup_split_no_dup_r with g3 g4 g0 pf3 pf0 pf as nd_pf3...
     specialize no_dup_split_no_dup with g3 g4 g0 pf3 pf0 pf as nd_pf0...
     intuition.
     destruct H6 as [w2 [pfw2 TSPLIT2]].
     destruct f.
    + inversion H. subst.
      specialize flag_of_split_l with
          g3 g4 g0 pf3 pf0 pf n as FSPLIT.
      intuition. 
      remember ((n, ill, Top) :: w2) as k2.
      exists k2.
      assert (pfk2 : isMap k2). 
      rewrite Heqk2. apply cons_isMap...
      apply split_not_in_not_ex with (removeEntry n g1)  (removeEntry n g0) pf' pfw2 pf0'...
      intros ABS; destruct ABS as [f1 [t1 ABS]].
      apply in_g_in_domain in ABS.
      specialize split_domain_l_2 with
          (removeEntry n g1) (removeEntry n g2) (removeEntry n g3) pf' pf'' pf''' n as SPD; intuition.
      apply in_domain_in_g in  H6...
      destruct H6 as [f2 [t2 ABS2]].
      apply no_dup_not_in_removeEntry in ABS2...
      exists pfk2.
      revert dependent pfw2.
      assert (ENVEQ: w2 = removeEntry n ( (n, ill, Top) :: w2)).
      rewrite removeEntry_head...
      rewrite ENVEQ. 
      intros.
      revert dependent pfk2.
      rewrite Heqk2. intros. 
      apply SpTop with
          (n := n)  (f := hid) (f' := hid) (g := ill)
          
          (pf' :=  pf') (pf'' := pfw2) (pf''' := pf0').
      eauto.
      eauto.
      eauto.
      eauto.
      tauto.
      eauto.
      inversion H4; subst. destruct n. 
      specialize tsub_top with g3 g4 g0 pf3 pf0 pf n n0 f as TYP0.
      intuition.
    + inversion H. subst.
       specialize flag_of_split_l with
          g3 g4 g0 pf3 pf0 pf n as FSPLIT.
      intuition. 
      remember ((n, hid, Top) :: w2) as k2.
      exists k2.
      assert (pfk2 : isMap k2). 
      rewrite Heqk2. apply cons_isMap...
      apply split_not_in_not_ex with (removeEntry n g1)  (removeEntry n g0) pf' pfw2 pf0'...
      intros ABS; destruct ABS as [f1 [t1 ABS]].
      apply in_g_in_domain in ABS.
      specialize split_domain_l_2 with
          (removeEntry n g1) (removeEntry n g2) (removeEntry n g3) pf' pf'' pf''' n as SPD; intuition.
      apply in_domain_in_g in  H6...
      destruct H6 as [f2 [t2 ABS2]].
      apply no_dup_not_in_removeEntry in ABS2...
      exists pfk2.
      revert dependent pfw2.
      assert (ENVEQ: w2 = removeEntry n ( (n, hid, Top) :: w2)).
      rewrite removeEntry_head...
      rewrite ENVEQ. 
      intros.
      revert dependent pfk2.
      rewrite Heqk2. intros. 
      apply SpTop with
          (n := n)  (f := ill) (f' := hid) (g := hid)
          (pf' :=  pf') (pf'' := pfw2) (pf''' := pf0').
      eauto.
      eauto.
      eauto.
      eauto. 
      tauto.
      eauto.
      inversion H4; subst. destruct n. 
      specialize tsub_top with g3 g4 g0 pf3 pf0 pf n n0 f as TYP0.
      intuition.
      subst.
      inversion H3; subst.
      assert (EQ: n = (fst n, snd n)) by apply surjective_pairing.
      rewrite EQ in H2. 
      apply fsub_ill with g3 g4 g0 pf3 pf0 pf (fst n) (snd n) t in H2 as [HID | ILL].
       remember ((n, hid, Top) :: w2) as k2.
      exists k2.
      assert (pfk2 : isMap k2). 
      rewrite Heqk2. apply cons_isMap...
      apply split_not_in_not_ex with (removeEntry n g1)  (removeEntry n g0) pf' pfw2 pf0'...
      intros ABS; destruct ABS as [f1 [t1 ABS]].
      apply in_g_in_domain in ABS.
      specialize split_domain_l_2 with
          (removeEntry n g1) (removeEntry n g2) (removeEntry n g3) pf' pf'' pf''' n as SPD; intuition.
      apply in_domain_in_g in  H2...
      destruct H2 as [f2 [t2 ABS2]].
      apply no_dup_not_in_removeEntry in ABS2...
      exists pfk2.
      revert dependent pfw2.
      assert (ENVEQ: w2 = removeEntry n ( (n, hid, Top) :: w2)).
      rewrite removeEntry_head...
      rewrite ENVEQ. 
      intros.
      revert dependent pfk2.
      rewrite Heqk2. intros. 
      apply SpTop with
          (n := n)  (f := ill) (f' := hid) (g := hid)
          (pf' :=  pf') (pf'' := pfw2) (pf''' := pf0').
      apply Fp_ih.
      eauto.
      eauto.
      eauto. 
      tauto.
      rewrite EQ...
      inversion H4; subst. 
      specialize tsub_top with g3 g4 g0 pf3 pf0 pf (fst n) (snd n) f  as TYP0. rewrite <-EQ in TYP0; intuition.

      remember ((n, ill, Top) :: w2) as k2.
      exists k2.
      assert (pfk2 : isMap k2). 
      rewrite Heqk2. apply cons_isMap...
      apply split_not_in_not_ex with (removeEntry n g1)  (removeEntry n g0) pf' pfw2 pf0'...
      intros ABS; destruct ABS as [f1 [t1 ABS]].
      apply in_g_in_domain in ABS.
      specialize split_domain_l_2 with
          (removeEntry n g1) (removeEntry n g2) (removeEntry n g3) pf' pf'' pf''' n as SPD; intuition.
      apply in_domain_in_g in  H2...
      destruct H2 as [f2 [t2 ABS2]].
      apply no_dup_not_in_removeEntry in ABS2...
      exists pfk2.
      revert dependent pfw2.
      assert (ENVEQ: w2 = removeEntry n ( (n, ill,Top) :: w2)).
      rewrite removeEntry_head...
      rewrite ENVEQ. 
      intros.
      revert dependent pfk2.
      rewrite Heqk2. intros. 
      apply SpTop with
          (n := n)  (f := ill) (f' := ill) (g := ill)
          (pf' :=  pf') (pf'' := pfw2) (pf''' := pf0').
      eauto.
      eauto.
      eauto.
      eauto.
      tauto.
      rewrite EQ...
      inversion H4; subst. 
      specialize tsub_top with g3 g4 g0 pf3 pf0 pf (fst n) (snd n) f  as TYP0. rewrite <-EQ in TYP0; intuition.
      eauto.
      +  remember ((n, vis, Top) :: w2) as k2.
      exists k2.
      assert (pfk2 : isMap k2). 
      rewrite Heqk2. apply cons_isMap...
      apply split_not_in_not_ex with (removeEntry n g1)  (removeEntry n g0) pf' pfw2 pf0'...
      intros ABS; destruct ABS as [f1 [t1 ABS]].
      apply in_g_in_domain in ABS.
      subst g'''.
      specialize split_domain_l_2 with
          (removeEntry n g1) (removeEntry n g2) (removeEntry n g3) pf' pf'' pf''' n as SPD; intuition.
      apply in_domain_in_g in  H2...
      destruct H2 as [f2 [t2 ABS2]].
      apply no_dup_not_in_removeEntry in ABS2...
      exists pfk2.
      revert dependent pfw2.
      assert (ENVEQ: w2 = removeEntry n ( (n, vis, Top) :: w2)).
      rewrite removeEntry_head...
      rewrite ENVEQ. 
      intros.
      revert dependent pfk2.
      rewrite Heqk2. intros. 
      apply SpTop with
          (n := n)  (f := vis) (f' := vis) (g := vis)
          (pf' :=  pf') (pf'' := pfw2) (pf''' := pf0').
      apply Fp_vv.
      eauto.
      eauto.
      eauto.
      tauto.
      inversion H; subst. 
      inversion H3; subst.
      assert (EQ: n = (fst n, snd n)) by apply surjective_pairing.
      rewrite EQ in H2.
      apply fsub_vis with
           g3 g4 g0 pf3 pf0 pf (fst n) (snd n) t in H2.
      rewrite EQ...
      eauto.
      inversion H4; subst. 
      specialize tsub_top with g3 g4 g0 pf3 pf0 pf (fst n) (snd n) f as TYP0.
      assert (EQ: n = (fst n, snd n)) by apply surjective_pairing.
      rewrite <-EQ in TYP0; intuition.
Qed.

Hint Resolve flag_of_split_l.
Hint Resolve split_of_split.

(*Lemma split_lin_un_false:
  forall g1 g2 g pf1 pf2 pf y1 y2 f p q t,
    In ((y1, y2), f, (Chan lin p t)) g1 ->
    typeOf g (y1, y2) (Chan un q t) ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    False.
Proof. 

Lemma split_un_lin_false:
  forall g1 g2 g pf1 pf2 pf y1 y2 f p q t,
    In ((y1, y2), f, (Chan un p t)) g1 ->
    typeOf g (y1, y2) (Chan lin q t) ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    False.
Proof. 
*)
