Require Import
        Bool List Omega PeanoNat Program.Equality
        ListAddOns Max Domain RemoveEntry NewEntries Replication
        header
        operations pi_syntax 
        pairEq type_system semantics
        type_operations_1
        split_exists_neutral
        sub_split
        no_dup_split_no_dup
	split_existential
        split_cons_remove
        split_operations_3
        disjoint_newEntries.


Lemma split_cons_remove_2 :
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
    ((b1, b2, hid, t1) :: removeEntry (b1, b2) g1)
    ((b1, b2, ill, t2) :: removeEntry (b1, b2) g2)
    ((b1, b2, hid, t3) :: removeEntry (b1, b2) g3)
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
    assert (pf' : isMap (removeEntry (b1, b2) ((b1, b2, hid, Chan lin p t) :: removeEntry (b1, b2) g1))).
    unfold removeEntry at 1.
    assert (PEQ: pair_eq (b1, b2) (b1, b2)=true).
    apply pairEq_eq_true...
    rewrite PEQ...
    assert (pf'' : isMap (removeEntry (b1, b2) ((b1, b2, ill, Chan lin p2 t) :: removeEntry (b1, b2) g2))). 
     unfold removeEntry at 1.
    assert (PEQ: pair_eq (b1, b2) (b1, b2)=true).
    apply pairEq_eq_true...
    rewrite PEQ...
    assert (pf''' : isMap (removeEntry (b1, b2) ((b1, b2, hid, Chan lin p3 t) :: removeEntry (b1, b2) g3))). 
     unfold removeEntry at 1.
    assert (PEQ: pair_eq (b1, b2) (b1, b2)=true).
    apply pairEq_eq_true...
    rewrite PEQ...
    
    apply SpLin with
        (n := (b1, b2))
        (f := hid) (g := ill) (f' := hid)
        (p := p) (t := t) (pf' := pf') (pf'' := pf'')
        (pf''' := pf''') (q := p2) (p' := p3).
    apply Fp_hi.
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
       assert (pf' : isMap (removeEntry (b1, b2) ((b1, b2, hid, Chan un p t) :: removeEntry (b1, b2) g1))).
       unfold removeEntry at 1.
       assert (PEQ: pair_eq (b1, b2) (b1, b2)=true).
       apply pairEq_eq_true...
       rewrite PEQ...
       assert (pf'' : isMap (removeEntry (b1, b2) ((b1, b2, ill, Chan un p2 t) :: removeEntry (b1, b2) g2))). 
       unfold removeEntry at 1.
       assert (PEQ: pair_eq (b1, b2) (b1, b2)=true).
       apply pairEq_eq_true...
       rewrite PEQ...
       assert (pf''' : isMap (removeEntry (b1, b2) ((b1, b2, hid, Chan un p3 t) :: removeEntry (b1, b2) g3))). 
       unfold removeEntry at 1.
       assert (PEQ: pair_eq (b1, b2) (b1, b2)=true).
       apply pairEq_eq_true...
       rewrite PEQ...
       destruct H1 as [K1 k2]; inversion K1. inversion H1; subst p2 p3. 
       clear H1 H2. 
       apply SpUn with
           (n := (b1, b2))
           (f := hid) (g := ill) (f' := hid)
           (p := p) (t := t) (pf' := pf') (pf'' := pf'')
           (pf''' := pf''') .
       apply Fp_hi.
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

    +  assert (pf' : isMap (removeEntry (b1, b2) ((b1, b2, hid, Top) :: removeEntry (b1, b2) g1))).
       unfold removeEntry at 1.
       assert (PEQ: pair_eq (b1, b2) (b1, b2)=true).
       apply pairEq_eq_true...
       rewrite PEQ...
       assert (pf'' : isMap (removeEntry (b1, b2) ((b1, b2, ill, Top) :: removeEntry (b1, b2) g2))). 
       unfold removeEntry at 1.
       assert (PEQ: pair_eq (b1, b2) (b1, b2)=true).
       apply pairEq_eq_true...
       rewrite PEQ...
       assert (pf''' : isMap (removeEntry (b1, b2) ((b1, b2, hid, Top) :: removeEntry (b1, b2) g3))). 
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
           (f := hid) (g := ill) (f' := hid)
            (pf' := pf') (pf'' := pf'')
           (pf''' := pf''') .
    apply Fp_hi.
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



Lemma split_cons_remove_3 :
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
    ((b1, b2, f1, t1) :: removeEntry (b1, b2) g1)
    ((b1, b2, f2, t2) :: removeEntry (b1, b2) g2)
    ((b1, b2, f3, t3) :: removeEntry (b1, b2) g3)
    pf1' pf2' pf3'.
 Proof with eauto.
  intros g1 g2 g3 pf1 pf2 pf3
         nd_pf1 nd_pf2 nd_pf3
         b1 b2 f1 t1 f2 t2 f3 t3 pf1' pf2' pf3'
         T1 T2 T3 TS.
  assert (FP: flag_plus f1 f2 f3).
  assert (SFP: exists f2 : flag, flagOf g2 (b1, b2) f2 /\ flag_plus f1 f2 f3).
  eapply split_flag_plus...
  destruct SFP as (f'' &FY2 &SFP).
  assert (f'' = f2).
  eapply flag_of_map with (g := g2)...
  subst...
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
    assert (pf' : isMap (removeEntry (b1, b2) ((b1, b2, f1, Chan lin p t) :: removeEntry (b1, b2) g1))).
    unfold removeEntry at 1.
    assert (PEQ: pair_eq (b1, b2) (b1, b2)=true).
    apply pairEq_eq_true...
    rewrite PEQ...
    assert (pf'' : isMap (removeEntry (b1, b2) ((b1, b2, f2, Chan lin p2 t) :: removeEntry (b1, b2) g2))). 
     unfold removeEntry at 1.
    assert (PEQ: pair_eq (b1, b2) (b1, b2)=true).
    apply pairEq_eq_true...
    rewrite PEQ...
    assert (pf''' : isMap (removeEntry (b1, b2) ((b1, b2, f3, Chan lin p3 t) :: removeEntry (b1, b2) g3))). 
     unfold removeEntry at 1.
    assert (PEQ: pair_eq (b1, b2) (b1, b2)=true).
    apply pairEq_eq_true...
    rewrite PEQ...
    
    eapply SpLin with (pf' := pf') (pf'' := pf'')
        (pf''' := pf''')...
(*    all:eauto.
  with
        (n := (b1, b2))
        (f := f1) (g := f2) (f' := f3)
        (p := p) (t := t) (pf' := pf') (pf'' := pf'')
        (pf''' := pf''') (q := p2) (p' := p3).
    apply Fp_hi.
    all:eauto.*)
    
    revert dependent pf'. revert dependent pf''. revert dependent pf'''. simpl.
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
       assert (pf' : isMap (removeEntry (b1, b2) ((b1, b2, f1, Chan un p t) :: removeEntry (b1, b2) g1))).
       unfold removeEntry at 1.
       assert (PEQ: pair_eq (b1, b2) (b1, b2)=true).
       apply pairEq_eq_true...
       rewrite PEQ...
       assert (pf'' : isMap (removeEntry (b1, b2) ((b1, b2, f2, Chan un p2 t) :: removeEntry (b1, b2) g2))). 
       unfold removeEntry at 1.
       assert (PEQ: pair_eq (b1, b2) (b1, b2)=true).
       apply pairEq_eq_true...
       rewrite PEQ...
       assert (pf''' : isMap (removeEntry (b1, b2) ((b1, b2, f3, Chan un p3 t) :: removeEntry (b1, b2) g3))). 
       unfold removeEntry at 1.
       assert (PEQ: pair_eq (b1, b2) (b1, b2)=true).
       apply pairEq_eq_true...
       rewrite PEQ...
       destruct H1 as [K1 k2]; inversion K1. inversion H1; subst p2 p3. 
       clear H1 H2. 
       apply SpUn with
           (n := (b1, b2))
           (f := f1) (g := f2) (f' := f3)
           (p := p) (t := t) (pf' := pf') (pf'' := pf'')
           (pf''' := pf''')...
       
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

    +  assert (pf' : isMap (removeEntry (b1, b2) ((b1, b2, f1, Top) :: removeEntry (b1, b2) g1))).
       unfold removeEntry at 1.
       assert (PEQ: pair_eq (b1, b2) (b1, b2)=true).
       apply pairEq_eq_true...
       rewrite PEQ...
       assert (pf'' : isMap (removeEntry (b1, b2) ((b1, b2, f2, Top) :: removeEntry (b1, b2) g2))). 
       unfold removeEntry at 1.
       assert (PEQ: pair_eq (b1, b2) (b1, b2)=true).
       apply pairEq_eq_true...
       rewrite PEQ...
       assert (pf''' : isMap (removeEntry (b1, b2) ((b1, b2, f3, Top) :: removeEntry (b1, b2) g3))). 
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
           (f := f1) (g := f2) (f' := f3)
            (pf' := pf') (pf'' := pf'')
           (pf''' := pf''') ...
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
