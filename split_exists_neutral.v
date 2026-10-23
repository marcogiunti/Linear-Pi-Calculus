Require Import
        Bool List Lia PeanoNat Program.Equality
        RemoveEntry Domain
        header
        operations pi_syntax
        pairEq type_system semantics pairEq
        type_operations_1
        disjoint_newEntries.

Lemma split_domain_l:
  forall g1 g2 g pf1 pf2 pf x,
    tEnv_split g1 g2 g pf1 pf2 pf ->
    In x (domain g1) <-> In x (domain g).
Proof with eauto.
  intros g1 g2 g pf1 pf2 pf x TS.
  dependent induction TS.
  - subst... intuition.
  - subst g'''. intuition.
    case_eq (pair_eq x n).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    inversion H5...
    apply in_g_in_domain in H8...
    intros PNEQ. rewrite <-pairEq_neq in PNEQ.
    apply in_domain_in_g in H7.
    destruct H7 as [f1 [t1 IN]].
    apply removeEntry_in with
        x f1 t1 n g1 in PNEQ.
    apply in_g_in_domain in PNEQ; intuition.
    apply in_domain_in_g in H7.     
    destruct H7 as [f2 [t2 IN2]].
    apply in_removeEntry in IN2.
    apply in_g_in_domain in IN2...
    assumption.
    case_eq (pair_eq x n).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    apply in_g_in_domain in H1...
    intros PNEQ. rewrite <-pairEq_neq in PNEQ.
    apply in_domain_in_g in H7.
    destruct H7 as [f1 [t1 IN]].
    apply removeEntry_in with
        x f1 t1 n g3 in PNEQ.
    apply in_g_in_domain in PNEQ; intuition.
    apply in_domain_in_g in H7.     
    destruct H7 as [f2 [t2 IN2]].
    apply in_removeEntry in IN2.
    apply in_g_in_domain in IN2...
    assumption.
  - intuition.
    subst g'''.
    case_eq (pair_eq x n).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    inversion H4...
    apply in_g_in_domain in H2...
    intros PNEQ. rewrite <-pairEq_neq in PNEQ.
    apply in_domain_in_g in H7.
    destruct H7 as [f1 [t1 IN]].
    apply removeEntry_in with
        x f1 t1 n g1 in PNEQ.
    apply in_g_in_domain in PNEQ; intuition.
    apply in_domain_in_g in H2.     
    destruct H2 as [f2 [t2 IN2]].
    apply in_removeEntry in IN2.
    apply in_g_in_domain in IN2...
    assumption.
    case_eq (pair_eq x n).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    apply in_g_in_domain in H0...
    intros PNEQ. rewrite <-pairEq_neq in PNEQ.
    apply in_domain_in_g in H7.
    destruct H7 as [f1 [t1 IN]].
    subst g'''.
    apply removeEntry_in with
        x f1 t1 n g3 in PNEQ.
    apply in_g_in_domain in PNEQ; intuition.
    apply in_domain_in_g in H2.     
    destruct H2 as [f2 [t2 IN2]].
    apply in_removeEntry in IN2.
    apply in_g_in_domain in IN2...
    assumption.
  -  intuition. subst g'''.
     case_eq (pair_eq x n).
     intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
     inversion H4...
     apply in_g_in_domain in H2...
     intros PNEQ. rewrite <-pairEq_neq in PNEQ.
     apply in_domain_in_g in H7.
     destruct H7 as [f1 [t1 IN]].
     apply removeEntry_in with
         x f1 t1 n g1 in PNEQ.
     apply in_g_in_domain in PNEQ; intuition.
     apply in_domain_in_g in H2.     
     destruct H2 as [f2 [t2 IN2]].
     apply in_removeEntry in IN2.
     apply in_g_in_domain in IN2...
     assumption.
     case_eq (pair_eq x n).
     intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
     apply in_g_in_domain in H0...
     intros PNEQ. rewrite <-pairEq_neq in PNEQ.
     apply in_domain_in_g in H7.
     destruct H7 as [f1 [t1 IN]].
     subst g'''.
     apply removeEntry_in with
         x f1 t1 n g3 in PNEQ.
     apply in_g_in_domain in PNEQ; intuition.
     apply in_domain_in_g in H2.     
     destruct H2 as [f2 [t2 IN2]].
     apply in_removeEntry in IN2.
     apply in_g_in_domain in IN2...
     assumption.
Qed.

Lemma split_domain_r:
  forall g1 g2 g pf1 pf2 pf x,
    tEnv_split g1 g2 g pf1 pf2 pf ->
    In x (domain g2) <-> In x (domain g).
Proof with eauto.
  intros g1 g2 g pf1 pf2 pf x TS.
  dependent induction TS.
  - subst... intuition.
  - subst g'''. intuition.
    case_eq (pair_eq x n).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    inversion H5...
    apply in_g_in_domain in H8...
    intros PNEQ. rewrite <-pairEq_neq in PNEQ.
    apply in_domain_in_g in H7.
    destruct H7 as [f1 [t1 IN]].
    apply removeEntry_in with
        x f1 t1 n g2 in PNEQ.
    apply in_g_in_domain in PNEQ; intuition.
    apply in_domain_in_g in H7.     
    destruct H7 as [f2 [t2 IN2]].
    apply in_removeEntry in IN2.
    apply in_g_in_domain in IN2...
    assumption.
    case_eq (pair_eq x n).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    apply in_g_in_domain in H2...
    intros PNEQ. rewrite <-pairEq_neq in PNEQ.
    apply in_domain_in_g in H7.
    destruct H7 as [f1 [t1 IN]].
    apply removeEntry_in with
        x f1 t1 n g3 in PNEQ.
    apply in_g_in_domain in PNEQ; intuition.
    apply in_domain_in_g in H7.     
    destruct H7 as [f2 [t2 IN2]].
    apply in_removeEntry in IN2.
    apply in_g_in_domain in IN2...
    assumption.
  - intuition.
    subst g'''.
    case_eq (pair_eq x n).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    inversion H4...
    apply in_g_in_domain in H2...
    intros PNEQ. rewrite <-pairEq_neq in PNEQ.
    apply in_domain_in_g in H7.
    destruct H7 as [f1 [t1 IN]].
    apply removeEntry_in with
        x f1 t1 n g2 in PNEQ.
    apply in_g_in_domain in PNEQ; intuition.
    apply in_domain_in_g in H2.     
    destruct H2 as [f2 [t2 IN2]].
    apply in_removeEntry in IN2.
    apply in_g_in_domain in IN2...
    assumption.
    case_eq (pair_eq x n).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    apply in_g_in_domain in H1...
    intros PNEQ. rewrite <-pairEq_neq in PNEQ.
    apply in_domain_in_g in H7.
    destruct H7 as [f1 [t1 IN]].
    subst g'''.
    apply removeEntry_in with
        x f1 t1 n g3 in PNEQ.
    apply in_g_in_domain in PNEQ; intuition.
    apply in_domain_in_g in H2.     
    destruct H2 as [f2 [t2 IN2]].
    apply in_removeEntry in IN2.
    apply in_g_in_domain in IN2...
    assumption.
  -  intuition. subst g'''.
     case_eq (pair_eq x n).
     intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
     inversion H4...
     apply in_g_in_domain in H2...
     intros PNEQ. rewrite <-pairEq_neq in PNEQ.
     apply in_domain_in_g in H7.
     destruct H7 as [f1 [t1 IN]].
     apply removeEntry_in with
         x f1 t1 n g2 in PNEQ.
     apply in_g_in_domain in PNEQ; intuition.
     apply in_domain_in_g in H2.     
     destruct H2 as [f2 [t2 IN2]].
     apply in_removeEntry in IN2.
     apply in_g_in_domain in IN2...
     assumption.
     case_eq (pair_eq x n).
     intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
     apply in_g_in_domain in H1...
     intros PNEQ. rewrite <-pairEq_neq in PNEQ.
     apply in_domain_in_g in H7.
     destruct H7 as [f1 [t1 IN]].
     subst g'''.
     apply removeEntry_in with
         x f1 t1 n g3 in PNEQ.
     apply in_g_in_domain in PNEQ; intuition.
     apply in_domain_in_g in H2.     
     destruct H2 as [f2 [t2 IN2]].
     apply in_removeEntry in IN2.
     apply in_g_in_domain in IN2...
     assumption.
Qed.

Lemma split_domain_m:
  forall g1 g2 g pf1 pf2 pf x,
    tEnv_split g1 g2 g pf1 pf2 pf ->
    In x (domain g1) <-> In x (domain g2).
Proof.
  intros.
  apply split_domain_l with (x := x) in H as K.
  apply split_domain_r with (x := x) in H as K1.
  intuition.
Qed.

Lemma split_domain_l_2:
  forall g1 g2 g pf1 pf2 pf,
    tEnv_split g1 g2 g pf1 pf2 pf ->
    forall x, In x (domain g1) <-> In x (domain g).
Proof.
  intros.
  apply split_domain_l with (x := x) in H.
  assumption.
Qed.

Lemma split_exists_neutral :
  forall g pf (nd_pf : NoDup(domain g)),
  exists neutral pfn (nd_pfn : NoDup (domain neutral)),
    tEnv_split g neutral g pf pfn pf.
Proof with eauto.
  intros.
  induction g.
  exists nil.
  exists pf.
  exists nd_pf.
  apply SpNil; tauto.
  remember pf as pf1; subst pf.
  assert (pf := pf1).
  apply isMap_cons in pf.
  specialize IHg with pf.
  apply no_dup_domain_cons in nd_pf as IHg2.
  apply IHg in IHg2. clear IHg.
  destruct IHg2 as [neutral [pfn [nd_pfn TSPLIT]]].
  destruct a.
  destruct p as [a f].
  remember p0 as t; subst p0.
  destruct t.
  - destruct m.
    + destruct f.
      * specialize Fp_hi as H.
        remember ((a, hid, Chan lin p t) :: g) as g1.
        remember ((a, ill, Chan lin empty t) :: neutral) as neutral2.
        exists neutral2.
        
        rewrite Heqg1 in nd_pf.
        assert (nd_pff := nd_pf).
        apply split_head_map
          with (g1 := g) (g2 := neutral) (g := g) (pf1 := pf) (pf2 := pfn)
               (pf := pf)
               (a := a) (f := hid) (t := Chan lin p t)
               (f1 := ill) (t1 := Chan lin empty t)
          in nd_pff as pfn0.
        subst neutral2.
        exists pfn0.
        remember ((a, ill, Chan lin empty t) :: neutral) as neutral2.
        specialize SpLin with
            (n := a)  (f := hid) (g := ill) (f' := hid)
            (g1 := g1)
            (pf1 := pf1)
            (g2 := neutral2)
            (pf2 := pfn0)
            (g3 := g1)
            (pf3 := pf1)
            (g''' := g)
          as TSPLIT2.
        rewrite <-Heqg1 in nd_pf.
        specialize removeEntry_head with
            a hid (Chan lin p t) g as H0.
        specialize removeEntry_head with
            a ill (Chan lin empty t) neutral as H1.
        revert dependent TSPLIT2.
        subst g1 neutral2. 
        rewrite H0. rewrite H1.
        
        intros.
        remember ((a, hid, Chan lin p t) :: g) as g1.
        remember ((a, ill, Chan lin empty t) :: neutral)
          as neutral2.
        specialize TSPLIT2 with
            (pf' := pf) (pf'' := pfn)  (pf''' := pf)
            (p := p) (q := empty) (p' := p) (t := t).
        apply TSPLIT2 in H. clear TSPLIT2.

        assert (pfn2 : NoDup (domain neutral2)).
        rewrite Heqneutral2.
        unfold domain; fold domain.
        apply NoDup_cons.
        intro.
        apply split_domain_m with (x := a) in TSPLIT as IFF.
        apply IFF in H2 as ABS.
        assert (nd_pf2 := nd_pf).
        rewrite  Heqg1 in nd_pf2.
        unfold domain in nd_pf2; fold domain in nd_pf2.
        inversion nd_pf2. subst.
        contradiction.
        eauto.
        exists pfn2.
        
        assumption.
        apply Pp_emptyR.
        subst; intuition.
        subst; intuition.
        assumption.
        tauto.
        assert (Fa : In ((a, hid, Chan lin p t)) g1).
        subst; intuition.
        apply F_Entry in Fa; assumption.
        assert (Ta : In ((a, hid, Chan lin p t)) g1).
        subst; intuition.
        apply T_Entry in Ta; assumption.
        all:assumption.
      * specialize Fp_ii as H.
        remember ((a, ill, Chan lin p t) :: g) as g1.
        remember ((a, ill, Chan lin empty t) :: neutral) as neutral2.
        exists neutral2.
        
        rewrite Heqg1 in nd_pf.
        assert (nd_pff := nd_pf).
        apply split_head_map
          with (g1 := g) (g2 := neutral) (g := g) (pf1 := pf) (pf2 := pfn)
               (pf := pf)
               (a := a) (f := ill) (t := Chan lin p t)
               (f1 := ill) (t1 := Chan lin empty t)
          in nd_pff as pfn0.
        subst neutral2.
        exists pfn0.
        remember ((a, ill, Chan lin empty t) :: neutral) as neutral2.
        specialize SpLin with
            (n := a)  (f := ill) (g := ill) (f' := ill)
            (g1 := g1)
            (pf1 := pf1)
            (g2 := neutral2)
            (pf2 := pfn0)
            (g3 := g1)
            (pf3 := pf1)
            (g''' := g)
          as TSPLIT2.
        rewrite <-Heqg1 in nd_pf.
        specialize removeEntry_head with
            a ill (Chan lin p t) g as H0.
        specialize removeEntry_head with
            a ill (Chan lin empty t) neutral as H1.
        revert dependent TSPLIT2.
        subst g1 neutral2. 
        rewrite H0. rewrite H1.
        
        intros.
        remember ((a, ill, Chan lin p t) :: g) as g1.
        remember ((a, ill, Chan lin empty t) :: neutral)
          as neutral2.
        specialize TSPLIT2 with
            (pf' := pf) (pf'' := pfn)  (pf''' := pf)
            (p := p) (q := empty) (p' := p) (t := t).
        apply TSPLIT2 in H. clear TSPLIT2.

        assert (pfn2 : NoDup (domain neutral2)).
        rewrite Heqneutral2.
        unfold domain; fold domain.
        apply NoDup_cons.
        intro.
        apply split_domain_m with (x := a) in TSPLIT as IFF.
        apply IFF in H2 as ABS.
        assert (nd_pf2 := nd_pf).
        rewrite  Heqg1 in nd_pf2.
        unfold domain in nd_pf2; fold domain in nd_pf2.
        inversion nd_pf2. subst.
        contradiction.
        eauto.
        exists pfn2.
        
        assumption.
        apply Pp_emptyR.
        subst; intuition.
        subst; intuition.
        assumption.
        tauto.
        assert (Fa : In ((a, ill, Chan lin p t)) g1).
        subst; intuition.
        apply F_Entry in Fa; assumption.
        assert (Ta : In ((a, ill, Chan lin p t)) g1).
        subst; intuition.
        apply T_Entry in Ta; assumption.
        all:assumption.
      * specialize Fp_vv as H.
        remember ((a, vis, Chan lin p t) :: g) as g1.
        remember ((a, vis, Chan lin empty t) :: neutral) as neutral2.
        exists neutral2.
        
        rewrite Heqg1 in nd_pf.
        assert (nd_pff := nd_pf).
        apply split_head_map
          with (g1 := g) (g2 := neutral) (g := g) (pf1 := pf) (pf2 := pfn)
               (pf := pf)
               (a := a) (f := vis) (t := Chan lin p t)
               (f1 := vis) (t1 := Chan lin empty t)
          in nd_pff as pfn0.
        subst neutral2.
        exists pfn0.
        remember ((a, vis, Chan lin empty t) :: neutral) as neutral2.
        specialize SpLin with
            (n := a)  (f := vis) (g := vis) (f' := vis)
            (g1 := g1)
            (pf1 := pf1)
            (g2 := neutral2)
            (pf2 := pfn0)
            (g3 := g1)
            (pf3 := pf1)
            (g''' := g)
          as TSPLIT2.
        rewrite <-Heqg1 in nd_pf.
        specialize removeEntry_head with
            a vis (Chan lin p t) g as H0.
        specialize removeEntry_head with
            a vis (Chan lin empty t) neutral as H1.
        revert dependent TSPLIT2.
        subst g1 neutral2. 
        rewrite H0. rewrite H1.
        
        intros.
        remember ((a, vis, Chan lin p t) :: g) as g1.
        remember ((a, vis, Chan lin empty t) :: neutral)
          as neutral2.
        specialize TSPLIT2 with
            (pf' := pf) (pf'' := pfn)  (pf''' := pf)
            (p := p) (q := empty) (p' := p) (t := t).
        apply TSPLIT2 in H. clear TSPLIT2.

         assert (pfn2 : NoDup (domain neutral2)).
        rewrite Heqneutral2.
        unfold domain; fold domain.
        apply NoDup_cons.
        intro.
        apply split_domain_m with (x := a) in TSPLIT as IFF.
        apply IFF in H2 as ABS.
        assert (nd_pf2 := nd_pf).
        rewrite  Heqg1 in nd_pf2.
        unfold domain in nd_pf2; fold domain in nd_pf2.
        inversion nd_pf2. subst.
        contradiction.
        eauto.
        exists pfn2.
        
        assumption.
        apply Pp_emptyR.
        subst; intuition.
        subst; intuition.
        assumption.
        tauto.
        assert (Fa : In ((a, vis, Chan lin p t)) g1).
        subst; intuition.
        apply F_Entry in Fa; assumption.
        assert (Ta : In ((a, vis, Chan lin p t)) g1).
        subst; intuition.
        apply T_Entry in Ta; assumption.
        all:assumption.
    + destruct f.
      * specialize Fp_hi as H.
        remember ((a, hid, Chan un p t) :: g) as g1.
        remember ((a, ill, Chan un p t) :: neutral) as neutral2.
        exists neutral2.
        
        rewrite Heqg1 in nd_pf.
        assert (nd_pff := nd_pf).
        apply split_head_map
          with (g1 := g) (g2 := neutral) (g := g) (pf1 := pf) (pf2 := pfn)
               (pf := pf)
               (a := a) (f := hid) (t := Chan un p t)
               (f1 := ill) (t1 := Chan un p t)
          in nd_pff as pfn0.
        subst neutral2.
        exists pfn0.
        remember ((a, ill, Chan un p t) :: neutral) as neutral2.
        specialize SpUn with
            (n := a)  (f := hid) (g := ill) (f' := hid)
            (g1 := g1)
            (pf1 := pf1)
            (g2 := neutral2)
            (pf2 := pfn0)
            (g3 := g1)
            (pf3 := pf1)
            (g''' := g)
          as TSPLIT2.
        rewrite <-Heqg1 in nd_pf.
        specialize removeEntry_head with
            a hid (Chan un p t) g as H0.
        specialize removeEntry_head with
            a ill (Chan un p t) neutral as H1.
        revert dependent TSPLIT2.
        subst g1 neutral2. 
        rewrite H0. rewrite H1.
        
        intros.
        remember ((a, hid, Chan un p t) :: g) as g1.
        remember ((a, ill, Chan un p t) :: neutral)
          as neutral2.
        specialize TSPLIT2 with
            (pf' := pf) (pf'' := pfn)  (pf''' := pf)
            (p := p) (t := t).
        apply TSPLIT2 in H. clear TSPLIT2.

         assert (pfn2 : NoDup (domain neutral2)).
        rewrite Heqneutral2.
        unfold domain; fold domain.
        apply NoDup_cons.
        intro.
        apply split_domain_m with (x := a) in TSPLIT as IFF.
        apply IFF in H2 as ABS.
        assert (nd_pf2 := nd_pf).
        rewrite  Heqg1 in nd_pf2.
        unfold domain in nd_pf2; fold domain in nd_pf2.
        inversion nd_pf2. subst.
        contradiction.
        eauto.
        exists pfn2.
        
        assumption.
        subst; intuition.
        subst; intuition.
        assumption.
        tauto.
        assert (Fa : In ((a, hid, Chan un p t)) g1).
        subst; intuition.
        apply F_Entry in Fa; assumption.
        assert (Ta : In ((a, hid, Chan un p t)) g1).
        subst; intuition.
        apply T_Entry in Ta; assumption.
        all:assumption.
      * specialize Fp_ii as H.
        remember ((a, ill, Chan un p t) :: g) as g1.
        remember ((a, ill, Chan un p t) :: neutral) as neutral2.
        exists neutral2.
        
        rewrite Heqg1 in nd_pf.
        assert (nd_pff := nd_pf).
        apply split_head_map
          with (g1 := g) (g2 := neutral) (g := g) (pf1 := pf) (pf2 := pfn)
               (pf := pf)
               (a := a) (f := ill) (t := Chan un p t)
               (f1 := ill) (t1 := Chan un p t)
          in nd_pff as pfn0.
        subst neutral2.
        exists pfn0.
        remember ((a, ill, Chan un p t) :: neutral) as neutral2.
        specialize SpUn with
            (n := a)  (f := ill) (g := ill) (f' := ill)
            (g1 := g1)
            (pf1 := pf1)
            (g2 := neutral2)
            (pf2 := pfn0)
            (g3 := g1)
            (pf3 := pf1)
            (g''' := g)
          as TSPLIT2.
        rewrite <-Heqg1 in nd_pf.
        specialize removeEntry_head with
            a ill (Chan un p t) g as H0.
        specialize removeEntry_head with
            a ill (Chan un p t) neutral as H1.
        revert dependent TSPLIT2.
        subst g1 neutral2. 
        rewrite H0. rewrite H1.
        
        intros.
        remember ((a, ill, Chan un p t) :: g) as g1.
        remember ((a, ill, Chan un p t) :: neutral)
          as neutral2.
        specialize TSPLIT2 with
            (pf' := pf) (pf'' := pfn)  (pf''' := pf)
            (p := p) (t := t).
        apply TSPLIT2 in H. clear TSPLIT2.

         assert (pfn2 : NoDup (domain neutral2)).
        rewrite Heqneutral2.
        unfold domain; fold domain.
        apply NoDup_cons.
        intro.
        apply split_domain_m with (x := a) in TSPLIT as IFF.
        apply IFF in H2 as ABS.
        assert (nd_pf2 := nd_pf).
        rewrite  Heqg1 in nd_pf2.
        unfold domain in nd_pf2; fold domain in nd_pf2.
        inversion nd_pf2. subst.
        contradiction.
        eauto.
        exists pfn2.
        
        assumption.
        subst; intuition.
        subst; intuition.
        assumption.
        tauto.
        assert (Fa : In ((a, ill, Chan un p t)) g1).
        subst; intuition.
        apply F_Entry in Fa; assumption.
        assert (Ta : In ((a, ill, Chan un p t)) g1).
        subst; intuition.
        apply T_Entry in Ta; assumption.
        all:assumption.
      * specialize Fp_vv as H.
        remember ((a, vis, Chan un p t) :: g) as g1.
        remember ((a, vis, Chan un p t) :: neutral) as neutral2.
        exists neutral2.
        
        rewrite Heqg1 in nd_pf.
        assert (nd_pff := nd_pf).
        apply split_head_map
          with (g1 := g) (g2 := neutral) (g := g) (pf1 := pf) (pf2 := pfn)
               (pf := pf)
               (a := a) (f := vis) (t := Chan un p t)
               (f1 := vis) (t1 := Chan un p t)
          in nd_pff as pfn0.
        subst neutral2.
        exists pfn0.
        remember ((a, vis, Chan un p t) :: neutral) as neutral2.
        specialize SpUn with
            (n := a)  (f := vis) (g := vis) (f' := vis)
            (g1 := g1)
            (pf1 := pf1)
            (g2 := neutral2)
            (pf2 := pfn0)
            (g3 := g1)
            (pf3 := pf1)
            (g''' := g)
          as TSPLIT2.
        rewrite <-Heqg1 in nd_pf.
        specialize removeEntry_head with
            a vis (Chan un p t) g as H0.
        specialize removeEntry_head with
            a vis (Chan un p t) neutral as H1.
        revert dependent TSPLIT2.
        subst g1 neutral2. 
        rewrite H0. rewrite H1.
        
        intros.
        remember ((a, vis, Chan un p t) :: g) as g1.
        remember ((a, vis, Chan un p t) :: neutral)
          as neutral2.
        specialize TSPLIT2 with
            (pf' := pf) (pf'' := pfn)  (pf''' := pf)
            (p := p) (t := t).
        apply TSPLIT2 in H. clear TSPLIT2.

         assert (pfn2 : NoDup (domain neutral2)).
        rewrite Heqneutral2.
        unfold domain; fold domain.
        apply NoDup_cons.
        intro.
        apply split_domain_m with (x := a) in TSPLIT as IFF.
        apply IFF in H2 as ABS.
        assert (nd_pf2 := nd_pf).
        rewrite  Heqg1 in nd_pf2.
        unfold domain in nd_pf2; fold domain in nd_pf2.
        inversion nd_pf2. subst.
        contradiction.
        eauto.
        exists pfn2.
        
        assumption.
        subst; intuition.
        subst; intuition.
        assumption.
        tauto.
        assert (Fa : In ((a, vis, Chan un p t)) g1).
        subst; intuition.
        apply F_Entry in Fa; assumption.
        assert (Ta : In ((a, vis, Chan un p t)) g1).
        subst; intuition.
        apply T_Entry in Ta; assumption.
        all:assumption.      
  -
    destruct f.
    * specialize Fp_hi as H.
      remember ((a, hid, Top) :: g) as g1.
      remember ((a, ill, Top) :: neutral) as neutral2.
      exists neutral2.
      (* EXISTS pfn0 *)
      assert (pfn0: isMap neutral2).
      assert (pfn2 := pfn).
      apply cons_isMap
        with a ill Top neutral in pfn2.
      rewrite Heqneutral2; assumption. clear pfn2.
      unfold not; intros ABS; destruct ABS as [f [t ABS]].
      apply split_not_in_not_ex with
          g neutral g pf pfn pf a
        in TSPLIT as ABS2.
      elim ABS2; exists f; exists t; assumption.
      rewrite Heqg1 in nd_pf.
      apply no_dup_domain_not_exists in nd_pf.
      unfold not; intuition.
      elim nd_pf; intuition.
      (* END OF SUBPROOF *)
      exists pfn0.
      specialize SpTop with
          (n := a)  (f := hid) (g := ill) (f' := hid)
          (g1 := g1)
          (pf1 := pf1)
          (g2 := neutral2)
          (pf2 := pfn0)
          (g3 := g1)
          (pf3 := pf1)
          (g''' := g)
        as TSPLIT2.
      specialize removeEntry_head with a hid Top g as H0.
      rewrite <-Heqg1 in H0.
      specialize removeEntry_head with a ill Top neutral as H1.
      rewrite <-Heqneutral2 in H1.
      revert dependent TSPLIT2.
      rewrite H0. rewrite H1.
      intros.
      specialize TSPLIT2 with
          (pf' := pf) (pf'' := pfn)  (pf''' := pf).
      apply TSPLIT2 in H. clear TSPLIT2.

       assert (pfn2 : NoDup (domain neutral2)).
        rewrite Heqneutral2.
        unfold domain; fold domain.
        apply NoDup_cons.
        intro.
        apply split_domain_m with (x := a) in TSPLIT as IFF.
        apply IFF in H2 as ABS.
        assert (nd_pf2 := nd_pf).
        rewrite  Heqg1 in nd_pf2.
        unfold domain in nd_pf2; fold domain in nd_pf2.
        inversion nd_pf2. subst.
        contradiction.
        eauto.
        exists pfn2.
        
      assumption.
      subst; intuition.
      subst; intuition.
      assumption.
      tauto.
      assert (Fa : In ((a, hid, Top)) g1).
      subst; intuition.
      apply F_Entry in Fa; assumption.
      assert (Ta : In ((a, hid, Top)) g1).
      subst; intuition.
      apply T_Entry in Ta; assumption.
    * specialize Fp_ii as H.
      remember ((a, ill, Top) :: g) as g1.
      remember ((a, ill, Top) :: neutral) as neutral2.
      exists neutral2.
      (* EXISTS pfn0 *)
      assert (pfn0: isMap neutral2).
      assert (pfn2 := pfn).
      apply cons_isMap
        with a ill Top neutral in pfn2.
      rewrite Heqneutral2; assumption. clear pfn2.
      unfold not; intros ABS; destruct ABS as [f [t ABS]].
      apply split_not_in_not_ex with
          g neutral g pf pfn pf a 
        in TSPLIT as ABS2.
      elim ABS2; exists f; exists t; assumption.
      rewrite Heqg1 in nd_pf.
      apply no_dup_domain_not_exists in nd_pf.
      unfold not; intuition.
      elim nd_pf; intuition. 
      (* END OF SUBPROOF *)
      exists pfn0.
      specialize SpTop with
          (n := a)  (f := ill) (g := ill) (f' := ill)
          (g1 := g1)
          (pf1 := pf1)
          (g2 := neutral2)
          (pf2 := pfn0)
          (g3 := g1)
          (pf3 := pf1)
          (g''' := g)
        as TSPLIT2.
      specialize removeEntry_head with a ill Top g as H0.
      rewrite <-Heqg1 in H0.
      specialize removeEntry_head with a ill Top neutral as H1.
      rewrite <-Heqneutral2 in H1.
      revert dependent TSPLIT2.
      rewrite H0. rewrite H1.
      intros.
      specialize TSPLIT2 with
          (pf' := pf) (pf'' := pfn)  (pf''' := pf).
      apply TSPLIT2 in H. clear TSPLIT2.

       assert (pfn2 : NoDup (domain neutral2)).
        rewrite Heqneutral2.
        unfold domain; fold domain.
        apply NoDup_cons.
        intro.
        apply split_domain_m with (x := a) in TSPLIT as IFF.
        apply IFF in H2 as ABS.
        assert (nd_pf2 := nd_pf).
        rewrite  Heqg1 in nd_pf2.
        unfold domain in nd_pf2; fold domain in nd_pf2.
        inversion nd_pf2. subst.
        contradiction.
        eauto.
        exists pfn2.
      
      assumption.
      subst; intuition.
      subst; intuition.
      assumption.
      tauto.
      assert (Fa : In ((a, ill, Top)) g1).
      subst; intuition.
      apply F_Entry in Fa; assumption.
      assert (Ta : In ((a, ill, Top)) g1).
      subst; intuition.
      apply T_Entry in Ta; assumption.
    * specialize Fp_vv as H.
      remember ((a, vis, Top) :: g) as g1.
      remember ((a, vis, Top) :: neutral) as neutral2.
      exists neutral2.
      (* EXISTS pfn0 *)
      assert (pfn0: isMap neutral2).
      assert (pfn2 := pfn).
      apply cons_isMap
        with a vis Top neutral in pfn2.
      rewrite Heqneutral2; assumption. clear pfn2.
      unfold not; intros ABS; destruct ABS as [f [t ABS]].
      apply split_not_in_not_ex with
          g neutral g pf pfn pf a
        in TSPLIT as ABS2.
      elim ABS2; exists f; exists t; assumption.
      rewrite Heqg1 in nd_pf.
      apply no_dup_domain_not_exists in nd_pf.
      unfold not; intuition.
      elim nd_pf; intuition. 
      (* END OF SUBPROOF *)
      exists pfn0.
      specialize SpTop with
          (n := a)  (f := vis) (g := vis) (f' := vis)
          (g1 := g1)
          (pf1 := pf1)
          (g2 := neutral2)
          (pf2 := pfn0)
          (g3 := g1)
          (pf3 := pf1)
          (g''' := g)
        as TSPLIT2.
      specialize removeEntry_head with a vis Top g as H0.
      rewrite <-Heqg1 in H0.
      specialize removeEntry_head with a vis Top neutral as H1.
      rewrite <-Heqneutral2 in H1.
      revert dependent TSPLIT2.
      rewrite H0. rewrite H1.
      intros.
      specialize TSPLIT2 with
          (pf' := pf) (pf'' := pfn)  (pf''' := pf).
      apply TSPLIT2 in H. clear TSPLIT2.

       assert (pfn2 : NoDup (domain neutral2)).
        rewrite Heqneutral2.
        unfold domain; fold domain.
        apply NoDup_cons.
        intro.
        apply split_domain_m with (x := a) in TSPLIT as IFF.
        apply IFF in H2 as ABS.
        assert (nd_pf2 := nd_pf).
        rewrite  Heqg1 in nd_pf2.
        unfold domain in nd_pf2; fold domain in nd_pf2.
        inversion nd_pf2. subst.
        contradiction.
        eauto.
        exists pfn2.
        
      assumption.
      subst; intuition.
      subst; intuition.
      assumption.
      tauto.
      assert (Fa : In ((a, vis, Top)) g1).
      subst; intuition.
      apply F_Entry in Fa; assumption.
      assert (Ta : In ((a, vis, Top)) g1).
      subst; intuition.
      apply T_Entry in Ta; assumption.
Qed.