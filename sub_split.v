Require Import
        Bool List Lia PeanoNat Program.Equality
        RemoveEntry Domain ListAddOns
        header
        operations pi_syntax
        pairEq type_system semantics
        disjoint_newEntries
        type_operations_1
        split_exists_neutral.

#[global] Hint Constructors piType.
#[global] Hint Resolve Pp_emptyL.
#[global] Hint Resolve Pp_emptyR.
#[global] Hint Resolve Pp_inpL.
#[global] Hint Resolve Pp_inpR.
#[global] Hint Resolve Tp_Base.
#[global] Hint Resolve Tp_LinPlus.
#[global] Hint Resolve Tp_UnPlus.
#[global] Hint Resolve T_Entry.
#[global] Hint Resolve F_Entry.
#[global] Hint Resolve type_plus_comm.
#[global] Hint Resolve type_of_map.
#[global] Hint Resolve flag_of_map.
#[global] Hint Resolve isMap_cons.
#[global] Hint Resolve cons_isMap.
#[global] Hint Resolve removeEntry_head.
#[global] Hint Resolve in_removeEntry.
#[global] Hint Resolve split_in_ex.
#[global] Hint Resolve split_in_ex_2.
#[global] Hint Resolve split_exists_neutral.

Lemma tsub_un :
  forall g1 g2 g pf1 pf2 pf a1 a2 f p t,
    In (a1, a2, f, Chan un p t) g1 ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    typeOf g (a1, a2) (Chan un p t).
Proof.
  intros g1 g2 g pf1 pf2 pf a1 a2 f p t IN TSPLIT.
  generalize dependent a1.
  generalize dependent a2.
  generalize dependent f. 
  generalize dependent p.
  generalize dependent t.
  dependent induction TSPLIT.
  - intros; subst; inversion IN.
  - intros.
    specialize IHTSPLIT with t0 p0 f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf1).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply type_of_map with
        g1 (a1, a2) (Chan un p0 t0) (Chan lin p t) in TYP.
    inversion TYP.
    assumption.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan un p0 t0) n  g1 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H3.
    apply T_Entry in H3; assumption.
    assumption.
  - intros. 
    specialize IHTSPLIT with t0 p0 f0 a2 a1.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf1).
    apply type_of_map with
        g1 (a1, a2) (Chan un p t) (Chan un p0 t0) in TYP.
    inversion TYP; subst. clear TYP IN.
    assumption.
    apply T_Entry in H0; assumption.
    apply T_Entry in IN; assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    subst g'''.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan un p0 t0) n  g1 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H2.
    apply T_Entry in H2; assumption.
    assumption.
  - intros. 
    specialize IHTSPLIT with t p f0 a2 a1.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf1).
    apply type_of_map with
        g1 (a1, a2) (Chan un p t) Top in TYP.
    inversion TYP.
    apply T_Entry in IN; assumption.
    apply T_Entry in H0; assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan un p t) n  g1 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H5.
    apply T_Entry in H5; assumption.
    assumption.
Qed.

Lemma tsub_un_r :
  forall g1 g2 g pf1 pf2 pf a1 a2 f p t,
    In (a1, a2, f, Chan un p t) g2 ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    typeOf g (a1, a2) (Chan un p t).
Proof.
  intros g1 g2 g pf1 pf2 pf a1 a2 f p t IN TSPLIT.
  generalize dependent a1.
  generalize dependent a2.
  generalize dependent f. 
  generalize dependent p.
  generalize dependent t.
  dependent induction TSPLIT.
  - intros; subst; inversion IN.
  - intros.
    specialize IHTSPLIT with t0 p0 f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf2).
    apply T_Entry in H2.
    apply T_Entry in IN.
    apply type_of_map with
        g2 (a1, a2) (Chan un p0 t0) (Chan lin q t) in TYP.
    inversion TYP.
    assumption.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan un p0 t0) n  g2 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H3.
    apply T_Entry in H3; assumption.
    assumption.
  - intros. 
    specialize IHTSPLIT with t0 p0 f0 a2 a1.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf2).
    apply type_of_map with
        g2 (a1, a2) (Chan un p t) (Chan un p0 t0) in TYP.
    inversion TYP; subst. clear TYP IN.
    assumption.
    apply T_Entry in H1; assumption.
    apply T_Entry in IN; assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    subst g'''.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan un p0 t0) n  g2 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H2.
    apply T_Entry in H2; assumption.
    assumption.
  - intros. 
    specialize IHTSPLIT with t p f0 a2 a1.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf2).
    apply type_of_map with
        g2 (a1, a2) (Chan un p t) Top in TYP.
    inversion TYP.
    apply T_Entry in IN; assumption.
    apply T_Entry in H1; assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan un p t) n  g2 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H5.
    apply T_Entry in H5; assumption.
    assumption.
Qed.

Lemma tsub_in :
  forall g1 g2 g pf1 pf2 pf a1 a2 f m t,
    In (a1, a2, f, Chan m inp t) g1 ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    (typeOf g (a1, a2) (Chan m inp t) \/
     typeOf g (a1, a2) (Chan m io t)).
Proof.
  intros g1 g2 g pf1 pf2 pf a1 a2 f m t IN TSPLIT.
  generalize dependent a1.
  generalize dependent a2.
  generalize dependent f. 
  generalize dependent m.
  generalize dependent t.
  dependent induction TSPLIT.
  - intros; subst; inversion IN.
  - intros.
    specialize IHTSPLIT with t0 m f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf1).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply type_of_map with
        g1 (a1, a2) (Chan lin p t) (Chan m inp t0) in TYP.
    inversion TYP; subst. clear TYP IN.
    inversion H0; subst; auto.
    assumption.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m inp t0) n  g1 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [PINP | PIO].
    + left.
      inversion PINP.
      apply T_Entry with (f := f1).
      apply in_removeEntry in H3.
      assumption.
    + right.
      inversion PIO.
      apply T_Entry with (f := f1).
      apply in_removeEntry in H3.
      assumption.
    + assumption.
  - intros.
    specialize IHTSPLIT with t0 m f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf1).
    apply T_Entry in H0.
    apply T_Entry in IN.
    apply type_of_map with
        g1 (a1, a2) (Chan un p t) (Chan m inp t0) in TYP.
    inversion TYP; subst. clear TYP IN.
    inversion H0; subst; auto.
    assumption.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m inp t0) n  g1 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [PINP | PIO].
    + left.
      inversion PINP.
      apply T_Entry with (f := f1).
      apply in_removeEntry in H2.
      assumption.
    + right.
      inversion PIO.
      apply T_Entry with (f := f1).
      apply in_removeEntry in H2.
      assumption.
    + assumption.
  - intros.
    specialize IHTSPLIT with t m f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf1).
    apply T_Entry in H0.
    apply T_Entry in IN.
    apply type_of_map with
        g1 (a1, a2) Top (Chan m inp t) in TYP.
    inversion TYP; subst. clear TYP IN.
    inversion H0; subst; auto.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m inp t) n  g1 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [PINP | PIO].
    + left.
      inversion PINP.
      apply T_Entry with (f := f1).
      apply in_removeEntry in H2.
      assumption.
    + right.
      inversion PIO.
      apply T_Entry with (f := f1).
      apply in_removeEntry in H2.
      assumption.
    + assumption.
Qed.

Lemma tsub_in_r :
  forall g1 g2 g pf1 pf2 pf a1 a2 f m t,
    In (a1, a2, f, Chan m inp t) g2 ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    (typeOf g (a1, a2) (Chan m inp t) \/
     typeOf g (a1, a2) (Chan m io t)).
Proof.
  intros g1 g2 g pf1 pf2 pf a1 a2 f m t IN TSPLIT.
  generalize dependent a1.
  generalize dependent a2.
  generalize dependent f. 
  generalize dependent m.
  generalize dependent t.
  dependent induction TSPLIT.
  - intros; subst; inversion IN.
  - intros.
    specialize IHTSPLIT with t0 m f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf2).
    apply T_Entry in H2.
    apply T_Entry in IN.
    apply type_of_map with
        g2 (a1, a2) (Chan lin q t) (Chan m inp t0) in TYP.
    inversion TYP; subst. clear TYP IN.
    inversion H0; subst; auto.
    assumption.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m inp t0) n  g2 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [PINP | PIO].
    + left.
      inversion PINP.
      apply T_Entry with (f := f1).
      apply in_removeEntry in H3.
      assumption.
    + right.
      inversion PIO.
      apply T_Entry with (f := f1).
      apply in_removeEntry in H3.
      assumption.
    + assumption.
  - intros.
    specialize IHTSPLIT with t0 m f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf2).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply type_of_map with
        g2 (a1, a2) (Chan un p t) (Chan m inp t0) in TYP.
    inversion TYP; subst. clear TYP IN.
    inversion H1; subst; auto.
    assumption.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m inp t0) n  g2 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [PINP | PIO].
    + left.
      inversion PINP.
      apply T_Entry with (f := f1).
      apply in_removeEntry in H2.
      assumption.
    + right.
      inversion PIO.
      apply T_Entry with (f := f1).
      apply in_removeEntry in H2.
      assumption.
    + assumption.
  - intros.
    specialize IHTSPLIT with t m f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf2).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply type_of_map with
        g2 (a1, a2) Top (Chan m inp t) in TYP.
    inversion TYP; subst. clear TYP IN.
    inversion H1; subst; auto.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m inp t) n  g2 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [PINP | PIO].
    + left.
      inversion PINP.
      apply T_Entry with (f := f1).
      apply in_removeEntry in H2.
      assumption.
    + right.
      inversion PIO.
      apply T_Entry with (f := f1).
      apply in_removeEntry in H2.
      assumption.
    + assumption.
Qed.

Lemma tsub_out :
  forall g1 g2 g pf1 pf2 pf a1 a2 f m t,
    In (a1, a2, f, Chan m out t) g1 ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    (typeOf g (a1, a2) (Chan m out t) \/
     typeOf g (a1, a2) (Chan m io t)).
Proof.
  intros g1 g2 g pf1 pf2 pf a1 a2 f m t IN TSPLIT.
  generalize dependent a1.
  generalize dependent a2.
  generalize dependent f. 
  generalize dependent m.
  generalize dependent t.
  dependent induction TSPLIT.
  - intros; subst; inversion IN.
  - intros.
    specialize IHTSPLIT with t0 m f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf1).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply type_of_map with
        g1 (a1, a2) (Chan lin p t) (Chan m out t0) in TYP.
    inversion TYP; subst. clear TYP IN.
    inversion H0; subst; auto.
    assumption.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m out t0) n  g1 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [POUT | PIO].
    + left.
      inversion POUT.
      apply T_Entry with (f := f1).
      apply in_removeEntry in H3.
      assumption.
    + right.
      inversion PIO.
      apply T_Entry with (f := f1).
      apply in_removeEntry in H3.
      assumption.
    + assumption.
  - intros.
    specialize IHTSPLIT with t0 m f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf1).
    apply T_Entry in H0.
    apply T_Entry in IN.
    apply type_of_map with
        g1 (a1, a2) (Chan un p t) (Chan m out t0) in TYP.
    inversion TYP; subst. clear TYP IN.
    inversion H0; subst; auto.
    assumption.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m out t0) n  g1 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [POUT | PIO].
    + left.
      inversion POUT.
      apply T_Entry with (f := f1).
      apply in_removeEntry in H2.
      assumption.
    + right.
      inversion PIO.
      apply T_Entry with (f := f1).
      apply in_removeEntry in H2.
      assumption.
    + assumption.
  - intros.
    specialize IHTSPLIT with t m f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf1).
    apply T_Entry in H0.
    apply T_Entry in IN.
    apply type_of_map with
        g1 (a1, a2) Top (Chan m out t) in TYP.
    inversion TYP; subst. clear TYP IN.
    inversion H0; subst; auto.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m out t) n  g1 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [PINP | PIO].
    + left.
      inversion PINP.
      apply T_Entry with (f := f1).
      apply in_removeEntry in H2.
      assumption.
    + right.
      inversion PIO.
      apply T_Entry with (f := f1).
      apply in_removeEntry in H2.
      assumption.
    + assumption.
Qed.

Lemma tsub_out_r :
  forall g1 g2 g pf1 pf2 pf a1 a2 f m t,
    In (a1, a2, f, Chan m out t) g2 ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    (typeOf g (a1, a2) (Chan m out t) \/
     typeOf g (a1, a2) (Chan m io t)).
Proof.
  intros g1 g2 g pf1 pf2 pf a1 a2 f m t IN TSPLIT.
  generalize dependent a1.
  generalize dependent a2.
  generalize dependent f. 
  generalize dependent m.
  generalize dependent t.
  dependent induction TSPLIT.
  - intros; subst; inversion IN.
  - intros.
    specialize IHTSPLIT with t0 m f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf2).
    apply T_Entry in H2.
    apply T_Entry in IN.
    apply type_of_map with
        g2 (a1, a2) (Chan lin q t) (Chan m out t0) in TYP.
    inversion TYP; subst. clear TYP IN.
    inversion H0; subst; auto.
    assumption.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m out t0) n  g2 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [POUT | PIO].
    + left.
      inversion POUT.
      apply T_Entry with (f := f1).
      apply in_removeEntry in H3.
      assumption.
    + right.
      inversion PIO.
      apply T_Entry with (f := f1).
      apply in_removeEntry in H3.
      assumption.
    + assumption.
  - intros.
    specialize IHTSPLIT with t0 m f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf2).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply type_of_map with
        g2 (a1, a2) (Chan un p t) (Chan m out t0) in TYP.
    inversion TYP; subst. clear TYP IN.
    inversion H; subst; auto.
    assumption.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m out t0) n  g2 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [POUT | PIO].
    + left.
      inversion POUT.
      apply T_Entry with (f := f1).
      apply in_removeEntry in H2.
      assumption.
    + right.
      inversion PIO.
      apply T_Entry with (f := f1).
      apply in_removeEntry in H2.
      assumption.
    + assumption.
  - intros.
    specialize IHTSPLIT with t m f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf2).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply type_of_map with
        g2 (a1, a2) Top (Chan m out t) in TYP.
    inversion TYP; subst. clear TYP IN.
    inversion H; subst; auto.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m out t) n  g2 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [PINP | PIO].
    + left.
      inversion PINP.
      apply T_Entry with (f := f1).
      apply in_removeEntry in H2.
      assumption.
    + right.
      inversion PIO.
      apply T_Entry with (f := f1).
      apply in_removeEntry in H2.
      assumption.
    + assumption.
Qed.

Lemma tsub_empty :
  forall g1 g2 g pf1 pf2 pf a1 a2 f m t,
    In (a1, a2, f, Chan m empty t) g1 ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    (exists p,
        typeOf g2 (a1, a2) (Chan m p t) /\
        typeOf g (a1, a2) (Chan m p t)).
Proof.
  intros g1 g2 g pf1 pf2 pf a1 a2 f m t IN TSPLIT.
  generalize dependent a1.
  generalize dependent a2.
  generalize dependent f. 
  generalize dependent m.
  generalize dependent t.
  dependent induction TSPLIT.
  - intros; subst; inversion IN.
  - intros.
    specialize IHTSPLIT with t0 m f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf1).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply type_of_map with
        g1 (a1, a2) (Chan lin p t) (Chan m empty t0) in TYP.
    inversion TYP; subst. clear TYP IN.
    inversion H0; subst; auto.
    exists p'; split; apply T_Entry in H2; assumption.
    exists empty; split; apply T_Entry in H2; assumption.
    assumption.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m empty t0) n  g1 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [p1 [TYP2 TYP3]].
    inversion TYP2; inversion TYP3; subst.
    apply in_removeEntry in H3.
    apply in_removeEntry in H9.
    exists p1; split.
    apply T_Entry in H3; assumption.
    apply T_Entry in H9; assumption.
    assumption.
  - intros.
    specialize IHTSPLIT with t0 m f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf1).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply type_of_map with
        g1 (a1, a2) (Chan un p t) (Chan m empty t0) in TYP.
    inversion TYP; subst. clear TYP IN.
    inversion H1; subst; auto.
    exists empty; split; apply T_Entry in H2; assumption.
    apply T_Entry in H0; assumption.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m empty t0) n  g1 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [p1 [TYP2 TYP3]].
    inversion TYP2; inversion TYP3; subst.
    apply in_removeEntry in H2.
    apply in_removeEntry in H8.
    exists p1; split.
    apply T_Entry in H2; assumption.
    apply T_Entry in H8; assumption.
    assumption.
  - intros.
    specialize IHTSPLIT with t m f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf1).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply type_of_map with
        g1 (a1, a2) Top (Chan m empty t) in TYP.
    inversion TYP.
    apply T_Entry in H0; assumption.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m empty t) n  g1 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [p1 [TYP2 TYP3]].
    inversion TYP2; inversion TYP3; subst.
    apply in_removeEntry in H2.
    apply in_removeEntry in H8.
    exists p1; split.
    apply T_Entry in H2; assumption.
    apply T_Entry in H8; assumption.
    assumption.
Qed.

Lemma tsub_empty_r :
  forall g1 g2 g pf1 pf2 pf a1 a2 f m t,
    In (a1, a2, f, Chan m empty t) g2 ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    (exists p,
        typeOf g1 (a1, a2) (Chan m p t) /\
        typeOf g (a1, a2) (Chan m p t)).
Proof.
  intros g1 g2 g pf1 pf2 pf a1 a2 f m t IN TSPLIT.
  generalize dependent a1.
  generalize dependent a2.
  generalize dependent f. 
  generalize dependent m.
  generalize dependent t.
  dependent induction TSPLIT.
  - intros; subst; inversion IN.
  - intros.
    specialize IHTSPLIT with t0 m f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf2).
    apply T_Entry in H2.
    apply T_Entry in IN.
    apply type_of_map with
        g2 (a1, a2) (Chan lin q t) (Chan m empty t0) in TYP.
    inversion TYP; subst. clear TYP IN.
    inversion H0; subst; auto.
    exists empty; split; apply T_Entry in H1; assumption.
    exists p'; split; apply T_Entry in H1; assumption.
    assumption.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m empty t0) n  g2 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [p1 [TYP2 TYP3]].
    inversion TYP2; inversion TYP3; subst.
    apply in_removeEntry in H3.
    apply in_removeEntry in H9.
    exists p1; split.
    apply T_Entry in H3; assumption.
    apply T_Entry in H9; assumption.
    assumption.
  - intros.
    specialize IHTSPLIT with t0 m f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf2).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply type_of_map with
        g2 (a1, a2) (Chan un p t) (Chan m empty t0) in TYP.
    inversion TYP; subst. clear TYP IN.
    inversion H1; subst; auto.
    exists empty; split; apply T_Entry in H0; assumption.
    apply T_Entry in H0; assumption.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m empty t0) n  g2 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [p1 [TYP2 TYP3]].
    inversion TYP2; inversion TYP3; subst.
    apply in_removeEntry in H2.
    apply in_removeEntry in H8.
    exists p1; split.
    apply T_Entry in H2; assumption.
    apply T_Entry in H8; assumption.
    assumption.
  - intros.
    specialize IHTSPLIT with t m f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf2).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply type_of_map with
        g2 (a1, a2) Top (Chan m empty t) in TYP.
    inversion TYP.
    apply T_Entry in H0; assumption.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m empty t) n  g2 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [p1 [TYP2 TYP3]].
    inversion TYP2; inversion TYP3; subst.
    apply in_removeEntry in H2.
    apply in_removeEntry in H8.
    exists p1; split.
    apply T_Entry in H2; assumption.
    apply T_Entry in H8; assumption.
    assumption.
Qed.

Lemma tsub_io :
  forall g1 g2 g pf1 pf2 pf a1 a2 f m t,
    In (a1, a2, f, Chan m io t) g1 ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    typeOf g (a1, a2) (Chan m io t).
Proof.
  intros g1 g2 g pf1 pf2 pf a1 a2 f m t IN TSPLIT.
  generalize dependent a1.
  generalize dependent a2.
  generalize dependent f. 
  generalize dependent m.
  generalize dependent t.
  dependent induction TSPLIT.
  - intros; subst; inversion IN.
  - intros.
    specialize IHTSPLIT with t0 m f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf1).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply type_of_map with
        g1 (a1, a2) (Chan lin p t) (Chan m io t0) in TYP.
    inversion TYP; subst. clear TYP IN.
    inversion H0; subst; auto.
    assumption.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m io t0) n  g1 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst.
    apply in_removeEntry in H3; apply T_Entry in H3; assumption.
    assumption.
  - intros.
    specialize IHTSPLIT with t0 m f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf1).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply type_of_map with
        g1 (a1, a2) (Chan un p t) (Chan m io t0) in TYP.
    inversion TYP; subst; auto.
    apply T_Entry in H0; assumption.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m io t0) n  g1 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst.
    apply in_removeEntry in H2; apply T_Entry in H2; assumption.
    assumption.
  - intros.
    specialize IHTSPLIT with t m f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf1).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply type_of_map with
        g1 (a1, a2)  Top (Chan m io t) in TYP.
    inversion TYP; subst; auto.
    apply T_Entry in H0; assumption.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m io t) n  g1 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst.
    apply in_removeEntry in H2; apply T_Entry in H2; assumption.
    assumption.
Qed.

Lemma tsub_io_r :
  forall g1 g2 g pf1 pf2 pf a1 a2 f m t,
    In (a1, a2, f, Chan m io t) g2 ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    typeOf g (a1, a2) (Chan m io t).
Proof.
  intros g1 g2 g pf1 pf2 pf a1 a2 f m t IN TSPLIT.
  generalize dependent a1.
  generalize dependent a2.
  generalize dependent f. 
  generalize dependent m.
  generalize dependent t.
  dependent induction TSPLIT.
  - intros; subst; inversion IN.
  - intros.
    specialize IHTSPLIT with t0 m f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf2).
    apply T_Entry in H2.
    apply T_Entry in IN.
    apply type_of_map with
        g2 (a1, a2) (Chan lin q t) (Chan m io t0) in TYP.
    inversion TYP; subst. clear TYP IN.
    inversion H0; subst; auto.
    assumption.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m io t0) n  g2 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst.
    apply in_removeEntry in H3; apply T_Entry in H3; assumption.
    assumption.
  - intros.
    specialize IHTSPLIT with t0 m f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf2).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply type_of_map with
        g2 (a1, a2) (Chan un p t) (Chan m io t0) in TYP.
    inversion TYP; subst; auto.
    apply T_Entry in H0; assumption.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m io t0) n  g2 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst.
    apply in_removeEntry in H2; apply T_Entry in H2; assumption.
    assumption.
  - intros.
    specialize IHTSPLIT with t m f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf2).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply type_of_map with
        g2 (a1, a2)  Top (Chan m io t) in TYP.
    inversion TYP; subst; auto.
    apply T_Entry in H0; assumption.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m io t) n  g2 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst.
    apply in_removeEntry in H2; apply T_Entry in H2; assumption.
    assumption.
Qed.

Lemma tsub_top : 
  forall g1 g2 g pf1 pf2 pf a1 a2 f,
    In (a1, a2, f, Top) g1 ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    typeOf g (a1, a2) Top.
Proof.
  intros g1 g2 g pf1 pf2 pf a1 a2 f IN TSPLIT.
  generalize dependent a1.
  generalize dependent a2.
  generalize dependent f. 
  dependent induction TSPLIT.
  - intros; subst; inversion IN.
  - intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf1).
    apply type_of_map with
        g1 (a1, a2) (Chan lin p t) Top in TYP.
    inversion TYP.
    apply T_Entry in H1; assumption.
    apply T_Entry in IN; assumption. 
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  Top n  g1 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H3.
    apply T_Entry in H3; assumption.
    assumption.
  - intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf1).
    apply type_of_map with
        g1 (a1, a2) (Chan un p t) Top in TYP.
    inversion TYP.
    apply T_Entry in H0; assumption.
    apply T_Entry in IN; assumption. 
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  Top n  g1 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H2.
    apply T_Entry in H2; assumption.
    assumption.
  - intros.
    intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n; auto.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  Top n  g1 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H2.
    apply T_Entry in H2; assumption.
    assumption.
Qed.

Lemma tsub_top_r : 
  forall g1 g2 g pf1 pf2 pf a1 a2 f,
    In (a1, a2, f, Top) g2 ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    typeOf g (a1, a2) Top.
Proof.
  intros g1 g2 g pf1 pf2 pf a1 a2 f IN TSPLIT.
  generalize dependent a1.
  generalize dependent a2.
  generalize dependent f. 
  dependent induction TSPLIT.
  - intros; subst; inversion IN.
  - intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf2).
    apply type_of_map with
        g2 (a1, a2) (Chan lin q t) Top in TYP.
    inversion TYP.
    apply T_Entry in H2; assumption.
    apply T_Entry in IN; assumption. 
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  Top n  g2 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H3.
    apply T_Entry in H3; assumption.
    assumption.
  - intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf2).
    apply type_of_map with
        g2 (a1, a2) (Chan un p t) Top in TYP.
    inversion TYP.
    apply T_Entry in H1; assumption.
    apply T_Entry in IN; assumption. 
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  Top n  g2 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H2.
    apply T_Entry in H2; assumption.
    assumption.
  - intros.
    intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n; auto.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  Top n  g2 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H2.
    apply T_Entry in H2; assumption.
    assumption.
Qed.


#[global] Hint Resolve tsub_un.
#[global] Hint Resolve tsub_empty.
#[global] Hint Resolve tsub_in.
#[global] Hint Resolve tsub_out.
#[global] Hint Resolve tsub_io.
#[global] Hint Resolve tsub_top.
#[global] Hint Resolve tsub_un_r.
#[global] Hint Resolve tsub_empty_r.
#[global] Hint Resolve tsub_in_r.
#[global] Hint Resolve tsub_out_r.
#[global] Hint Resolve tsub_io_r.
#[global] Hint Resolve tsub_top_r.

Lemma tsub_payload :
  forall g1 g2 g pf1 pf2 pf a1 a2 f m p t,
    In (a1, a2, f, (Chan m p t)) g1 ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    exists p1,
      typeOf g (a1, a2) (Chan m p1 t).
Proof with eauto.
  intros g1 g2 g pf1 pf2 pf a1 a2 f m p t IN TSPLIT.
  destruct m; destruct p...
  apply tsub_empty with
      g1 g2 g pf1 pf2 pf a1 a2 f lin t
    in IN.
  destruct IN as [q [TYP2 TYP]].
  exists q...
  assumption.
  apply tsub_in with
      g1 g2 g pf1 pf2 pf a1 a2 f lin t
    in IN.
  destruct IN as [TIN | TIO].
  exists inp...
  exists io...
  assumption.
  apply tsub_out with
      g1 g2 g pf1 pf2 pf a1 a2 f lin t
    in IN.
  destruct IN as [TIN | TIO].
  exists out...
  exists io...
  assumption.
Qed.

Lemma tsub_payload_r :
  forall g1 g2 g pf1 pf2 pf a1 a2 f m p t,
    In (a1, a2, f, (Chan m p t)) g2 ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    exists p1,
      typeOf g (a1, a2) (Chan m p1 t).
Proof with eauto.
  intros g1 g2 g pf1 pf2 pf a1 a2 f m p t IN TSPLIT.
  destruct m; destruct p...
  apply tsub_empty_r with
      g1 g2 g pf1 pf2 pf a1 a2 f lin t
    in IN.
  destruct IN as [q [TYP2 TYP]].
  exists q...
  assumption.
  apply tsub_in_r with
      g1 g2 g pf1 pf2 pf a1 a2 f lin t
    in IN.
  destruct IN as [TIN | TIO].
  exists inp...
  exists io...
  assumption.
  apply tsub_out_r with
      g1 g2 g pf1 pf2 pf a1 a2 f lin t
    in IN.
  destruct IN as [TIN | TIO].
  exists out...
  exists io...
  assumption.
  
Qed.

Lemma tsuper_payload :
  forall g1 g2 g pf1 pf2 pf a1 a2 f m p t,
    In (a1, a2, f, (Chan m p t)) g ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    exists p1,
      typeOf g1 (a1, a2) (Chan m p1 t).
Proof with eauto.
  intros g1 g2 g pf1 pf2 pf a1 a2 f m p t IN TSPLIT.
  generalize dependent a1.
  generalize dependent a2.
  generalize dependent f. 
  generalize dependent t.
  dependent induction TSPLIT.
  - intros; subst; inversion IN.
  - intros.
    specialize IHTSPLIT with t0 f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf3).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply type_of_map with
        g3 (a1, a2) (Chan lin p' t) (Chan m p t0) in TYP.
    inversion TYP; subst. clear TYP IN.
    inversion H0; subst; eauto...
    assumption.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m p t0) n  g3 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [p1 PNEQ2].
    inversion PNEQ2; subst.
    apply in_removeEntry in H3; apply T_Entry in H3...
    assumption.
  - intros.
    specialize IHTSPLIT with t0 f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf3).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply type_of_map with
        g3 (a1, a2) (Chan un p0 t) (Chan m p t0) in TYP.
    inversion TYP; subst...
    apply T_Entry in H0...
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m p t0) n  g3 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [p1 PNEQ2].
    inversion PNEQ2; subst.
    apply in_removeEntry in H2; exists p1...
    eauto.
  - intros.
    specialize IHTSPLIT with t f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf3).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply type_of_map with
        g3 (a1, a2)  Top (Chan m p t) in TYP.
    inversion TYP; subst; auto...
    apply T_Entry in H0; assumption.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m p t) n  g3 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [p1 PNEQ2].
    inversion PNEQ2; subst.
    apply in_removeEntry in H2; apply T_Entry in H2...
    assumption.
Qed.

Lemma tsuper_payload_r :
  forall g1 g2 g pf1 pf2 pf a1 a2 f m p t,
    In (a1, a2, f, (Chan m p t)) g ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    exists p1,
      typeOf g2 (a1, a2) (Chan m p1 t).
Proof with eauto.
  intros g1 g2 g pf1 pf2 pf a1 a2 f m p t IN TSPLIT.
  generalize dependent a1.
  generalize dependent a2.
  generalize dependent f. 
  generalize dependent t.
  dependent induction TSPLIT.
  - intros; subst; inversion IN.
  - intros.
    specialize IHTSPLIT with t0 f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf3).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply type_of_map with
        g3 (a1, a2) (Chan lin p' t) (Chan m p t0) in TYP.
    inversion TYP; subst. clear TYP IN.
    inversion H0; subst; eauto...
    assumption.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m p t0) n  g3 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [p1 PNEQ2].
    inversion PNEQ2; subst.
    apply in_removeEntry in H3; apply T_Entry in H3...
    assumption.
  - intros.
    specialize IHTSPLIT with t0 f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf3).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply type_of_map with
        g3 (a1, a2) (Chan un p0 t) (Chan m p t0) in TYP.
    inversion TYP; subst...
    apply T_Entry in H0...
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m p t0) n  g3 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [p1 PNEQ2].
    inversion PNEQ2; subst.
    apply in_removeEntry in H2; exists p1...
    eauto.
  - intros.
    specialize IHTSPLIT with t f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf3).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply type_of_map with
        g3 (a1, a2)  Top (Chan m p t) in TYP.
    inversion TYP; subst; auto...
    apply T_Entry in H0; assumption.
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  (Chan m p t) n  g3 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [p1 PNEQ2].
    inversion PNEQ2; subst.
    apply in_removeEntry in H2; apply T_Entry in H2...
    assumption.
Qed.

Lemma tsuper_top :
  forall g1 g2 g pf1 pf2 pf a1 a2 f ,
    In (a1, a2, f, Top) g ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    typeOf g1 (a1, a2) Top.
Proof with eauto.
  intros g1 g2 g pf1 pf2 pf a1 a2 f IN TSPLIT.
  generalize dependent a1.
  generalize dependent a2.
  generalize dependent f. 
  dependent induction TSPLIT.
  - intros; subst; inversion IN.
  - intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf3).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply type_of_map with
        g3 (a1, a2) (Chan lin p' t) Top in TYP.
    inversion TYP; subst. clear TYP IN.
    inversion H0; subst; auto...
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  Top n  g3 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst.
    apply in_removeEntry in H3; apply T_Entry in H3...
    assumption.
  - intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf3).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply type_of_map with
        g3 (a1, a2) (Chan un p t) Top in TYP.
    inversion TYP; subst...
    apply T_Entry in H0...
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  Top n  g3 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst.
    apply in_removeEntry in H2...
    eauto.
  - intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf3).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply T_Entry in H0; assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  Top n  g3 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst.
    apply in_removeEntry in H2; apply T_Entry in H2...
    assumption.
Qed.

Lemma tsuper_top_r :
  forall g1 g2 g pf1 pf2 pf a1 a2 f ,
    In (a1, a2, f, Top) g ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    typeOf g2 (a1, a2) Top.
Proof with eauto.
  intros g1 g2 g pf1 pf2 pf a1 a2 f IN TSPLIT.
  generalize dependent a1.
  generalize dependent a2.
  generalize dependent f. 
  dependent induction TSPLIT.
  - intros; subst; inversion IN.
  - intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf3).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply type_of_map with
        g3 (a1, a2) (Chan lin p' t) Top in TYP.
    inversion TYP; subst. clear TYP IN.
    inversion H0; subst; auto...
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  Top n  g3 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst.
    apply in_removeEntry in H3; apply T_Entry in H3...
    assumption.
  - intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf3).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply type_of_map with
        g3 (a1, a2) (Chan un p t) Top in TYP.
    inversion TYP; subst...
    apply T_Entry in H0...
    assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  Top n  g3 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst.
    apply in_removeEntry in H2...
    eauto.
  - intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (TYP := pf3).
    apply T_Entry in H1.
    apply T_Entry in IN.
    apply T_Entry in H0; assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) f0  Top n  g3 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst.
    apply in_removeEntry in H2; apply T_Entry in H2...
    assumption.
Qed.

Lemma fsub_hid :
  forall g1 g2 g pf1 pf2 pf a1 a2 t,
    In (a1, a2, hid, t) g1 ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    flagOf g (a1, a2) hid.
Proof.
  intros g1 g2 g pf1 pf2 pf a1 a2 f IN TSPLIT.
  generalize dependent a1.
  generalize dependent a2.
  generalize dependent f. 
  dependent induction TSPLIT.
  - intros; subst; inversion IN.
  - intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (FYP := pf1).
    apply flag_of_map with
        g1 (a1, a2) f hid in FYP.
    inversion H; subst; auto.
    inversion H.
    inversion H3.
    apply F_Entry in H1; assumption.
    apply F_Entry in IN; assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) hid f0  n  g1 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H3.
    apply F_Entry in H3; assumption.
    assumption.
  - intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (FYP := pf1).
    apply flag_of_map with
        g1 (a1, a2) f hid in FYP.
    inversion H; subst; auto.
    inversion H2. 
    inversion H2.
    apply F_Entry in H0; assumption.
    apply F_Entry in IN; assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) hid f0  n  g1 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H2.
    apply F_Entry in H2; assumption.
    assumption.
  - intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (FYP := pf1).
    apply flag_of_map with
        g1 (a1, a2) f hid in FYP.
    inversion H; subst; auto.
    inversion H2. 
    inversion H2.
    apply F_Entry in H0; assumption.
    apply F_Entry in IN; assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) hid f0  n  g1 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H2.
    apply F_Entry in H2; assumption.
    assumption.
Qed.

Lemma fsub_hid_r :
  forall g1 g2 g pf1 pf2 pf a1 a2 t,
    In (a1, a2, hid, t) g2 ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    flagOf g (a1, a2) hid.
Proof.
  intros g1 g2 g pf1 pf2 pf a1 a2 f IN TSPLIT.
  generalize dependent a1.
  generalize dependent a2.
  generalize dependent f. 
  dependent induction TSPLIT.
  - intros; subst; inversion IN.
  - intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (FYP := pf2).
    apply flag_of_map with
        g2 (a1, a2) g hid in FYP.
    inversion H; subst; auto.
    inversion H6.
    inversion H6.
    apply F_Entry in H2; assumption.
    apply F_Entry in IN; assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) hid f0  n  g2 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H3.
    apply F_Entry in H3; assumption.
    assumption.
  - intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (FYP := pf2).
    apply flag_of_map with
        g2 (a1, a2) g hid in FYP.
    inversion H; subst; auto.
    inversion H5. 
    inversion H5.
    apply F_Entry in H1; assumption.
    apply F_Entry in IN; assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) hid f0  n  g2 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H2.
    apply F_Entry in H2; assumption.
    assumption.
  - intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (FYP := pf2).
    apply flag_of_map with
        g2 (a1, a2) g hid in FYP.
    inversion H; subst; auto.
    inversion H5. 
    inversion H5.
    apply F_Entry in H1; assumption.
    apply F_Entry in IN; assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) hid f0  n  g2 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H2.
    apply F_Entry in H2; assumption.
    assumption.
Qed.


Lemma fsub_ill :
  forall g1 g2 g pf1 pf2 pf a1 a2 t,
    In (a1, a2, ill, t) g1 ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    (flagOf g (a1, a2) hid \/
     flagOf g (a1, a2) ill).
Proof.
  intros g1 g2 g pf1 pf2 pf a1 a2 f IN TSPLIT.
  generalize dependent a1.
  generalize dependent a2.
  generalize dependent f. 
  dependent induction TSPLIT.
  - intros; subst; inversion IN.
  - intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (FYP := pf1).
    apply flag_of_map with
        g1 (a1, a2) f ill in FYP.
    inversion H; subst; auto.
    inversion H3.
    apply F_Entry in H1; assumption.
    apply F_Entry in IN; assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) ill f0  n  g1 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [PNEQ2 | PNEQ2].
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H3.
    apply F_Entry in H3; left; assumption.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H3.
    apply F_Entry in H3; right; assumption.
    assumption.
  - intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (FYP := pf1).
    apply flag_of_map with
        g1 (a1, a2) f ill in FYP.
    inversion H; subst; auto.
    inversion H2. 
    apply F_Entry in H0; assumption.
    apply F_Entry in IN; assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) ill f0  n  g1 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [PNEQ2 | PNEQ2].
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H2.
    apply F_Entry in H2; left; assumption.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H2.
    apply F_Entry in H2; right; assumption.
    assumption.
  - intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (FYP := pf1).
    apply flag_of_map with
        g1 (a1, a2) f ill in FYP.
    inversion H; subst; auto.
    inversion H2. 
    apply F_Entry in H0; assumption.
    apply F_Entry in IN; assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) ill f0  n  g1 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [PNEQ2 | PNEQ2].
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H2.
    apply F_Entry in H2; left; assumption.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H2.
    apply F_Entry in H2; right; assumption.
    assumption.
Qed.

Lemma fsub_ill_r :
  forall g1 g2 g pf1 pf2 pf a1 a2 t,
    In (a1, a2, ill, t) g2 ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    (flagOf g (a1, a2) hid \/
     flagOf g (a1, a2) ill).
Proof.
  intros g1 g2 g pf1 pf2 pf a1 a2 f IN TSPLIT.
  generalize dependent a1.
  generalize dependent a2.
  generalize dependent f. 
  dependent induction TSPLIT.
  - intros; subst; inversion IN.
  - intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (FYP := pf2).
    apply flag_of_map with
        g2 (a1, a2) g ill in FYP.
    inversion H; subst; auto.
    inversion H6.
    apply F_Entry in H2; assumption.
    apply F_Entry in IN; assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) ill f0  n  g2 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [PNEQ2 | PNEQ2].
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H3.
    apply F_Entry in H3; left; assumption.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H3.
    apply F_Entry in H3; right; assumption.
    assumption.
  - intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (FYP := pf2).
    apply flag_of_map with
        g2 (a1, a2) g ill in FYP.
    inversion H; subst; auto.
    inversion H5. 
    apply F_Entry in H1; assumption.
    apply F_Entry in IN; assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) ill f0  n  g2 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [PNEQ2 | PNEQ2].
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H2.
    apply F_Entry in H2; left; assumption.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H2.
    apply F_Entry in H2; right; assumption.
    assumption.
  - intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (FYP := pf2).
    apply flag_of_map with
        g2 (a1, a2) g ill in FYP.
    inversion H; subst; auto.
    inversion H5. 
    apply F_Entry in H1; assumption.
    apply F_Entry in IN; assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) ill f0  n  g2 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    destruct PNEQ2 as [PNEQ2 | PNEQ2].
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H2.
    apply F_Entry in H2; left; assumption.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H2.
    apply F_Entry in H2; right; assumption.
    assumption.
Qed.

Lemma fsub_vis :
  forall g1 g2 g pf1 pf2 pf a1 a2 t,
    In (a1, a2, vis, t) g1 ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    flagOf g (a1, a2) vis.
Proof.
  intros g1 g2 g pf1 pf2 pf a1 a2 f IN TSPLIT.
  generalize dependent a1.
  generalize dependent a2.
  generalize dependent f. 
  dependent induction TSPLIT.
  - intros; subst; inversion IN.
  - intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (FYP := pf1).
    apply flag_of_map with
        g1 (a1, a2) f vis in FYP.
    inversion H; subst; auto.
    inversion H3.
    inversion H3.
    inversion H3.
    apply F_Entry in H1; assumption.
    apply F_Entry in IN; assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) vis f0  n  g1 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H3.
    apply F_Entry in H3; assumption.
    assumption.
  - intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (FYP := pf1).
    apply flag_of_map with
        g1 (a1, a2) f vis in FYP.
    inversion H; subst; auto.
    inversion H2.
    inversion H2.
    inversion H2.
    apply F_Entry in H0; assumption.
    apply F_Entry in IN; assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) vis f0  n  g1 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H2.
    apply F_Entry in H2; assumption.
    assumption.
  - intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (FYP := pf1).
    apply flag_of_map with
        g1 (a1, a2) f vis in FYP.
    inversion H; subst; auto.
    inversion H2.
    inversion H2.
    inversion H2.
    apply F_Entry in H0; assumption.
    apply F_Entry in IN; assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) vis f0  n  g1 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H2.
    apply F_Entry in H2; assumption.
    assumption.
Qed.

Lemma fsub_vis_r :
  forall g1 g2 g pf1 pf2 pf a1 a2 t,
    In (a1, a2, vis, t) g2 ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    flagOf g (a1, a2) vis.
Proof.
  intros g1 g2 g pf1 pf2 pf a1 a2 f IN TSPLIT.
  generalize dependent a1.
  generalize dependent a2.
  generalize dependent f. 
  dependent induction TSPLIT.
  - intros; subst; inversion IN.
  - intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (FYP := pf2).
    apply flag_of_map with
        g2 (a1, a2) g vis in FYP.
    inversion H; subst; auto.
    inversion H6.
    inversion H6.
    inversion H6.
    apply F_Entry in H2; assumption.
    apply F_Entry in IN; assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) vis f0  n  g2 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H3.
    apply F_Entry in H3; assumption.
    assumption.
  - intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (FYP := pf2).
    apply flag_of_map with
        g2 (a1, a2) g vis in FYP.
    inversion H; subst; auto.
    inversion H5.
    inversion H5.
    inversion H5.
    apply F_Entry in H1; assumption.
    apply F_Entry in IN; assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) vis f0  n  g2 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H2.
    apply F_Entry in H2; assumption.
    assumption.
  - intros.
    specialize IHTSPLIT with f0 a2 a1.
    subst g'''.
    case_eq (pair_eq n (a1, a2)).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    assert (FYP := pf2).
    apply flag_of_map with
        g2 (a1, a2) g vis in FYP.
    inversion H; subst; auto.
    inversion H5.
    inversion H5.
    inversion H5.
    apply F_Entry in H1; assumption.
    apply F_Entry in IN; assumption.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize removeEntry_in with
        (a1, a2) vis f0  n  g2 as INREM.
    assert (PNEQ2 : (a1, a2) <> n). auto.
    apply INREM in PNEQ2.
    apply IHTSPLIT in PNEQ2.
    inversion PNEQ2; subst; auto.
    apply in_removeEntry in H2.
    apply F_Entry in H2; assumption.
    assumption.
Qed.

Lemma fsuper_vis: forall g1 g2 g pf1 pf2 pf n t,
    tEnv_split g1 g2 g pf1 pf2 pf ->
    In (n, vis, t) g ->
    flagOf g1 n vis /\ flagOf g2 n vis. 
Proof.
  intros g1 g2 g pf1 pf2 pf n t TSPLIT IN.
  destruct t.
  destruct n.
  remember n as a1; remember n0 as a2; subst n n0.
  apply tsuper_payload with
      (g1 := g1) (g2 := g2)
      (pf1 := pf1) (pf2 := pf2) (pf := pf)
    in IN as TYP1.
  destruct TYP1 as [q TYP1]; inversion TYP1;
    clear TYP1; subst.
  split.
  
  assert (f = vis); destruct f.
  * apply fsub_hid with
        (g2 := g2) (g := g) (pf1 := pf1)
        (pf2 := pf2) (pf := pf) in H.
    inversion H; subst.
    eauto.
    eauto.
  * apply fsub_ill with
        (g2 := g2) (g := g) (pf1 := pf1)
        (pf2 := pf2) (pf := pf) in H.
    inversion H; subst.
    inversion H0; subst.
    apply flag_of_map with
        g (a1, a2) vis hid
      in pf as ABS2.
    inversion ABS2.
    eauto.
    eauto.
    apply flag_of_map with
        g (a1, a2) vis ill
      in pf as ABS2.
    inversion ABS2.
    eauto.
    eauto.
    eauto.
  * tauto.
  * inversion H0.
  * inversion H0.
  * eauto.
  *
    apply tsuper_payload_r with
        (g1 := g1) (g2 := g2)
        (pf1 := pf1) (pf2 := pf2) (pf := pf)
      in IN as TYP1.
    destruct TYP1 as [q1 TYP1]; inversion TYP1;
      clear TYP1; subst.
    clear H f.
    remember f0 as f.
    assert (f = vis); destruct f.
    assert (H := H0).
    apply fsub_hid_r with
        (g2 := g2) (g := g) (pf1 := pf1)
        (pf2 := pf2) (pf := pf) in H.
    inversion H; subst.
    eauto.
    eauto.
    assert (H := H0).
    apply fsub_ill_r with
        (g2 := g2) (g := g) (pf1 := pf1)
        (pf2 := pf2) (pf := pf) in H.
    inversion H; subst.
    inversion H1; subst.
    apply flag_of_map with
        g (a1, a2) vis hid
      in pf as ABS2.
    inversion ABS2.
    eauto.
    eauto.
    apply flag_of_map with
        g (a1, a2) vis ill
      in pf as ABS2.
    inversion ABS2.
    eauto.
    eauto.
    eauto.
    tauto.
    inversion H.
    inversion H.
    eauto.
    eauto.
  * eauto.
  * destruct n.
    remember n as a1; remember n0 as a2; subst n n0.
    apply tsuper_top with
        (g1 := g1) (g2 := g2)
        (pf1 := pf1) (pf2 := pf2) (pf := pf)
      in IN as TYP1. inversion TYP1; subst.
    split.
    
    assert (f = vis); destruct f.

    apply fsub_hid with
        (g2 := g2) (g := g) (pf1 := pf1)
        (pf2 := pf2) (pf := pf) in H.
    inversion H; subst.
    eauto.
    eauto.
    apply fsub_ill with
        (g2 := g2) (g := g) (pf1 := pf1)
        (pf2 := pf2) (pf := pf) in H.
    inversion H; subst.
    inversion H0; subst.
    apply flag_of_map with
        g (a1, a2) vis hid
      in pf as ABS2.
    inversion ABS2.
    eauto.
    eauto.
    apply flag_of_map with
        g (a1, a2) vis ill
      in pf as ABS2.
    inversion ABS2.
    eauto.
    eauto.
    eauto.
    tauto.
    inversion H0.
    inversion H0.
    eauto.
    clear TYP1.
    apply tsuper_top_r with
        (g1 := g1) (g2 := g2)
        (pf1 := pf1) (pf2 := pf2) (pf := pf)
      in IN as TYP1.
    inversion TYP1; subst.
    clear H f.
    remember f0 as f.
    assert (f = vis); destruct f.
    assert (H := H0).
    apply fsub_hid_r with
        (g2 := g2) (g := g) (pf1 := pf1)
        (pf2 := pf2) (pf := pf) in H.
    inversion H; subst.
    eauto.
    eauto.
    assert (H := H0).
    apply fsub_ill_r with
        (g2 := g2) (g := g) (pf1 := pf1)
        (pf2 := pf2) (pf := pf) in H.
    inversion H; subst.
    inversion H1; subst.
    apply flag_of_map with
        g (a1, a2) vis hid
      in pf as ABS2.
    inversion ABS2.
    eauto.
    eauto.
    apply flag_of_map with
        g (a1, a2) vis ill
      in pf as ABS2.
    inversion ABS2.
    eauto.
    eauto.
    eauto.
    tauto.
    inversion H.
    inversion H.
    eauto.
    eauto.
    eauto.
Qed.