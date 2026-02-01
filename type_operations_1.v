Require Import
        Bool List Omega PeanoNat Program.Equality
        RemoveEntry Domain
        header
        operations
        pi_syntax 
        pairEq type_system semantics
        disjoint_newEntries.

Hint Resolve nonRecTypes.

Hint Constructors piType.
Hint Resolve Pp_emptyL.
Hint Resolve Pp_emptyR.
Hint Resolve Pp_inpL.
Hint Resolve Pp_inpR.
Hint Resolve Tp_Base.
Hint Resolve Tp_LinPlus.
Hint Resolve Tp_UnPlus.
Hint Resolve T_Entry.
Hint Resolve F_Entry.
Hint Resolve type_plus_comm.






Lemma cons_isMap: forall a f t g,
    isMap g ->
    (~ exists f1 t1, In (a, f1, t1) g) ->
    isMap ((a, f, t) :: g).
Proof.
  intros a f t g pf NEX.
  unfold isMap.
  intuition.
  - case_eq (pair_eq (a0, b) a).
    intros PEQ. assert (PEQ2 := PEQ).
    rewrite <-pairEq_eq in PEQ; subst.
    apply in_inv in H1. apply in_inv in H0.
    intuition.
    inversion H; inversion H1.
    subst; tauto.
    elim NEX; exists f1; exists t1; assumption.
    elim NEX; exists f2; exists t2; assumption.
    apply flag_of_map with (x := (a0, b)) (f1 := f1) (f2 := f2) in pf as FLAG.
    assumption.
    apply F_Entry in H1; assumption.
    apply F_Entry in H; assumption.
    intros PNEQ. assert (PEQ2 := PNEQ).
    rewrite <-pairEq_neq in PNEQ.
    assert (COMM : a <> (a0, b)); auto...
    apply in_inv in H1. apply in_inv in H0.
    intuition. 
    inversion H; inversion H0.
    subst; tauto.
    inversion H; subst; tauto.
    inversion H0; subst; tauto.
    apply flag_of_map
      with (x := (a0, b)) (f1 := f1) (f2 := f2)
      in pf as FLAG.
    assumption.
    apply F_Entry in H; assumption.
    apply F_Entry in H0; assumption.
  -  case_eq (pair_eq (a0, b) a).
     intros PEQ. assert (PEQ2 := PEQ).
     rewrite <-pairEq_eq in PEQ; subst.
     apply in_inv in H1. apply in_inv in H0.
     intuition.
     inversion H; inversion H1.
     subst; tauto.
     elim NEX; exists f1; exists t1; assumption.
     elim NEX; exists f2; exists t2; assumption.
     apply type_of_map with (x := (a0, b)) (t1 := t1) (t2 := t2) in pf as TYP.
     assumption.
     apply T_Entry in H1; assumption.
     apply T_Entry in H; assumption.
     intros PNEQ. assert (PEQ2 := PNEQ).
     rewrite <-pairEq_neq in PNEQ.
     assert (COMM : a <> (a0, b)); auto...
     apply in_inv in H1. apply in_inv in H0.
     intuition. 
     inversion H; inversion H0.
     subst; tauto.
     inversion H; subst; tauto.
     inversion H0; subst; tauto.
     apply type_of_map
       with (x := (a0, b)) (t1 := t1) (t2 := t2)
       in pf as TYP.
     assumption.
     apply T_Entry in H; assumption.
     apply T_Entry in H0; assumption.
Qed.


Hint Resolve isMap_cons.
Hint Resolve cons_isMap.





Hint Resolve removeEntry_head.
Hint Resolve in_removeEntry.

     

Lemma split_in_ex: forall g1 g2 g pf1 pf2 pf a f t,
    tEnv_split g1 g2 g pf1 pf2 pf ->
    In (a, f, t) g1 ->
    exists f2 t2,
      In (a, f2, t2) g2.
Proof.
  intros g1 g2 g pf1 pf2 pf a f t TSPLIT IN.
  dependent induction TSPLIT.
  - subst; inversion IN.
  - case_eq (pair_eq n a).
    + intros PEQ. assert (PEQ2 := PEQ).
      rewrite <-pairEq_eq in PEQ; subst.
      exists g. exists (Chan lin q t0). assumption.
    + intros PNEQ. assert (PEQ2 := PNEQ).
      rewrite <-pairEq_neq in PNEQ.
      assert (PNEQC : a <> n); auto.
      apply removeEntry_in with
          a f t n g1
        in PNEQC as REM.
      apply IHTSPLIT in REM.
      destruct REM as [f1 [t1 REM]].
      apply in_removeEntry in REM.
      exists f1; exists t1; assumption.
      all:assumption.
  - case_eq (pair_eq n a).
    + intros PEQ. assert (PEQ2 := PEQ).
      rewrite <-pairEq_eq in PEQ; subst.
      exists g. exists (Chan un p t0). assumption.
    + intros PNEQ. assert (PEQ2 := PNEQ).
      rewrite <-pairEq_neq in PNEQ.
      assert (PNEQC : a <> n); auto.
      apply removeEntry_in with
          a f t n g1
        in PNEQC as REM.
      apply IHTSPLIT in REM.
      destruct REM as [f1 [t1 REM]].
      apply in_removeEntry in REM.
      exists f1; exists t1; assumption.
      all:assumption.
  - case_eq (pair_eq n a).
    + intros PEQ. assert (PEQ2 := PEQ).
      rewrite <-pairEq_eq in PEQ; subst.
      exists g. exists Top. assumption.
    + intros PNEQ. assert (PEQ2 := PNEQ).
      rewrite <-pairEq_neq in PNEQ.
      assert (PNEQC : a <> n); auto.
      apply removeEntry_in with
          a f t n g1
        in PNEQC as REM.
      apply IHTSPLIT in REM.
      destruct REM as [f1 [t1 REM]].
      apply in_removeEntry in REM.
      exists f1; exists t1; assumption.
      all:assumption.
Qed.

Lemma split_in_ex_2: forall g1 g2 g pf1 pf2 pf a f t,
    tEnv_split g1 g2 g pf1 pf2 pf ->
    In (a, f, t) g2 ->
    exists f2 t2,
      In (a, f2, t2) g1.
Proof.
  intros g1 g2 g pf1 pf2 pf a f t TSPLIT IN.
  dependent induction TSPLIT.
  - subst; inversion IN.
  - case_eq (pair_eq n a).
    + intros PEQ. assert (PEQ2 := PEQ).
      rewrite <-pairEq_eq in PEQ; subst.
      exists f0. exists (Chan lin p t0). assumption.
    + intros PNEQ. assert (PEQ2 := PNEQ).
      rewrite <-pairEq_neq in PNEQ.
      assert (PNEQC : a <> n); auto.
      apply removeEntry_in with
          a f t n g2
        in PNEQC as REM.
      apply IHTSPLIT in REM.
      destruct REM as [f1 [t1 REM]].
      apply in_removeEntry in REM.
      exists f1; exists t1; assumption.
      all:assumption.
  - case_eq (pair_eq n a).
    + intros PEQ. assert (PEQ2 := PEQ).
      rewrite <-pairEq_eq in PEQ; subst.
      exists f0. exists (Chan un p t0). assumption.
    + intros PNEQ. assert (PEQ2 := PNEQ).
      rewrite <-pairEq_neq in PNEQ.
      assert (PNEQC : a <> n); auto.
      apply removeEntry_in with
          a f t n g2
        in PNEQC as REM.
      apply IHTSPLIT in REM.
      destruct REM as [f1 [t1 REM]].
      apply in_removeEntry in REM.
      exists f1; exists t1; assumption.
      all:assumption.
  - case_eq (pair_eq n a).
    + intros PEQ. assert (PEQ2 := PEQ).
      rewrite <-pairEq_eq in PEQ; subst.
      exists f0. exists Top. assumption.
    + intros PNEQ. assert (PEQ2 := PNEQ).
      rewrite <-pairEq_neq in PNEQ.
      assert (PNEQC : a <> n); auto.
      apply removeEntry_in with
          a f t n g2
        in PNEQC as REM.
      apply IHTSPLIT in REM.
      destruct REM as [f1 [t1 REM]].
      apply in_removeEntry in REM.
      exists f1; exists t1; assumption.
      all:assumption.
Qed.


Hint Resolve split_in_ex.
Hint Resolve split_in_ex_2.


Lemma split_not_in_not_ex: forall g1 g2 g pf1 pf2 pf a,
    tEnv_split g1 g2 g pf1 pf2 pf ->
    (~ exists f t, In (a, f, t) g1) ->
    ~exists f2 t2,
        In (a, f2, t2) g2.
Proof.
  intros.
  unfold not; intros.
  elim H0.
  destruct H1 as [f1 [t1 ABS]].
  apply split_in_ex_2 with
      g1 g2 g pf1 pf2 pf a f1 t1
    in H as IN.
  eauto...
  assumption.
Qed.



Lemma split_head_map :
  forall g1 g2 g pf1 pf2 pf a f t f1 t1,
    NoDup(domain ((a,f,t) :: g1)) ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    isMap ((a, f1, t1) :: g2).
Proof.
  intros g1 g2 g pf1 pf2 pf a f t f1 t1 nd_pf TSPLIT.
  apply no_dup_domain_not_exists in nd_pf.
  assert (pf2' := pf2). 
  apply cons_isMap with
      a f1 t1 g2 in pf2'.
  assumption.
  apply split_not_in_not_ex with (a := a)  in TSPLIT.
  intuition.
  unfold not; intros ABS; elim nd_pf.
  intuition.
Qed.



Hint Resolve no_dup_domain_cons.

Lemma no_dup_isMap: forall g,
    NoDup(domain g) ->
    isMap g.
Proof with eauto.
  unfold isMap.
  dependent induction g.
  intros. inversion H0; inversion H1...
  intros.
  assert (NoDup (domain g))... intuition.

  destruct a as [[a f] t]. 
  apply in_inv in H2; apply in_inv in H3.
  intuition.
  rewrite H2 in H4; inversion H4; subst...
  unfold domain in H; fold domain in H.
  apply no_dup_iff with (l1 := a :: nil) in H.
  intuition.
  apply disjoint_car in H6;
    apply disjoint_2_cons_l in H6.       
  apply in_g_in_domain in H2.
  intuition. inversion H4; subst... contradiction.
  inversion H2; subst...
  unfold domain in H; fold domain in H.
  apply no_dup_iff with (l1 := x :: nil) in H.
  intuition.
  apply disjoint_car in H6;
    apply disjoint_2_cons_l in H6.
  intuition.
  apply in_g_in_domain in H4.
  intuition.
  specialize H0 with x f1 t1 f2 t2...
  intuition.

  destruct a as [[a f] t]. 
  apply in_inv in H2; apply in_inv in H3.
  intuition.
  rewrite H2 in H4; inversion H4; subst...
  unfold domain in H; fold domain in H.
  apply no_dup_iff with (l1 := a :: nil) in H.
  intuition.
  apply disjoint_car in H6;
    apply disjoint_2_cons_l in H6.       
  apply in_g_in_domain in H2.
  intuition. inversion H4; subst... contradiction.
  inversion H2; subst...
  unfold domain in H; fold domain in H.
  apply no_dup_iff with (l1 := x :: nil) in H.
  intuition.
  apply disjoint_car in H6;
    apply disjoint_2_cons_l in H6.
  intuition.
  apply in_g_in_domain in H4.
  intuition.
  specialize H0 with x f1 t1 f2 t2...
  intuition.
Qed.

Hint Resolve type_of_map.
Hint Resolve flag_of_map.
Hint Resolve isMap_cons.
Hint Resolve cons_isMap.
Hint Resolve no_dup_isMap.

Lemma nonRecActions1:
  forall g p a1 a2 b1 b2 g' p' pf,
    lts g p (aIn a1 a2 b1 b2) g' p' pf ->
    (a1, a2) <> (b1, b2).
Proof with eauto.
  intros.
  unfold not; intros ABS.
  assert (pf1: isMap g)...
  dependent induction H.
  specialize IHlts with a1 a2 b1 b2...
  
  inversion H; subst.
  rewrite <-ABS in H2.
  apply type_of_map with
      g (a1, a2) (Chan lin inp Top) Top 
    in pf1 as ABS2.
  assert (K := nonRecTypes). destruct K as [K1 K2].
  eauto. eauto. eauto.
  rewrite <-ABS in H2.
  apply type_of_map with
      g (a1, a2) (Chan lin inp (Chan lin p2 t0)) (Chan lin p1 t0) 
    in pf1 as ABS2.
  assert (K := nonRecTypes). destruct K as [K1 K2].
  all:eauto.

  
  rewrite <-ABS in H2.
  apply type_of_map with
      g (a1, a2) (Chan lin inp (Chan un p2 t0)) (Chan un p1 t0) 
    in pf1 as ABS2.
  assert (K := nonRecTypes). destruct K as [K1 K2].
  all:eauto.

  inversion H0; subst.
  rewrite <-ABS in H3.
  apply type_of_map with
      g (a1, a2) (Chan un pol Top) Top 
    in pf1 as ABS2.
  assert (K := nonRecTypes). destruct K as [K1 K2].
  eauto. eauto. eauto.
  rewrite <-ABS in H3.
  apply type_of_map with
      g (a1, a2) (Chan un pol (Chan lin p2 t0)) (Chan lin p1 t0) 
    in pf1 as ABS2.
  assert (K := nonRecTypes). destruct K as [K1 K2].
  all:eauto.
  
  rewrite <-ABS in H3.
  apply type_of_map with
      g (a1, a2) (Chan un pol (Chan un p2 t0)) (Chan un p1 t0) 
    in pf1 as ABS2.
  assert (K := nonRecTypes). destruct K as [K1 K2].
  all:eauto.

  inversion H0; subst.
  rewrite <-ABS in H3.
  apply type_of_map with
      g (a1, a2) (Chan un pol Top) Top 
    in pf1 as ABS2.
  assert (K := nonRecTypes). destruct K as [K1 K2].
  eauto. eauto. eauto.
  rewrite <-ABS in H3.
  apply type_of_map with
      g (a1, a2) (Chan un pol (Chan lin p2 t0)) (Chan lin p1 t0) 
    in pf1 as ABS2.
  assert (K := nonRecTypes). destruct K as [K1 K2].
  all:eauto.
  
  rewrite <-ABS in H3.
  apply type_of_map with
      g (a1, a2) (Chan un pol (Chan un p2 t0)) (Chan un p1 t0) 
    in pf1 as ABS2.
  assert (K := nonRecTypes). destruct K as [K1 K2].
  all:eauto.

Qed.


Lemma nonRecActions2:
  forall g p a1 a2 b1 b2 g' p' pf,
    lts g p (aOut a1 a2 b1 b2) g' p' pf ->
    (a1, a2) <> (b1, b2).
Proof.
  intros.
  unfold not; intros ABS.
  apply no_dup_isMap in pf as pf1...
  dependent induction H.
  specialize IHlts with a1 a2 b1 b2...
  intuition.
  
  assert (H2 := H1).
  inversion H; subst.
  destruct H4. inversion H4; subst.
  rewrite <-ABS in H2.
  apply type_of_map with
      g (a1, a2) (Chan lin out Top) Top 
    in pf1 as ABS2.
  assert (K := nonRecTypes). destruct K as [K1 K2].
  eauto. eauto. eauto.
  rewrite <-ABS in H2.
  apply type_of_map with
      g (a1, a2) (Chan lin out (Chan lin p1 t0)) (Chan lin p0 t0) 
    in pf1 as ABS2.
  assert (K := nonRecTypes). destruct K as [K1 K2].
  all:eauto.
  
  rewrite <-ABS in H2.
  apply type_of_map with
      g (a1, a2) (Chan lin out (Chan un p1 t0)) (Chan un (pol_cup p1 p2) t0) 
    in pf1 as ABS2.
  assert (K := nonRecTypes). destruct K as [K1 K2].
  all:eauto.

  assert (H3 := H2).
  inversion H0; subst.
  inversion H5. inversion H6; subst.
  rewrite <-ABS in H3.
  apply type_of_map with
      g (a1, a2) (Chan un pol Top) Top 
    in pf1 as ABS2.
  assert (K := nonRecTypes). destruct K as [K1 K2].
  eauto. eauto. eauto.
  rewrite <-ABS in H3.
  apply type_of_map with
      g (a1, a2) (Chan un pol (Chan lin p1 t0)) (Chan lin p0 t0) 
    in pf1 as ABS2.
  assert (K := nonRecTypes). destruct K as [K1 K2].
  all:eauto.
  
  rewrite <-ABS in H3.
  apply type_of_map with
      g (a1, a2) (Chan un pol (Chan un p1 t0)) (Chan un  (pol_cup p1 p2) t0) 
    in pf1 as ABS2.
  assert (K := nonRecTypes). destruct K as [K1 K2].
  all:eauto.
Qed.

Lemma typeOf_removeEntry : forall b f t g a ta,
    typeOf g a ta ->
    a <> b ->
    typeOf ((b, f, t) :: removeEntry b g) a ta.
Proof with eauto.
  intros.
  inversion H; subst.
  apply removeEntry_in with (f := f0) (t := ta) (g := g) in H0.
  apply in_cons with (a := (b, f, t)) in H0.
  all:eauto.
Qed.
