Require Import
        Bool List Omega PeanoNat Program.Equality
        RemoveEntry Domain
        header
        operations pi_syntax 
        pairEq type_system semantics 
        type_operations_1
        split_exists_neutral
        sub_split
        disjoint_newEntries.


(************ TYPE OPERATIONS 2 *****************)



Lemma unique_remove :
  forall t t2 t3 t4,
    type_remove t3 t t4 ->
    type_remove t3 t t2 ->
    t2 = t4.
Proof.
  intros t t2 t3 t4 TS4 TS2.
  destruct t3.
  destruct m. 
  specialize type_remove_lin with
      t3 t t4 as TRL4.
  specialize type_remove_lin with
      t3 t t2 as TRL2.
  destruct p; intuition.
  all:subst; auto...
  inversion H1.
  inversion H.
  inversion H5.
  inversion H5.
  inversion H.
  inversion H.
  inversion H1.
  inversion H.
  specialize type_remove_un with
      t3 t t4 as TRL4.
  specialize type_remove_un with
      t3 t t2 as TRL2.
  destruct p; intuition.
  all:subst; auto...
  inversion TS4. inversion TS2.
  destruct H0; inversion H0.
  destruct H2; inversion H2.
  tauto.
Qed.

Hint Resolve unique_remove.




Hint Resolve no_dup_not_in_removeEntry.




Hint Resolve no_dup_removeEntry_no_dup.
Hint Resolve nonRecTypes.

Lemma cons_removeEntry: forall g a f t,
    NoDup (domain g) ->
    isMap ((a, f, t) :: (removeEntry a g)).
Proof with eauto.
  intros g a f t nd_pf.
  apply no_dup_not_in_removeEntry with
      g a f t 
    in nd_pf as ND1.
  apply  no_dup_isMap in nd_pf as pf. 
  unfold isMap; intros; intuition.
  apply in_inv in H0.
  apply in_inv in H1.
  intuition.
  inversion H; inversion H0. subst f1 t1 x f2 t2.
  tauto.
  inversion H. subst x f1 t1.
  apply no_dup_not_in_removeEntry with
      g a f2 t2
    in nd_pf as ND2.
  intuition.
  inversion H0; subst x f2 t2.
  apply no_dup_not_in_removeEntry with
      g a f1 t1
    in nd_pf as ND2.
  intuition.
  apply no_dup_removeEntry_no_dup with
      g a in nd_pf as nd_pf2.
  apply no_dup_isMap in nd_pf2 as pf2.
  apply flag_of_map with
      (removeEntry a g) x f1 f2
    in pf2 as FLY.
  eauto.
  eauto.
  eauto.
  apply no_dup_removeEntry_no_dup with
      g a in nd_pf as nd_pf2.
  apply no_dup_isMap in nd_pf2 as pf2.
  apply cons_isMap with
      a f t (removeEntry a g) 
    in pf2 as pf3.
  remember ((a, f, t) :: removeEntry a g) as g3.
  apply type_of_map with
      g3 x t1 t2
    in pf3 as TYP.
  eauto.
  eauto.
  eauto.
  unfold not; intros ABS.
  destruct ABS as [f3 [t3 ABS]].
  apply no_dup_not_in_removeEntry with
      g a f3 t3 
    in nd_pf as ND2.
  eauto...
Qed.


Lemma cons_removeEntry_app: forall g a b f1 t1 f2 t2,
    NoDup (domain g) ->
    a <> b ->
    isMap ((a, f1, t1)
             :: (b, f2, t2)
             :: (removeEntry a
                             (removeEntry b g))).
Proof.
  intros g a b f1 t1 f2 t2 nd_pf NEQ.
  apply no_dup_isMap in nd_pf as pf.
  apply no_dup_removeEntry_no_dup with g b
    in nd_pf as nd_pf1.
  remember (removeEntry b g) as g1.
  apply no_dup_removeEntry_no_dup with
      g1 a
    in nd_pf1 as nd_pf2.
  apply no_dup_isMap in nd_pf2 as pf2.
  apply cons_isMap with
       b f2 t2 (removeEntry a g1)
    in pf2 as CONS.
  apply cons_isMap.
  eauto.
  unfold not; intros ABS.
  destruct ABS as [f [t ABS]].
  apply in_inv in ABS.
  destruct ABS as [ABS1 | ABS2].
  inversion ABS1; subst...
  eauto.
  apply no_dup_not_in_removeEntry with
      g1 a f t 
    in nd_pf1 as ND1.
  eauto...
  unfold not; intros ABS.
  destruct ABS as [f [t ABS]].
  apply in_removeEntry with
      b f t a g1 in ABS; subst.
  apply no_dup_not_in_removeEntry with
      g b f t 
    in nd_pf as ND1.
  eauto...
Qed.

Lemma no_dup_cons_removeEntry: forall g b f1 t1,
    NoDup (domain g) ->
    NoDup (domain ((b, f1, t1)
                     :: (removeEntry b g))).
Proof with eauto.
  intros g b f1 t1 nd_pf.
  apply no_dup_removeEntry_no_dup with g b
    in nd_pf as nd_pf1.
  unfold domain; fold domain.
  apply NoDup_cons_iff.
  split. intro. 
  apply in_domain_in_g in H.
  destruct H as [f3 [t3 ABS]].
   apply no_dup_not_in_removeEntry with
      g b f3 t3 
    in nd_pf. intuition.
   assumption.
Qed.

Lemma no_dup_cons_removeEntry_app: forall g a b f1 t1 f2 t2,
    NoDup (domain g) ->
    a <> b ->
    NoDup (domain ((a, f1, t1)
             :: (b, f2, t2)
             :: (removeEntry a
                             (removeEntry b g)))).
Proof with eauto.
  intros g a b f1 t1 f2 t2 nd_pf NEQ.
  apply no_dup_removeEntry_no_dup with g b
    in nd_pf as nd_pf1.
  remember (removeEntry b g) as g1.
  apply no_dup_removeEntry_no_dup with
      g1 a
    in nd_pf1 as nd_pf2.
  unfold domain; fold domain.
  apply NoDup_cons_iff.
  split. intro. 
  apply in_inv in H; intuition.
  apply in_domain_in_g in H0.
  destruct H0 as [f3 [t3 ABS]].
  apply no_dup_not_in_removeEntry with
      g1 a f3 t3 
    in nd_pf1; intuition.
  apply NoDup_cons_iff.
  split. intro.
  rewrite Heqg1 in H.
  apply in_domain_in_g in H.
  destruct H as [f3 [t3 ABS]].
  apply no_dup_not_in_removeEntry with
      g1 b f3 t3 
    in nd_pf1; intuition.
  apply in_removeEntry in ABS...
  apply no_dup_not_in_removeEntry with
      g b f3 t3 
    in nd_pf; intuition.
  assumption.
Qed.

Hint Resolve no_dup_isMap.
Hint Resolve cons_isMap.
Hint Resolve cons_removeEntry.
Hint Resolve cons_removeEntry_app.






(************* NO DUP SPLIT NO DUP ***************)

Lemma count_occ_removeEntry:
  forall a g,
    In a  (domain g) ->
    count_occ
      nat_pair_eq_dec
      (domain (removeEntry a g))
      a + 1=  
    count_occ nat_pair_eq_dec (domain g) a.
Proof with eauto.
  intros.
  induction g. 
  inversion H.
  destruct a0 as [[b f] t]. 
  unfold domain in H. fold domain in H.
  inversion H; subst.
  rewrite removeEntry_head.
  unfold domain; fold domain.
  rewrite count_occ_cons_eq...
  omega.
  intuition...
  unfold domain; fold domain.
  case_eq (pair_eq b a). intros PEQ.
  rewrite count_occ_cons_eq...
  unfold removeEntry. rewrite PEQ.
  omega.
  apply pairEq_eq...
  intros PNEQ.
  rewrite count_occ_cons_neq...
  unfold removeEntry. rewrite PNEQ. fold removeEntry.
  unfold domain; fold domain.
  rewrite count_occ_cons_neq...
  apply pairEq_neq...
  apply pairEq_neq...
Qed.
  
Lemma count_occ_removeEntry_neq:
  forall x a g,
    x <> a ->
    count_occ
      nat_pair_eq_dec
      (domain (removeEntry a g))
      x =  
    count_occ nat_pair_eq_dec (domain g) x.
Proof with eauto.
  intros.
  induction g.
  unfold removeEntry...
  destruct a0 as [[b f] t].
  unfold domain at 2; fold domain. 
  case_eq (pair_eq b a). intros PEQ.
  unfold removeEntry. rewrite PEQ.
  rewrite count_occ_cons_neq...
  assert (b =a). apply pairEq_eq... subst...
  intros PNEQ.
  unfold removeEntry. rewrite PNEQ. fold removeEntry.
  unfold domain; fold domain.
  case_eq (pair_eq b x). intros PEQ.
  rewrite count_occ_cons_eq...
  rewrite IHg.  
  rewrite count_occ_cons_eq...
  apply pairEq_eq...
  apply pairEq_eq...
  intros PNEQ2.
  rewrite count_occ_cons_neq...
  rewrite IHg.
  rewrite count_occ_cons_neq...
  apply pairEq_neq...
  apply pairEq_neq...
Qed.
  
Lemma no_dup_split_no_dup_l:
  forall g1 g2 g pf1 pf2 pf,
    NoDup (domain g) ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    NoDup (domain g1).
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
    (*$ Show Existentials. $*)
    Existential 3:=nat_pair_eq_dec.
    apply count_occ_removeEntry  in IN.

    assert (count_occ nat_pair_eq_dec
                      (domain (removeEntry n g1)) n > 0 ->
            False); unfold not. intros ABS.
    rewrite <-count_occ_In  in ABS.
    apply in_domain_in_g in ABS.
    destruct ABS as [f1 [t1 ABS]].
    destruct t1.
    specialize  tsub_payload with
        (removeEntry n g1) (removeEntry n g2) (removeEntry n g3)
        pf' pf'' pf''' (fst n) (snd n) f1 m p0 t1
      as TSUB.
    rewrite <-surjective_pairing in TSUB; intuition.
    destruct H7 as [q1 ABS2].
    inversion ABS2; subst.
    apply no_dup_not_in_removeEntry with
        g3 n f0 (Chan m q1 t1)
      in nd_pf ; eauto.
    specialize  tsub_top with
        (removeEntry n g1) (removeEntry n g2) (removeEntry n g3)
        pf' pf'' pf''' (fst n) (snd n) f1
      as TSUB.
    rewrite <-surjective_pairing in TSUB; intuition.
    inversion H7; subst.
    apply no_dup_not_in_removeEntry with
        g3 n f0 Top
      in nd_pf ; eauto.
    intuition.

    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    assert (PNEQ2 : x <> n) by auto.
    apply count_occ_removeEntry_neq with (g := g1)
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
    apply count_occ_removeEntry  in IN.

    assert (count_occ nat_pair_eq_dec
                      (domain (removeEntry n g1)) n > 0 ->
            False); unfold not. intros ABS.
    rewrite <-count_occ_In  in ABS.
    apply in_domain_in_g in ABS.
    destruct ABS as [f1 [t1 ABS]].
    destruct t1.
    specialize  tsub_payload with
        (removeEntry n g1) (removeEntry n g2) (removeEntry n g3)
        pf' pf'' pf''' (fst n) (snd n) f1 m p0 t1
      as TSUB.
    rewrite <-surjective_pairing in TSUB; intuition.
    destruct H6 as [q1 ABS2].
    inversion ABS2; subst.
    apply no_dup_not_in_removeEntry with
        g3 n f0 (Chan m q1 t1)
      in nd_pf ; eauto.
    specialize  tsub_top with
        (removeEntry n g1) (removeEntry n g2) (removeEntry n g3)
        pf' pf'' pf''' (fst n) (snd n) f1
      as TSUB.
    rewrite <-surjective_pairing in TSUB; intuition.
    inversion H6; subst.
    apply no_dup_not_in_removeEntry with
        g3 n f0 Top
      in nd_pf ; eauto.
    intuition.

    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    assert (PNEQ2 : x <> n) by auto.
    apply count_occ_removeEntry_neq with (g := g1)
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
    apply count_occ_removeEntry  in IN.

    assert (count_occ nat_pair_eq_dec
                      (domain (removeEntry n g1)) n > 0 ->
            False); unfold not. intros ABS.
    rewrite <-count_occ_In  in ABS.
    apply in_domain_in_g in ABS.
    destruct ABS as [f1 [t1 ABS]].
    destruct t1.
    specialize  tsub_payload with
        (removeEntry n g1) (removeEntry n g2) (removeEntry n g3)
        pf' pf'' pf''' (fst n) (snd n) f1 m p t1
      as TSUB.
    rewrite <-surjective_pairing in TSUB; intuition.
    destruct H6 as [q1 ABS2].
    inversion ABS2; subst.
    apply no_dup_not_in_removeEntry with
        g3 n f0 (Chan m q1 t1)
      in nd_pf ; eauto.
    specialize  tsub_top with
        (removeEntry n g1) (removeEntry n g2) (removeEntry n g3)
        pf' pf'' pf''' (fst n) (snd n) f1
      as TSUB.
    rewrite <-surjective_pairing in TSUB; intuition.
    inversion H6; subst.
    apply no_dup_not_in_removeEntry with
        g3 n f0 Top
      in nd_pf ; eauto.
    intuition.

    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    assert (PNEQ2 : x <> n) by auto.
    apply count_occ_removeEntry_neq with (g := g1)
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

Lemma no_dup_split_no_dup_r:
  forall g1 g2 g pf1 pf2 pf,
    NoDup (domain g) ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    NoDup (domain g2).
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
    (*$ Show Existentials.$*)
    Existential 3:=nat_pair_eq_dec.
    apply count_occ_removeEntry  in IN.

    assert (count_occ nat_pair_eq_dec
                      (domain (removeEntry n g2)) n > 0 ->
            False); unfold not. intros ABS.
    rewrite <-count_occ_In  in ABS.
    apply in_domain_in_g in ABS.
    destruct ABS as [f1 [t1 ABS]].
    destruct t1.
    specialize  tsub_payload_r with
        (removeEntry n g1) (removeEntry n g2) (removeEntry n g3)
        pf' pf'' pf''' (fst n) (snd n) f1 m p0 t1
      as TSUB.
    rewrite <-surjective_pairing in TSUB; intuition.
    destruct H7 as [q1 ABS2].
    inversion ABS2; subst.
    apply no_dup_not_in_removeEntry with
        g3 n f0 (Chan m q1 t1)
      in nd_pf ; eauto.
    specialize  tsub_top_r with
        (removeEntry n g1) (removeEntry n g2) (removeEntry n g3)
        pf' pf'' pf''' (fst n) (snd n) f1
      as TSUB.
    rewrite <-surjective_pairing in TSUB; intuition.
    inversion H7; subst.
    apply no_dup_not_in_removeEntry with
        g3 n f0 Top
      in nd_pf ; eauto.
    intuition.

    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    assert (PNEQ2 : x <> n) by auto.
    apply count_occ_removeEntry_neq with (g := g2)
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
    apply count_occ_removeEntry  in IN.

    assert (count_occ nat_pair_eq_dec
                      (domain (removeEntry n g2)) n > 0 ->
            False); unfold not. intros ABS.
    rewrite <-count_occ_In  in ABS.
    apply in_domain_in_g in ABS.
    destruct ABS as [f1 [t1 ABS]].
    destruct t1.
    specialize  tsub_payload_r with
        (removeEntry n g1) (removeEntry n g2) (removeEntry n g3)
        pf' pf'' pf''' (fst n) (snd n) f1 m p0 t1
      as TSUB.
    rewrite <-surjective_pairing in TSUB; intuition.
    destruct H6 as [q1 ABS2].
    inversion ABS2; subst.
    apply no_dup_not_in_removeEntry with
        g3 n f0 (Chan m q1 t1)
      in nd_pf ; eauto.
    specialize  tsub_top_r with
        (removeEntry n g1) (removeEntry n g2) (removeEntry n g3)
        pf' pf'' pf''' (fst n) (snd n) f1
      as TSUB.
    rewrite <-surjective_pairing in TSUB; intuition.
    inversion H6; subst.
    apply no_dup_not_in_removeEntry with
        g3 n f0 Top
      in nd_pf ; eauto.
    intuition.

    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    assert (PNEQ2 : x <> n) by auto.
    apply count_occ_removeEntry_neq with (g := g2)
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
    apply count_occ_removeEntry  in IN.

    assert (count_occ nat_pair_eq_dec
                      (domain (removeEntry n g2)) n > 0 ->
            False); unfold not. intros ABS.
    rewrite <-count_occ_In  in ABS.
    apply in_domain_in_g in ABS.
    destruct ABS as [f1 [t1 ABS]].
    destruct t1.
    specialize  tsub_payload_r with
        (removeEntry n g1) (removeEntry n g2) (removeEntry n g3)
        pf' pf'' pf''' (fst n) (snd n) f1 m p t1
      as TSUB.
    rewrite <-surjective_pairing in TSUB; intuition.
    destruct H6 as [q1 ABS2].
    inversion ABS2; subst.
    apply no_dup_not_in_removeEntry with
        g3 n f0 (Chan m q1 t1)
      in nd_pf ; eauto.
    specialize  tsub_top_r with
        (removeEntry n g1) (removeEntry n g2) (removeEntry n g3)
        pf' pf'' pf''' (fst n) (snd n) f1
      as TSUB.
    rewrite <-surjective_pairing in TSUB; intuition.
    inversion H6; subst.
    apply no_dup_not_in_removeEntry with
        g3 n f0 Top
      in nd_pf ; eauto.
    intuition.

    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    assert (PNEQ2 : x <> n) by auto.
    apply count_occ_removeEntry_neq with (g := g2)
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
