Require Import
        Bool List Lia PeanoNat Program.Equality
        ListAddOns Max RemoveEntry Domain
        header
        operations pi_syntax
        pairEq type_system semantics 
        type_operations_1
        split_exists_neutral
        sub_split
        split_existential
        no_dup_split_no_dup
        proposition27
        split_not_exists
        split_operations
        lts_operations
        split_operations_2
        split_operations_3
        disjoint_newEntries.




Lemma incl_incl : forall A (l : list A),
    incl l l.
Proof with eauto. unfold incl in *; dependent induction l...
Qed. 


Lemma rec_newEntries : forall g l m,
    (fun  (g : typeEnv) (l : list (name * name)) (max : name) =>
       match l with
       | nil => nil
       | (a1, a2) :: tail =>
         let (_, notNew) := InB (a1, a2) g in
         if notNew
         then newEntries g tail max
         else
           let (pair, _) := InB (a1, a2 - max) g in
           (a1, a2, fst pair, snd pair) :: newEntries g tail max
       end) g l m = 
    (fix newEntries (g : typeEnv) (l : list (name * name)) (max : name) {struct l} :
       typeEnv :=
       match l with
       | nil => nil
       | (a1, a2) :: tail =>
         let (_, notNew) := InB (a1, a2) g in
         if notNew
         then newEntries g tail max
         else
           let (pair, _) := InB (a1, a2 - max) g in
           (a1, a2, fst pair, snd pair) :: newEntries g tail max
       end) g l m.
Proof.
  intros.
  destruct l; simpl; auto.
Qed.


Lemma not_in_newEntries: forall a g l M,
    ~ In a l ->
    max (domain g) <= M ->
    ~ In a (domain (newEntries g l M)).
Proof with eauto.
  intros a g l M NIN MAX ABS.
  induction l.
  simpl in ABS...
  destruct a0; simpl in ABS.
  eapply not_in_cons in NIN; intuition.
  case_eq (InB (n, n0) g); intros;
    case_eq b; intros; subst; rewrite H2 in *; intuition.
  destruct (InB (n, n0 - M)); simpl in ABS; repeat intuition.
Qed.

#[global] Hint Resolve not_in_newEntries.
  
  
Lemma newEntries_no_dup: forall g q,
    NoDup (secLabs q) ->
    NoDup (domain g) ->
   NoDup (domain (newEntries g (secLabs q) (max (domain g)))).
Proof with eauto.
  intros g q nd_pf pf.
  induction (secLabs q).
  simpl...
  simpl. destruct a.
  eapply NoDup_cons_iff in nd_pf as (K1 &K2).
  case_eq (InB (n, n0) g); intros.
  case_eq b; intros...
  destruct (InB (n, n0 - max (domain g)) g).
  simpl; subst.
  eapply NoDup_cons_iff...
  Qed.
  
  
Lemma no_dup_sl_par : forall p q,
    NoDup (secLabs (dPar p q)) ->
    NoDup (secLabs p) /\  NoDup (secLabs q).
Proof.
  intros. unfold secLabs in H. fold secLabs in H.
  apply no_dup_distr in H. destruct H as [H1 H2].
  auto.
Qed.

#[global] Hint Resolve no_dup_sl_par.

  
#[global] Hint Resolve max_sl_par max_sl_bang max_sl_nu sl_pos_nu.


Lemma distr_no_dup : forall A (l m : list A),
    NoDup l -> NoDup m ->
    disjoint l m ->
    NoDup (l ++ m).
Proof with eauto.
  intros.
  induction l; induction m...
  assert ((a :: l) ++ nil = a :: l).
  erewrite app_nil_end...
  erewrite H2...
  assert ((a :: l) ++ a0 :: m = a :: l ++ a0 :: m)...
  rewrite H2; eapply NoDup_cons_iff.
  split.
  intros ABS.
  eapply in_app_iff in ABS as [K1 | K2].
  eapply NoDup_cons_iff in H; intuition.
  inversion K2; subst.
  eapply disjoint_r_cons in H1 as [_ ABS]; intuition.
  eapply disjoint_l_cons in H1; intuition.
  eapply NoDup_cons_iff in H as [_ K2].
  eapply disjoint_l_cons in H1 as [K1 _]...
Qed.
  
Lemma no_dup_sl_bang: forall a1 a2 x1 x2 p,
    NoDup (secLabs (dBang a1 a2 x1 x2 p)) ->
    NoDup (secLabs p).
Proof with eauto.
  intros. simpl in H...
Qed.

#[global] Hint Resolve no_dup_sl_bang.



Lemma in_removeEntry_cons_iff_0 : forall g b1 b2 f t,
    NoDup (domain g) ->
    In (b1, b2, f, t) g ->
    forall x,
      In x g <-> In x ((b1, b2, f, t) :: removeEntry (b1, b2) g).
Proof with eauto.
  intros g b1 b2 f t ND IN [[[x1 x2] f1] t1].
  unfold iff;split; intros IN2.
  - case_eq (pair_eq (x1, x2) (b1, b2)); intros PEQ.
    rewrite <-pairEq_eq in PEQ; inversion PEQ; subst.
    assert (EQ: f = f1 /\ t = t1).
    eapply in_isMap... destruct EQ. subst...
    erewrite <-pairEq_neq in PEQ. 
    right...
    eapply removeEntry_in...
  - inversion IN2. inversion H; subst...
    eapply in_removeEntry...
Qed.
  
Lemma in_removeEntry_cons_iff : forall g b1 b2 f t,
    NoDup (domain g) ->
    In (b1, b2) (domain g) ->
    forall x : name * name,
      In x (domain g) <-> In x (domain ((b1, b2, f, t) :: removeEntry (b1, b2) g)).
Proof with eauto.
  intros;  unfold iff;split; intros IN2. 
   - simpl.
    case_eq (pair_eq x (b1, b2)); intros PEQ.
    rewrite <-pairEq_eq in PEQ; inversion PEQ; subst...
    erewrite <-pairEq_neq in PEQ. 
    right...
     eapply in_domain_in_g in IN2 as (f1 &t1 &IN2).
    eapply in_g_in_domain,removeEntry_in...
   - simpl in IN2. destruct IN2 as [EQ | IN].
     subst...
      eapply in_domain_in_g in IN as (f1 &t1 &IN2).
      eapply in_g_in_domain...
Qed.
      
Lemma incl_removeEntry_cons :  forall g l b1 b2 f t, 
    NoDup (domain g) ->
    In (b1, b2) (domain g) ->
    incl_ l (domain g) ->
    incl_ l (domain ((b1, b2, f, t) :: removeEntry (b1, b2) g)).
Proof with eauto.
  intros g l b1 b2 f t ND IN INCL.
  simpl.
  destruct l.
  - intros; unfold incl_ ; intros; inversion H.
  - intros; (*destruct a as [a1 a2]*)
  unfold incl_; intros x IN2; split.
  inversion IN2; subst.
  + assert (IN3: In x (domain g)).
  eapply INCL...
  case_eq ( pair_eq x (b1, b2)); intros PEQ. rewrite <-pairEq_eq in PEQ; subst...
  rewrite <-pairEq_neq in PEQ.
  right. eapply in_domain_in_g in IN3 as (ff &tt &IN3).
  eapply in_g_in_domain,removeEntry_in...
  + eapply incl_pres in INCL...
    eapply in_split in H as (l1 & l2 &EQ); subst.
    case_eq ( pair_eq x (b1, b2)); intros PEQ. rewrite <-pairEq_eq in PEQ; subst...
    rewrite <-pairEq_neq in PEQ.
    assert (IN3: In x (domain g)).
    eapply INCL... eapply in_app_iff; right...
    right. eapply in_domain_in_g in IN3 as (ff &tt &IN3).
    eapply in_g_in_domain,removeEntry_in...
  + assert (ND1 : NoDup (p :: l)).
    eapply incl_preserves_no_dup...
    assert (ND2 : NoDup ((b1, b2) :: domain (removeEntry (b1, b2) g))).
    eapply no_dup_cons_removeEntry...
    eapply NoDup_count_occ with (decA := nat_pair_eq_dec) (x := x) in ND1.
    eapply NoDup_count_occ with (decA := nat_pair_eq_dec) (x := x) in ND2.
    assert (IN1 := IN2).
    erewrite count_occ_In with (eq_dec :=nat_pair_eq_dec) (x := x) in IN2.
    assert (EQ: count_occ nat_pair_eq_dec (p :: l) x = 1) by lia.
    rewrite EQ.
    assert (IN3: In x (domain g)).
    eapply INCL...
    assert (IN4:  In x ((b1, b2) :: domain (removeEntry (b1, b2) g))).
     case_eq ( pair_eq x (b1, b2)); intros PEQ. rewrite <-pairEq_eq in PEQ; subst...
    rewrite <-pairEq_neq in PEQ.
    right. eapply in_domain_in_g in IN3 as (ff &tt &IN3).
    eapply in_g_in_domain,removeEntry_in...
    erewrite count_occ_In with (eq_dec :=nat_pair_eq_dec) (x := x) in IN4.
    assert (EQ2: count_occ nat_pair_eq_dec ((b1, b2) :: domain (removeEntry (b1, b2) g)) x = 1) by lia.
    rewrite EQ2...
    Unshelve. all:eauto.
Qed.



#[global] Hint Resolve max_removeEntry_cons max_removeEntry_cons_app
     in_g_in_domain.

 (* Lemma ex_falso: forall T:Type, False -> T.
  inversion 1.
    QQed.
    
    Lemma disjoint_2_app_l : forall A (l1 l2 m : list A),
      disjoint_2 (l1 ++ l2) m -> disjoint_2 l1 m.
  Proof.
    intros.
    induction l1; econstructor.

    simpl; auto. 
    eapply disjoint_2_cons_l  in H.
    intuition. 
  QQed.

Lemma disjoint_absurd {A}: forall x (l m : list A) P,
        disjoint l m  -> In x l -> In x m -> P.
Proof with eauto.
    intros. apply ex_falso.
      eapply in_split in H0 as (l1 &l2 &ABS1).
       eapply in_split in H1 as (m1 &m2 &ABS2).
       subst. 
       eapply disjoint_app_r,disjoint_l_cons in H as [_ ABS].
       assert ( In x (m1 ++ x :: m2)).
       eapply in_app_iff; right...
       contradiction.
QQed.
*)

Lemma lts_no_dup :
  forall g p a g' p' nd_pf
         (pf_incl : incl_ (secLabs p) (domain g)),
    lts g p a g' p' nd_pf ->
    sl_pos p ->
    NoDup (secLabs p) ->
    max (secLabs p) <= max (domain g) ->
    NoDup (domain g').
Proof with eauto.
  intros g p a g' p' nd_pf pf_incl LTS SLP NDSL MAX.
  dependent induction LTS.
  - apply sl_pos_par_l in SLP.
    unfold secLabs in pf_incl; fold secLabs in pf_incl.
    apply incl2_distr in pf_incl. intuition.
    assert ( NoDup (secLabs p1)).
    eapply no_dup_sl_par with (q := q)...
    apply max_sl_par in MAX. intuition.
    intuition.
  - remember pf as nd_pf; subst pf.
    apply no_dup_cons_removeEntry_app with
        g (a1, a2) (b1, b2)
        vis (Chan lin empty t)
        vis t2
      in nd_pf as ISMAP.
    eauto.
    assert (ABS : t1 = Chan lin out t -> False); intros.
    inversion H; subst.
    inversion H3; subst.
    assert (K := nonRecTypes).
    destruct K as [NR1 NR2].
    eauto.
    assert (K := nonRecTypes).
    destruct K as [NR1 NR2].
    eauto.
    unfold not; intros ABS2.
    rewrite <-ABS2 in H1.
    apply no_dup_isMap in nd_pf as pf.
    apply type_of_map with
        g (a1, a2) (Chan lin out t) t1 in pf...
  - eapply no_dup_cons_removeEntry...
  - remember pf as nd_pf; subst pf.
    apply no_dup_isMap in nd_pf as pf.
    apply no_dup_cons_removeEntry_app with
        g (a1, a2) (b1, b2)
        vis (Chan lin empty t)
        vis t2
      in nd_pf as ISND.
    assumption.
    assert (ABS : t1 = Chan lin inp t -> False); intros.
    inversion H; subst.
    inversion H4.
    inversion H; subst.
    assert (K := nonRecTypes).
    destruct K as [NR1 NR2].
    specialize NR1 with lin p2 t0 as ABS; intuition.
    inversion H; subst.
    unfold not; intros ABS2.
    rewrite <-ABS2 in H2.
    apply type_of_map with
        g (a1, a2) (Chan lin inp t) t1 in pf as ABS3.
    intuition.
    eauto.
    eauto.
  - eapply no_dup_cons_removeEntry...
  - subst q.
    specialize new_entries_disjoint with g p pf as NED.
    remember (dep_relabel p (domain g) pf) as q.
    remember pf as nd_pf; subst pf. 
    clear H.
    unfold sl_pos in SLP; unfold secLabs in SLP; fold secLabs in SLP; fold sl_pos in SLP; intuition.
    
    remember
      (newEntries g (secLabs q) (max (domain g)))
      as m.
    assert (NDDISTR := distr_no_dup). 
    rewrite domain_distr.
    apply NDDISTR with (l := (domain m)). clear NDDISTR.
    
    + assert (NDSL2 : NoDup (secLabs p)).
      eapply no_dup_sl_bang...
      rewrite Heqm; apply newEntries_no_dup.
      all:eauto.
      rewrite Heqq.
      specialize prop27 with p (domain g) nd_pf as P27.
      assert (incl_ (secLabs p) (domain g))...
    + eapply no_dup_cons_removeEntry...
    + clear NDDISTR.
      apply disjoint_car; apply disjoint_2_comm; apply disjoint_car.
      specialize new_entries_disjoint with g p nd_pf as NED.
      rewrite <-Heqq in NED; rewrite <-Heqm in NED. 
      unfold domain; fold domain.
      eapply max_sl_bang in MAX as MAX1.
      intuition.
      assert (~ In (b1, b2) (domain m)).
      intros ABS. eapply disjoint_absurd...
      eapply disjoint_cons_removeEntry...
  - apply sl_pos_par_r in SLP.
    assert (max (domain g) <= max (domain ((a1, a2, vis, Chan lin inp t) :: (b1, b2, vis, s1) :: g0))).
    subst g0...
    assert (max (domain g) =
  max
    (domain
       ((a1, a2, vis, Chan lin inp t)
          :: (b1, b2, vis, s1) :: removeEntry (a1, a2) (removeEntry (b1, b2) g))))...
    lia.
    assert ( max (secLabs q1) <=
             max (domain ((a1, a2, vis, Chan lin inp t) :: (b1, b2, vis, s1) :: g0)) ); apply max_sl_par in MAX; intuition.
  - apply sl_pos_par_r in SLP.
    assert (max (domain g) <= max (domain ((a1, a2, vis, Chan lin inp t) :: (b1, b2, ill, s1) :: g0))).
    subst g0...
    assert (max (domain g) =
  max
    (domain
       ((a1, a2, vis, Chan lin inp t)
          :: (b1, b2, ill, s1) :: removeEntry (a1, a2) (removeEntry (b1, b2) g))))...
    lia.
    apply max_sl_par in MAX; 
      apply no_dup_sl_par in NDSL;
      intuition. 
  - apply sl_pos_par_r in SLP.
    assert (max (domain g) <= max (domain g')).
    subst g' g0.
    assert (max (domain g) = max (domain ((b1, b2, vis, s1) :: removeEntry (b1, b2) g)))... lia. 
    apply max_sl_par in MAX; 
      apply no_dup_sl_par in NDSL. intuition.
    assert (incl_ (secLabs q1) (domain g) /\ incl_ (secLabs p1) (domain g)).
    eapply incl2_distr.
    unfold secLabs in pf_incl; fold secLabs in pf_incl...
    eauto.
    assert ( incl_ (secLabs q1) (domain g')).
    subst g' g0; intuition; eapply  incl_removeEntry_cons...
    intuition. 
  - apply sl_pos_par_r in SLP.
    assert (max (domain g) <= max (domain g')).
    subst g' g0.
    assert (max (domain g) = max (domain ((b1, b2, ill, s1) :: removeEntry (b1, b2) g)))... lia.
    apply max_sl_par in MAX; 
    apply no_dup_sl_par in NDSL.
    assert (incl_ (secLabs q1) (domain g')).
    subst g' g0; intuition;
      eapply incl_removeEntry_cons...
    unfold secLabs in pf_incl; fold secLabs in pf_incl; eapply incl2_distr in pf_incl; intuition...
    intuition.
    assert (max (secLabs q1) <= max (domain g')).
    lia.
    intuition.
    eapply no_dup_cons_removeEntry... 
  - assert (incl_ (secLabs p) (domain ((b1, b2, vis, t) :: removeEntry (b1, b2) g))).
    eapply incl_removeEntry_cons ...
    (*specialize incl_removeEntry_cons with g (secLabs p) b1 b2 vis t; intuition. assert (incl_ (secLabs p) (domain g)).
     *)
    unfold secLabs in pf_incl; fold secLabs in pf_incl.
    eapply incl2_distr in pf_incl.
    intuition.
    intuition.
    eapply IHLTS...
    simpl in NDSL; eapply no_dup_iff in NDSL; intuition.
    assert (max (secLabs p) <= max (domain g))...
    assert (max (domain g) = max (domain ((b1, b2, vis, t) :: removeEntry (b1, b2) g))).
    eapply max_same_domain.
    eapply in_removeEntry_cons_iff...
    lia.
  - repeat rewrite domain_distr in *; simpl in *; try eapply IHLTS; try eapply no_dup_iff in NDSL as [NDSL_]...
    eapply incl2_distr in pf_incl as [INCL1 INCL2];
      subst; rewrite domain_distr in *; simpl in *...
     subst; rewrite domain_distr in *; simpl in *...
Qed.
