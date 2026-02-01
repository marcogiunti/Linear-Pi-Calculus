Require Import
        Bool List Omega PeanoNat Program.Equality
        ListAddOns Max Domain
        header pairEq
        operations pi_syntax type_system.

Require Import CpdtTactics LibTactics.

Lemma no_dup_domain_cons: forall a g,
    NoDup (domain (a :: g)) -> NoDup (domain g).
Proof.
  intros e g nd_pf.
  destruct e as [[a f] t].
  unfold domain in nd_pf; fold domain in nd_pf.
  apply no_dup_distr with
      (l1 := a :: nil) in nd_pf; intuition.
Qed.


Lemma no_dup_domain_not_exists: forall a f t g,
    NoDup (domain ((a, f, t) :: g)) ->
    ~exists f2 t2,
        In (a, f2, t2) g.
Proof.
  unfold not. intros a f t g nd_pf ABS.
  destruct ABS as [f2 [t2 ABS]].
  unfold domain in nd_pf; fold domain in nd_pf.
  apply in_g_in_domain in ABS.
  specialize no_dup_app_r with
      (l1 := nil) (x:=a) (y:= a) (l2 := domain g)
    as ND.
  intuition.
Qed.

Lemma in_removeEntry : forall x f t y g,
    In (x, f, t) (removeEntry y g) ->
    In (x, f, t) g.
Proof.
  intros.
  dependent induction g.
  unfold removeEntry in H; fold removeEntry in H; inversion H.
  destruct a. destruct p.
  remember p as a. subst p.
  case_eq (pair_eq y a).
  intros PEQ. assert (PEQ2 := PEQ).
  rewrite <-pairEq_eq in PEQ; subst.
  unfold removeEntry in H.
  rewrite PEQ2 in H.
  apply in_cons with
      (a := (a, f0, p0)) in H; assumption.
  intros PNEQ. assert (PEQ2 := PNEQ).
  rewrite <-pairEq_neq in PNEQ.
  unfold removeEntry in H.
  assert (COMM : a <> y); auto...  
  rewrite pairEq_neq in COMM; rewrite COMM in H.
  fold removeEntry in H.
  apply in_inv in H.
  destruct H. rewrite H. apply in_eq.
  intuition.
Qed.

Lemma removeEntry_in:
  forall x f t y g,
    x <> y ->
    In (x, f, t) g ->
    In (x, f, t) (removeEntry y g).
Proof.
  intros x f t y g NEQ IN.
  generalize dependent t.
  generalize dependent f.
  generalize dependent x.
  generalize dependent y.
  dependent induction g.
  intros.
  inversion IN.
  intros.
  destruct a. destruct p as [a f1].
  case_eq (pair_eq a x).
  - intros PEQ. assert (PEQ2 := PEQ).
    rewrite <-pairEq_eq in PEQ; subst.
    unfold removeEntry.
    assert (NEQ2 := NEQ).
    rewrite pairEq_neq in NEQ; rewrite NEQ.       
    fold removeEntry.
    apply in_inv in IN as [IN | IN].
    inversion IN; subst; apply in_eq.
    apply IHg with y x f t in NEQ2.
    apply in_cons; intuition.
    assumption.
  -  intros PNEQa. 
     rewrite <-pairEq_neq in PNEQa.
     case_eq (pair_eq a y).
     + intros PEQ. assert (PEQ2 := PEQ).
       rewrite <-pairEq_eq in PEQ; subst.
       unfold removeEntry; rewrite PEQ2; fold removeEntry.
       apply in_inv in IN; intuition; eauto...
       inversion H; intuition.
     + intros PNEQ.
       unfold removeEntry. rewrite PNEQ; fold removeEntry.
       apply in_inv in IN; intuition; eauto...
       inversion H; intuition.
Qed.

Lemma no_dup_removeEntry_no_dup:
  forall g a,
    NoDup (domain g) ->
    NoDup (domain (removeEntry a g)).
Proof with eauto using in_removeEntry.
  intros.
  dependent induction g.
  unfold removeEntry...
  apply no_dup_domain_cons in H as K.
  specialize IHg with a0; apply IHg in K as H1.
  unfold removeEntry; fold removeEntry.
  destruct a as [[a f] t].
  case_eq (pair_eq a a0); intros BEQ.
  assumption.  
  unfold domain; fold domain...
  apply no_dup_domain_not_exists in H; apply IHg in K.
  apply NoDup_cons_iff...
  intuition.
  apply in_domain_in_g in H0.
  destruct H. destruct H0 as [f1 [t1 ABS]].
  exists f1; exists  t1.
  rewrite <-pairEq_neq in BEQ...
Qed.

Lemma removeEntry_twice : forall a1 a2 b1 b2 f t f1 t1 g1,
    (a1, a2) <> (b1, b2) ->
    removeEntry
      (a1, a2)
      (removeEntry
         (b1, b2)
         ((a1, a2, f, t) :: (b1, b2, f1, t1) :: g1)) =
    g1.
Proof with eauto.
  intros.
  unfold removeEntry at 2.
  specialize pairEq_eq with (b1, b2) (b1, b2) as BEQ. intuition. rewrite H2.
  specialize pairEq_neq with (a1, a2) (b1, b2) as BEQ; intuition.
  rewrite H4; simpl.
  specialize pairEq_eq with (a1, a2) (a1, a2) as BEQ. intuition. rewrite H6...
Qed.

Lemma no_dup_not_in_removeEntry:
  forall g a f t,
    NoDup (domain g) ->
    ~ In (a, f, t) (removeEntry a g).
Proof with eauto.
  intros g a f t nd_pf.
  unfold not; intros ABS.
  dependent induction g.
  unfold removeEntry...
  destruct a as [n t1]. destruct n as [n f1].
  destruct a0 as [a1 a2].
  case_eq (pair_eq n (a1, a2)).
  intro PEQ; assert (PEQ2 := PEQ);
    rewrite <-pairEq_eq in PEQ; subst n.
  unfold removeEntry in ABS.
  rewrite PEQ2 in ABS.
  unfold domain in nd_pf; fold domain in nd_pf.
  specialize no_dup_app_r with
      (x := (a1, a2)) (y := (a1, a2))
      (l1 := nil) (l2 := (domain g))
    as ND.
  apply in_g_in_domain in ABS; unfold domain in ABS; intuition.
  intros PNEQ. assert (PNEQ2 := PNEQ).
  rewrite <-pairEq_neq in PNEQ.
  assert (COMM : (a1, a2) <>n); intuition.
  unfold domain in nd_pf; fold domain in nd_pf.
  apply no_dup_iff with (l1 := n:: nil) in nd_pf.
  unfold removeEntry in ABS; fold removeEntry in ABS.
  rewrite PNEQ2 in ABS.
  intuition.
  apply in_inv in ABS.
  destruct ABS as [ABS1 | ABS2].
  inversion ABS1...
  specialize IHg with (a1, a2) f t; intuition.
Qed.

Lemma domain_distr : forall g1 g2,
    domain (g1 ++ g2) = domain g1 ++ domain g2.
Proof.
  intros. induction g1, g2.
  unfold domain. fold domain. auto...
  rewrite app_nil_l with (l := p :: g2).
  unfold domain at 2; auto...
  rewrite app_nil_r with (l := a :: g1).
  unfold domain at 3.
  rewrite app_nil_r with (l := domain (a :: g1)); auto...
  assert ((a :: g1) ++ p :: g2 = a :: g1 ++ p :: g2) by auto...
  rewrite H. 
  unfold domain at 1. fold domain.
  induction a.
  induction a.
  unfold domain at 2; fold domain.
  rewrite IHg1; auto...
Qed.

Lemma removeEntry_head : forall a f t g,
    removeEntry a ((a, f, t) :: g) = g.
Proof.
  intros.
  unfold removeEntry; fold removeEntry.
  specialize pairEq_eq with a a as PEQ; intuition.
  rewrite H1; simpl; tauto.
Qed.



Lemma removeEntry_length_0: forall b1 b2 g,
    In (b1, b2) (domain g) ->
    S(List.length (removeEntry (b1, b2) g))=
    List.length g.
Proof with eauto.
  intros. dependent induction g.
  inversion H.
  unfold domain in H; fold domain in H;  destruct a as [[[a1 a2] f]t].
  case_eq (pair_eq (a1,a2)(b1,b2)). intros PEQ.
  unfold removeEntry; rewrite PEQ; fold removeEntry...
  intros PNEQ.
  unfold removeEntry; rewrite PNEQ; fold removeEntry.
  simpl.
  rewrite <-IHg...
  rewrite <-pairEq_neq in PNEQ.
  inversion H... contradiction.
Qed.

Lemma removeEntry_length_1: forall b1 b2 g,
    ~In (b1, b2) (domain g) ->
    List.length (removeEntry (b1, b2) g)=
    List.length g.
Proof with eauto.
  intros. dependent induction g.
  unfold removeEntry...
  
  unfold domain in H; fold domain in H;  destruct a as [[[a1 a2] f]t]. eapply not_in_cons in H as [H K].
  simpl.
  assert (DIFF:  (a1, a2) <> (b1, b2))... 
  rewrite pairEq_neq in DIFF.
  rewrite DIFF. simpl.
  assert (S (Datatypes.length (removeEntry (b1, b2) g)) = S (Datatypes.length g) ->
          Datatypes.length (removeEntry (b1, b2) g) =  (Datatypes.length g))...
Qed.


Lemma removeEntry_length: forall b1 b2 b3 b4 g,
    In (b1, b2) (domain g) ->
    In (b3, b4) (domain g) ->
    List.length (removeEntry (b1, b2) g)=
    List.length (removeEntry (b3, b4) g).
Proof with eauto.
  intros.
  assert (S (Datatypes.length (removeEntry (b1, b2) g)) = S(Datatypes.length (removeEntry (b3, b4) g)) ->
          Datatypes.length (removeEntry (b1, b2) g) = Datatypes.length (removeEntry (b3, b4) g))...
  assert (REM: S (Datatypes.length (removeEntry (b1, b2) g)) =
               S (Datatypes.length (removeEntry (b3, b4) g))).
  rewrite removeEntry_length_0,removeEntry_length_0...
  intuition.
Qed.

Hint Resolve in_eq.

Lemma removeEntry_app_notIn:
  forall b1 b2 f t f2 s g k,
    NoDup
      (domain
         ((b1, b2, f, t)
            :: removeEntry (b1, b2)
            (k ++
               (b1, b2, f2, s) :: g))) ->
    ~In (b1, b2) (domain k).
Proof with eauto.
  intros.
  unfold domain in H; fold domain in H.
  induction k.
  eauto.
  destruct a as [[[a1 a2] ff] tt].
  assert (EQ: ((a1, a2, ff, tt) :: k) ++ (b1, b2, f2, s) :: g = (a1, a2, ff, tt) :: k ++ (b1, b2, f2, s) :: g)...
  rewrite EQ in H.
  case_eq (pair_eq (a1, a2)(b1,b2)). intros PEQ.
  
  unfold removeEntry in H; rewrite PEQ in H; fold removeEntry in H.
  inversion H; subst.
  assert (In (b1, b2) (domain (k ++ (b1, b2, f2, s) :: g))).
  erewrite domain_distr,in_app_iff; unfold domain; fold domain; right...
  contradiction.

  intros PNEQ.
  unfold removeEntry in H; rewrite PNEQ in H; fold removeEntry in H.
  intros ABS. elim ABS. eapply pairEq_neq...
  eapply IHk.

  unfold domain in H; fold domain in H.
  inversion H; subst.
  inversion H3; subst.
  eapply NoDup_cons...
  erewrite not_in_cons in H2...  intuition.
Qed.

Lemma removeEntry_shift : forall a1 a2 b1 b2 f s g,
    (a1, a2) <> (b1, b2) ->
    (b1, b2, f, s) :: removeEntry (a1, a2) g =
    removeEntry (a1, a2) ((b1, b2, f, s) ::g).
Proof with eauto.
  intros.
  unfold removeEntry at 2.
  assert (PNEQ : (b1, b2) <> (a1, a2))...
  apply pairEq_neq in PNEQ.
  rewrite PNEQ. fold removeEntry...
Qed.



Lemma removeEntry_app_shift: forall b1 b2 k g,
    ~In (b1, b2) (domain k)  ->
    removeEntry (b1, b2) (k ++ g) = k ++ removeEntry (b1, b2) g.
Proof with eauto.
  intros. induction k...
  unfold domain in H; fold domain in H;  destruct a as [[[a1 a2] f]t]. eapply not_in_cons in H as [H K].
  simpl.
  assert (DIFF:  (a1, a2) <> (b1, b2))... 
  rewrite pairEq_neq in DIFF.
  rewrite DIFF, IHk...
Qed.     


Lemma removeEntry_eq: forall b1 b2 k k0 f1 s1 f2 s2 g,
    ~In (b1, b2) (domain k)  ->
    ~In (b1, b2) (domain k0)  ->
    removeEntry (b1, b2) (k0 ++ (b1, b2, f1, s1) :: g) =
    removeEntry (b1, b2) (k ++ (b1, b2, f2, s2) :: g) ->
    k = k0. 
Proof with eauto.
  intros.
  rewrite removeEntry_app_shift,removeEntry_app_shift in H1.
  simpl in H1; rewrite pairEq_eq_true in H1.
  eapply  app_inv_tail...
  all:eauto.
Qed.

Lemma removeEntry_length_01:  forall b1 b2 g,
    S(List.length (removeEntry (b1, b2) g))=
    List.length g \/
    List.length (removeEntry (b1, b2) g)=
    List.length g.

Proof with eauto.
  intros.
  case_eq (In2 (b1, b2) (domain g)); intros.
  left;
    eapply removeEntry_length_0,in2_implies_in...
  right; eapply removeEntry_length_1,in2_nIn_iff...
Qed.

Hint Resolve removeEntry_length_01.

Lemma removeEntry_app_shift2:
  forall (b1 b2 : name) (k : typeEnv) (g : list (name * name * flag * piType)),
    In (b1, b2) (domain k) -> removeEntry (b1, b2) (k ++ g) = (removeEntry (b1, b2) k) ++ g.
Proof with eauto.
  intros. induction k...
  inversion H.
  unfold domain in H; fold domain in H;  destruct a as [[[a1 a2] f]t]. destruct H as [H |  K].
  inversion H; subst.
  simpl; rewrite pairEq_eq_true...
  intuition auto.
  simpl.
  case_eq (pair_eq (a1, a2) (b1, b2)); intros EQ...
  rewrite H ...
Qed.


Lemma removeEntry_length_02:  forall b1 b2 k g,
    List.length (removeEntry (b1, b2) (k ++ g)) =
    List.length (removeEntry (b1, b2) k) + List.length g \/
    List.length (removeEntry (b1, b2) (k ++ g)) =
    List.length k + 
    List.length (removeEntry (b1, b2) g).
Proof with eauto using in2_implies_in,in2_nIn_iff. intros.
                                                   case_eq (In2 (b1, b2) (domain k)); intros.
                                                   left;
                                                     erewrite removeEntry_app_shift2,app_length...
                                                   erewrite removeEntry_app_shift,app_length...
                                                   eapply in2_nIn_iff...
Qed.              

Hint Resolve removeEntry_length_02.



Lemma removeEntry_iff: forall n g1 g2 (nd_pf1: NoDup (domain g1)) (nd_pf2 : NoDup (domain g2)),
    (forall x : name * name * flag * piType, In x g1 <-> In x g2) ->
    forall x : name * name * flag * piType, In x (removeEntry n g1) <-> In x (removeEntry n g2).
Proof with eauto.
  intros.
  intuition.
  apply in_removeEntry in H0 as K0.
  specialize H with (a0, b2, b1, b0); intuition.
  case_eq (pair_eq (a0, b2) (a, b)). intros ABS.
  rewrite <-pairEq_eq in ABS; inversion ABS; subst.
  assert (~In (a, b, b1, b0) (removeEntry (a, b) g1)).
  eapply no_dup_not_in_removeEntry...
  contradiction.
  intros.  rewrite <-pairEq_neq in H2.
  eapply removeEntry_in...
  apply in_removeEntry in H0 as K0.
  specialize H with (a0, b2, b1, b0); intuition.
  case_eq (pair_eq (a0, b2) (a, b)). intros ABS.
  rewrite <-pairEq_eq in ABS; inversion ABS; subst.
  assert (~In (a, b, b1, b0) (removeEntry (a, b) g2)).
  eapply no_dup_not_in_removeEntry...
  contradiction.
  intros.  rewrite <-pairEq_neq in H1.
  eapply removeEntry_in...
Qed.

Hint Resolve removeEntry_iff.



Lemma removeEntry_iff_cons a1 a2  b1 b2  g1 g2 (nd_pf1: NoDup (domain g1)) (nd_pf2 : NoDup (domain g2)):
  (forall x, In x (domain g1) <-> In x (domain g2)) ->
  (forall x, In x ((a1, a2) :: (b1,b2) :: domain (removeEntry (a1,a2)(removeEntry (b1, b2) g1))) <-> In x ((a1,a2):: (b1,b2):: domain (removeEntry (a1,a2)(removeEntry (b1, b2) g2)))).
Proof with eauto using no_dup_not_in_removeEntry.
  introv IFF; split; introv IN; try inv IN as [EQ | CONT];
    try inv CONT as [EQ2 | CONT2]...
  
  right...
  assert (FIX := CONT2).
  eapply in_domain_in_g in CONT2 as (ff &tt&IN2);
    eapply in_removeEntry,in_removeEntry,in_g_in_domain,IFF in IN2.
  repeat right.
  eapply in_domain_in_g in FIX as (ff1 &tt1 &ABS);
     eapply in_domain_in_g in IN2 as (ff2 &tt2 &IN2).
    eapply in_g_in_domain, removeEntry_in; try intros ABS2; subst.
  assert (~  In (a1, a2,ff1,tt1) (removeEntry (a1, a2) (removeEntry (b1, b2) g1)))...
  eapply no_dup_not_in_removeEntry, no_dup_removeEntry_no_dup...
  eapply removeEntry_in; try intros ABS2; subst...
  eapply in_removeEntry in ABS.
  assert (~ In (b1, b2, ff1, tt1) (removeEntry (b1, b2) g1))...
  right...

  destruct x as [x1 x2];
    eapply in_domain_in_g in CONT2 as (ff &tt &IN2);
    assert (NIN := IN2);
    eapply in_removeEntry,in_removeEntry,in_g_in_domain,IFF in IN2.
  eapply in_domain_in_g in IN2 as (ff1 &tt1 &IN2).
  repeat right.
  eapply in_g_in_domain,removeEntry_in,removeEntry_in;
    try intros ABS; try inv ABS...
   assert (~  In (a1, a2,ff,tt) (removeEntry (a1, a2) (removeEntry (b1, b2) g2)))...
   eapply no_dup_not_in_removeEntry, no_dup_removeEntry_no_dup...
  eapply in_removeEntry in NIN.
  assert (~ In (b1, b2, ff, tt) (removeEntry (b1, b2) g2))...
Qed.

Lemma removeEntry_swap: forall a b g,
    a <> b ->
    removeEntry a (removeEntry b g) =
    removeEntry b (removeEntry a g).
Proof with eauto.
  intros.  induction g. 
  unfold removeEntry; fold removeEntry...
  destruct a0 as [[a0 f] t].
  case_eq (pair_eq b a0). intros PEQ.
  rewrite <-pairEq_eq in PEQ. subst.
  unfold removeEntry.
  assert (K : a0 <> a)...
  apply pairEq_neq in K.
  rewrite K.
  assert (W : pair_eq a0 a0 = true) by apply pairEq_eq_true.
  rewrite W...
  intros PNEQ.
  apply pairEq_neq in PNEQ as K.
  assert (K1 : a0 <> b)...
  apply pairEq_neq in K1...
  case_eq (pair_eq a0 a). intros PEQ.
  unfold removeEntry.
  rewrite K1.
  rewrite PEQ...
  intros PNEQ2.
  assert (K2 : a0 <> b)...
  apply pairEq_neq in K2.
  unfold removeEntry.
  rewrite K1. rewrite PNEQ2. rewrite K2...
  fold removeEntry.
  rewrite IHg...
Qed.



Lemma removeEntry_idempot: forall b1 b2 g,
    ~In (b1, b2) (domain g)  ->
    removeEntry (b1, b2) g =  g.
Proof with eauto.
  intros. induction g...
  unfold domain in H; fold domain in H;  destruct a as [[[a1 a2] f]t]. eapply not_in_cons in H as [H K].
  assert (DIFF:  (a1, a2) <> (b1, b2))... 
  simpl.
  rewrite pairEq_neq in DIFF.
  rewrite DIFF. simpl.
  erewrite IHg...
Qed.


Lemma hid_proj_removeEntry a g (nd_pf : NoDup (domain g)):
  removeEntry a (hid_proj g) = hid_proj (removeEntry a g).
Proof with eauto using no_dup_cont.
  intros.
  induction g...
  destruct a as [b1 b2].
  destruct a0 as [[[a1 a2]f1]t1];
  assert (NIN: ~In (a1, a2) (domain g)).
  simpl in nd_pf; try inversion nd_pf...
  destruct f1; simpl.
  all:case_eq (pair_eq (a1,a2) (b1, b2)); try intros PEQ;
    try rewrite <-pairEq_eq in PEQ; try inv PEQ;
    simpl; try rewrite IHg; simpl in nd_pf...
 all:try rewrite removeEntry_idempot...
Qed.
