Require Import
        Bool List Omega PeanoNat Program.Equality Classical
        ListAddOns Max RemoveEntry Domain
        header
        operations pi_syntax
        pairEq type_system semantics
        proposition27.



Require Import CpdtTactics LibTactics.


Hint Resolve in_eq.

Lemma disjoint_removeEntry_eqd g g1 g2 b1 b2 (nd_pf2 : NoDup (domain g2)):
   domain g1 = domain g2 ->
   disjoint (domain g) (domain (removeEntry (b1, b2) g2)) ->
   ~In (b1, b2) (domain g) ->
   disjoint (domain g) (domain g1).
 Proof with eauto.
  introv EQ DIS NIN.
  gen g1 b1 b2;
    dependent induction g2; destruct g1; intros; simpl; try erewrite <-disjoint_car,disjoint_2_comm;try econstructor; try destruct a as [[[a1 a2] f] t];  try simpl in EQ; inv EQ;
      try destruct p as [[[c1 c2] f2] t2]; try inv H0;
        try eapply disjoint_2_l_cons; split; try intros ABS...
  case_eq (pair_eq (a1, a2)(b1,b2)); introv PEQ;
    assert (PEQ2:=PEQ);
    try rewrite <-pairEq_eq in PEQ; inv PEQ; try contradiction...
      simpl in DIS;
        try rewrite PEQ2 in DIS;
        try eapply disjoint_r_cons in DIS as [DIS NIN2]...
  case_eq (pair_eq (a1, a2)(b1,b2)); introv PEQ;
    assert (PEQ2:=PEQ);
    try rewrite <-pairEq_eq in PEQ; inv PEQ...
      simpl in DIS;
        try rewrite PEQ2 in DIS;
        try eapply disjoint_r_cons in DIS as [DIS NIN2];
        try rewrite H3;
        try eapply disjoint_2_comm,disjoint_car...
     simpl in DIS;
        try rewrite PEQ2 in DIS;
        try eapply disjoint_r_cons in DIS as [DIS NIN2];  simpl in nd_pf2; eapply NoDup_cons_iff in nd_pf2 as [NIN3 nd];
        eapply disjoint_2_comm,disjoint_car,IHg2...
Qed.

 Lemma disjoint_eqd_removeEntry g g1 g2 b1 b2:
   domain g1 = domain g2 ->
   disjoint (domain g) (domain g1) ->
  disjoint (domain g) (domain (removeEntry (b1, b2) g2)).
Proof with eauto.
  introv EQ DIS.
  gen g1 b1 b2;
    dependent induction g2; destruct g1; intros; simpl; try erewrite <-disjoint_car,disjoint_2_comm;try econstructor; try destruct a as [[[a1 a2] f] t];  try simpl in EQ; inv EQ;
      try destruct p as [[[c1 c2] f2] t2]...
  try inverts H0 as EQ...
  assert (DIS2 := DIS);
  simpl in DIS; eapply disjoint_r_cons in DIS as [DIS NIN];
    try eapply IHg2  in DIS...
  case_eq (pair_eq (a1, a2)(b1,b2)); introv PEQ.
  erewrite <-EQ,disjoint_car,disjoint_commute;
    eapply disjoint_r_cons...
  simpl; eapply disjoint_2_l_cons; intuition;
  try eapply disjoint_2_comm,disjoint_car... 
Qed.


Lemma disjoint_cons_removeEntry: forall g m b1 b2,
    NoDup (domain g) ->
    disjoint (domain g) (domain m) ->
    ~In (b1, b2) (domain m) ->
    disjoint ((b1, b2) :: domain (removeEntry (b1, b2) g)) (domain m).
Proof with eauto.
  intros g m b1 b2 ND NIN DIS.
  eapply disjoint_commute,disjoint_cons_r; split...
  dependent induction m;simpl...
  destruct a as [[[a1 a2] f] t];split; intros;simpl in *; try (eapply in_domain_in_g in H as (ff &tt &H);  eapply in_removeEntry in H; eapply disjoint_r_cons in NIN as [_ ABS];eapply in_g_in_domain in H; contradiction).
  eapply disjoint_r_cons in NIN as [NIN _]...
Qed.

  



Hint Resolve pairEq_eq_true.




Lemma sl_bang : forall x1 x2 y1 y2 p s,
    incl ((secLabs (dBang x1 x2 y1 y2 p))) s ->
    incl (secLabs p) s.            
Proof.
  intros. unfold secLabs in H. fold secLabs in H. tauto.
Qed.

Lemma sl_par : forall p q s,
    incl ((secLabs (dPar p q))) s ->
    incl (secLabs p) s /\ incl (secLabs q) s.            
Proof.
  intros. unfold secLabs in H. fold secLabs in H. apply incl_distr in H.
  intuition.
Qed.

Hint Resolve sl_par.




Hint Resolve max_cons.


 Lemma type_of_map : forall g x t1 t2,
    isMap g -> typeOf g x t1 -> typeOf g x t2 ->
    t1 = t2.
Proof.
  intros. unfold isMap in H. inversion H0. inversion H1.
  subst; auto...
  specialize H with x f t1 f0 t2; subst; auto...
  intuition.
Qed.

Lemma flag_of_map : forall g x f1 f2,
    isMap g -> flagOf g x f1 -> flagOf g x f2 ->
    f1 = f2.
Proof.
  intros. unfold isMap in H. inversion H0. inversion H1.
  subst; auto...
  specialize H with x f1 t f2 t0; subst; auto...
  intuition.
Qed.

Hint Resolve type_of_map.
Hint Resolve flag_of_map.

Lemma isMap_cons: forall a g,
    isMap (a :: g) -> isMap g.
Proof.
  intros a g pf.
  assert (TYP := pf).
  unfold isMap in pf.
  unfold isMap; intuition.
  remember (a0, b) as c.
  apply flag_of_map with
      (a::g) c f1 f2  in TYP.
  assumption.
  apply in_cons with (a := a) in H0.
  apply F_Entry in H0; assumption.
  apply in_cons with (a := a) in H1.
  apply F_Entry in H1; assumption.
  remember (a0, b) as c.
  apply type_of_map with
      (a::g) c t1 t2  in TYP.
  assumption.
  apply in_cons with (a := a) in H0.
  apply T_Entry in H0; assumption.
  apply in_cons with (a := a) in H1.
  apply T_Entry in H1; assumption.
Qed.

Hint Resolve isMap_cons.
    
  Lemma in_implies_InB: forall a f t g (pf : isMap g),
      In (a, f, t) g -> InB a g = ((f, t), true).
  Proof with eauto using isMap_cons.
    introv pf IN; induction g;
      try inversion IN; subst...
    simpl; destruct a; try rewrite pairEq_eq_true...
    simpl. destruct a0 as [[b f1] t1].
    case_eq (pair_eq a b); intros.
    rewrite <-pairEq_eq in H0; subst.
    inv IN as [IN2 | CONT]; try inv IN2...
    intuition.
    assert (f1 =f /\ t1 = t).
    eapply pf...
    all:intuition; subst...
  Qed.

Lemma inB_implies_In : forall a g p,
    InB a g = (p, true) ->
    exists (f : flag) (t : piType),
      In (a, f, t) g.
Proof with eauto.
  intros.
  induction g.
  unfold InB in H...
  inversion H...
  unfold InB in H...
  fold InB in H.
  case_eq a0; intros. rewrite H0 in H.
  case_eq p0; intros. rewrite H1 in H.
  case_eq (pair_eq a p2); intros.
  rewrite H2 in H...
  rewrite <-pairEq_eq in H2; subst...
  subst.
  rewrite H2 in *; intuition.
  destruct H0 as [f1 [t IN]]...
  exists f1; exists t...
  intuition.
Qed.

Hint Resolve inB_implies_In.


Lemma new_entries_disjoint : forall g p pf,
    sl_pos p ->
    max (secLabs p) <= max (domain g) ->
    disjoint (domain g)
             (domain
                (newEntries g
                            (secLabs (dep_relabel p (domain g) pf))
                            (max (domain g)))).
Proof with eauto.
  intros.
  specialize identif_seclabs_of_dep_relabel with p (domain g) pf.
  intuition.
  
  rewrite H1.
  clear H1.
  rewrite <- disjoint_car.
  assert (SLPOS := H).
  unfold sl_pos in H; unfold pos in H.
  induction (secLabs p).
  assert (map (fun x : name * name => (fst x, snd x + max (domain g))) nil = nil). intuition.
  rewrite H1. 
  unfold newEntries. apply disjoint_2_comm.  apply dis_nil.
  
  assert (map (fun x : name * name => (fst x, snd x + max (domain g))) (a :: l) = (fst a, snd a + max (domain g)) :: (map (fun x : name * name => (fst x, snd x + max (domain g))) l)). intuition.
  rewrite H1.

  remember (fun x : name * name => (fst x, snd x + max (domain g))) as ff.
  assert (let cont :=
              newEntries
                g
                (map ff l)
                (max (domain g)) in
          domain
            (newEntries
               g
               ((fst a, snd a + max (domain g))
                  :: map ff l)
               (max (domain g))) =
          (fst a, snd a + max (domain g)) :: domain cont).
  unfold domain. fold domain.
  unfold newEntries at 1.
  fold newEntries.
  
  assert (InB (fst a, snd a + max (domain g)) g =
          InB (fst a, snd a + max (domain g)) g) by tauto.
  unfold InB in H2 at 1.
  
  destruct (InB (fst a, snd a + max (domain g)) g).
  case_eq b; intros.
  rewrite H3 in H2. fold InB in H2.
  assert (exists f t,
             In (fst a, snd a + max (domain g), f, t) g)...
  destruct H4 as [f [t ABS]].
  apply in_g_in_domain in ABS.
  apply in_preserves_max in ABS.
  specialize H with (fst a) (snd a); intuition.
  rewrite <-surjective_pairing in H.
  specialize in_eq with (a := a) (l := l); intuition. 
  clear H2. assert (H2 := H3); clear H3.
  assert (snd a + max (domain g) - max (domain g) = snd a) by omega.
  rewrite H3.
  destruct (InB (fst a, snd a) g).
  case_eq b.
  intros.  eauto.
  intros. eauto.
  rewrite H2.
  apply disjoint_2_comm.
  apply disjoint_2_l_cons.
  split.
  clear H2.
  + intro.
    specialize H with (fst a) (snd a).
    rewrite <-surjective_pairing in H.
    assert (In a (a :: l)) by apply in_eq; intuition.
    
    intuition.
    apply in_preserves_max in H2.
    intuition.
  + assert ((forall x1 x2 : name, In (x1, x2) (a :: l) -> x2 > 0) ->  (forall x1 x2 : name, In (x1, x2) l -> x2 > 0)).
    intros.
    specialize H3 with x1 x2.
    intuition.
    intuition.
    apply disjoint_2_comm.
    assert (max l <= max (domain g)).
    specialize max_cons with a l as MC. omega.
    eauto.
Qed.

Hint Resolve in_eq.

Lemma disjoint_2_app_l : forall A (l1 l2 m : list A),
    disjoint_2 (l1 ++ l2) m -> disjoint_2 l1 m.
Proof.
  intros.
  induction l1; econstructor.

  simpl; auto. 
  eapply disjoint_2_cons_l  in H.
  intuition. 
Qed.



Lemma max_removeEntry_cons : forall g a1 a2 f1 t1,
    NoDup (domain g) ->
    In (a1, a2) (domain g) ->
    max (domain g) =
    max (domain ((a1, a2, f1, t1)
                   :: removeEntry (a1, a2) g)).
Proof with eauto.
  intros g a1 a2 f1 t1 ND IN.
  apply Peirce; intros ABS.
  eapply max_diff_domain in ABS as (x &[[ABS1 ABS2]| [ABS1 ABS2]]).
  case_eq (pair_eq x (a1, a2)); intros.
  rewrite <-pairEq_eq in H; inversion H; subst.
  assert (In (a1, a2) (domain ((a1, a2, f1, t1) :: removeEntry (a1, a2) g))); simpl...
  contradiction.
  rewrite <-pairEq_neq in H;
    assert (In x (domain ((a1, a2, f1, t1) :: removeEntry (a1, a2) g))). simpl; right.
  eapply in_domain_in_g in ABS1 as (ff &tt &ABS1).
  eapply in_g_in_domain with (f := ff) (t := tt)...
  eapply removeEntry_in...
  contradiction.
  simpl in ABS1; destruct ABS1 as [ABS0 | ABS1]; subst; try contradiction.
  eapply in_domain_in_g in ABS1 as (ff &tt &ABS1);
    eapply in_removeEntry,in_g_in_domain in ABS1; contradiction.
Qed.


Lemma max_removeEntry_cons_app : forall g a1 a2 f1 t1 b1 b2 f2 t2,
    NoDup (domain g) ->
    In (a1, a2) (domain g) ->
    In (b1, b2) (domain g) ->
    max (domain g) =
    max (domain ((a1, a2, f1, t1)
                   :: (b1, b2, f2, t2)
                   :: removeEntry (a1, a2) (removeEntry (b1, b2) g))).
Proof with eauto.
  intros g a1 a2 f1 t1 b1 b2 f2 t2 ND IN IN1.
  apply Peirce; intros ABS.
  eapply max_diff_domain in ABS as (x &[[ABS1 ABS2]| [ABS1 ABS2]]).
  case_eq (pair_eq x (a1, a2)); intros.
  rewrite <-pairEq_eq in H; inversion H; subst.
  assert (In (a1, a2) ((domain
                          ((a1, a2, f1, t1)
                             :: (b1, b2, f2, t2) :: removeEntry (a1, a2) (removeEntry (b1, b2) g))))); simpl...
  contradiction.
  rewrite <-pairEq_neq in H;
    assert (In x ((domain
                     ((a1, a2, f1, t1)
                        :: (b1, b2, f2, t2) :: removeEntry (a1, a2) (removeEntry (b1, b2) g))))).
  case_eq (pair_eq x (b1, b2)); intros.
  rewrite <-pairEq_eq in H0; inversion H0; subst; simpl; right...
  rewrite <-pairEq_neq in H0;
    simpl; right; right.
  eapply in_domain_in_g in ABS1 as (ff &tt &ABS1).
  eapply in_g_in_domain with (f := ff) (t := tt)...
  eapply removeEntry_in,removeEntry_in...
  contradiction.
  simpl in ABS1. destruct ABS1 as [ABS0 | [ABS1 | ABS11]]; subst; try contradiction.
  eapply in_domain_in_g in ABS11 as (ff &tt &ABS1);
    eapply in_removeEntry,in_removeEntry,in_g_in_domain in ABS1; contradiction.
Qed.


Lemma disjoint_incl {A}: forall (l1 l2 m : list A),
    disjoint l1 l2 ->
    incl m l2 ->
    disjoint l1 m.
Proof with eauto.
  intros.
  dependent induction m; erewrite disjoint_commute.
  simpl...
  eapply disjoint_cons_l.
  split.
  eapply incl_app_inv with (l1 := a::nil) in H0 as [ _ K];
    erewrite disjoint_commute...
  intros ABS.
  assert (In a l2). eapply H0...
  eapply disjoint_absurd...
Qed.



Lemma disjoint_remove {A}:
  forall eqd x (m l : list A),
    disjoint (remove eqd x m) l ->
    ~In x l ->
    disjoint m l.
Proof with eauto.
  introv DIS NIN; induction m, l...
  erewrite <-disjoint_car; eapply disjoint_2_comm,dis_nil...
  apply Peirce. intros ABS.
  eapply not_disjoint in ABS as (z &ABS1 &ABS2).

  case_eq (eqd x z); introv EQ; subst; try contradiction.
  case_eq (eqd x a); introv EQ2; subst...
  econstructor; simpl in DIS;
    try rewrite EQ2 in *; try eapply IHm...
  econstructor; simpl in DIS;
    try rewrite EQ2 in *; inv DIS... 
Qed.

Lemma in_isMap : forall x f t f1 t1 g,
    In (x, f, t) g ->
    In (x, f1, t1) g ->
    isMap g ->
    f = f1 /\ t = t1.
Proof with eauto.
  eauto.
Qed.

Lemma isMap_removeEntry : forall a g,
    isMap g -> isMap (removeEntry a g).
Proof with eauto.
  intros.
  induction g.
  unfold removeEntry...
  destruct a. destruct a0. destruct p. destruct p.
  unfold removeEntry.
  case_eq (pair_eq (n1, n2) (n, n0)). intros BEQ.
  apply isMap_cons with (a := (n1, n2, f, p0))...
  intros BNEQ.
  fold removeEntry.
  unfold isMap in H.
  unfold isMap. 
  intros.

  specialize H with x f1 t1 f2 t2. 
  assert (K1 : In (x, f1, t1) ((n1, n2, f, p0) :: g)).
  destruct H0 as [H1 H2].
  apply in_app_iff with (l := (n1, n2, f, p0):: nil) in H1 as [HEAD | TAIL]. 
  inversion HEAD. inversion H0. subst...
  inversion H0.
  apply in_removeEntry in TAIL as K.
  apply in_cons...
  assert (In (x, f2, t2) ((n1, n2, f, p0) :: g)).
  destruct H0 as [H1 H2].
  apply in_app_iff with (l := (n1, n2, f, p0):: nil) in H2 as [HEAD | TAIL]. 
  inversion HEAD. inversion H0. subst...
  inversion H0.
  apply in_removeEntry in TAIL as K.
  apply in_cons...
  intuition. 
  Qed.
