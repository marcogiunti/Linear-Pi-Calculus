Require Import
  Bool List Lia PeanoNat Program.Equality
  ListAddOns Max Domain RemoveEntry NewEntries Replication
  header
  operations pi_syntax 
  pairEq type_system
  semantics
  tc_dep_relabel_premises
  type_system_rules
  split_not_exists
  tc_prelim
  split_operations_4
  split_existential
  type_operations_1
  no_dup_split_no_dup
  disjoint_newEntries
  lts_payload_un_inp
  tc_premises_5
  split_operations
  split_operations_2
  sub_split
  tc_ill_vis
  tc_premises2
  substitution_prelim
  split_cons_remove.

#[global] Hint Resolve split_comm.

Lemma split_sub: forall g1 g2 g pf1 pf2 pf b1 b2 f tb,
    tEnv_split g1 g2 g pf1 pf2 pf ->
    In (b1, b2, f, tb) g1 ->
    exists f1 tb1 f2 tb2,
      In (b1, b2, f1, tb1) g2 /\ 
        In (b1, b2, f2, tb2) g.
Proof with eauto.
  intros g1 g2 g pf1 pf2 pf b1 b2 f tb TS IN.
  specialize flag_of_split_l with g1 g2 g pf1 pf2 pf (b1, b2) as FYP. eapply FYP in TS as [HID [VIS ILL]]; clear FYP.
  destruct f.
  assert (flagOf g1 (b1, b2) hid)... intuition.
  inversion H1; inversion H2; subst;
    exists ill,t,hid,t0...
  assert (flagOf g1 (b1, b2) ill)... intuition.
  inversion H0; inversion H2; subst;
    exists ill,t,ill,t0...
  inversion H0; inversion H2; subst;
    exists hid,t,hid,t0...
  assert (flagOf g1 (b1, b2) vis)... intuition.
  inversion H1; inversion H2; subst;
    exists vis,t,vis,t0...
Qed.






Lemma proj_newEntries_nil : forall l f g (pf : isMap g),
    pos l ->
    (forall a1 a2, In (a1, a2) l -> exists t, In (a1, a2, hid, t) g) ->
    (f= vis_proj \/ f = ill_proj) ->
    f (newEntries g  (map (fun x : name * name => (fst x, snd x + (max (domain g)))) l) (max (domain g))) = nil.
Proof with eauto.
  intros l f g pf SLP HID [H | H].
  induction l; subst...
  rewrite map_cons;
    destruct a as [a1 a2]; unfold newEntries; fold newEntries; simpl.
  specialize HID with a1 a2 as K. assert (In (a1, a2) ((a1, a2) :: l))... intuition. destruct H0 as (t0 &IN).
  eapply in_implies_InB in IN as INB.
  assert (forall p, ~ InB (a1, a2 + max (domain g)) g = (p, true)).
  intros p1 ABS;  eapply inB_implies_In in ABS as (ff &tt & ABS1); eapply in_g_in_domain,proposition27.in_preserves_max in ABS1.
  assert (a2 = 0) by lia.
  unfold pos in *; specialize SLP with a1 a2; assert (In (a1, a2) ((a1, a2) :: l))... intuition.
  case_eq (InB (a1, a2 + max (domain g)) g). intros.
  case_eq b; intros.
  specialize H0 with p; subst; intuition.
  assert (EQ: a2 + max (domain g) - max (domain g) = a2) by lia.
  subst; rewrite EQ, INB; simpl; rewrite IHl...
  intros. specialize HID with a0 a3.
  assert (In (a0, a3) ((a1, a2) :: l)). right...
  intuition.
  assumption.
  induction l; subst...
  rewrite map_cons;
    destruct a as [a1 a2]; unfold newEntries; fold newEntries; simpl.
  specialize HID with a1 a2 as K. assert (In (a1, a2) ((a1, a2) :: l))... intuition. destruct H0 as (t0 &IN).
  eapply in_implies_InB in IN as INB.
  assert (forall p, ~ InB (a1, a2 + max (domain g)) g = (p, true)).
  intros p1 ABS;  eapply inB_implies_In in ABS as (ff &tt & ABS1); eapply in_g_in_domain,proposition27.in_preserves_max in ABS1.
  assert (a2 = 0) by lia.
  unfold pos in *; specialize SLP with a1 a2; assert (In (a1, a2) ((a1, a2) :: l))... intuition.
  case_eq (InB (a1, a2 + max (domain g)) g). intros.
  case_eq b; intros.
  specialize H0 with p; subst; intuition.
  assert (EQ: a2 + max (domain g) - max (domain g) = a2) by lia.
  subst; rewrite EQ, INB; simpl; rewrite IHl...
  intros. specialize HID with a0 a3.
  assert (In (a0, a3) ((a1, a2) :: l)). right...
  intuition.
  assumption.
Qed.

(*Lemma proj_newEntries_nil : forall x1 x2 t f g pf p (nd_pf1 : NoDup (domain ((x1, x2, vis, t) :: g))) nd_pf,
    sl_pos p ->
    typeCheck ((x1, x2, vis, t) :: g) pf p ->
    (f= vis_proj \/ f = ill_proj) ->
    f (newEntries g  (secLabs (dep_relabel p (domain g) nd_pf)) (max (domain g))) = nil.
Proof with eauto.
  intros x1 x2 t  f g pf p nd_pf1 nd_pf SLP TC H.
  rewrite identif_seclabs_of_dep_relabel.
  case_eq (secLabs p).
  cut TC.
  unfold newEntries.
  revert dependent x1.
  revert dependent x2.
  revert dependent t.
  revert dependent g.
  dependent induction p.
  all:destruct H as [H | H]; subst; simpl; intuition auto;inversion TC; subst.
  eapply H.

  
  [H | H]; subst.
  - rewrite identif_seclabs_of_dep_relabel.
    unfold sl_pos, pos in SLP.
    specialize type_checking_0.typeCheck_hid with (g := (x1, x2, vis, t) :: g) (p:= p) (pf := pf) as K.
    Search newEntries.
    induction (secLabs p); subst...
    rewrite map_cons;
    destruct a as [a1 a2]; unfold newEntries; fold newEntries; simpl.
    case_eq ( InB (a1, a2) g); intros. case_eq b; intros...
    assert (forall p, ~ InB (a1, a2 + max (domain g)) g = (p, true)).
    intros p1 ABS;  eapply inB_implies_In in ABS as (ff &tt & ABS1); eapply in_g_in_domain,proposition27.in_preserves_max in ABS1.
    assert (a2 = 0) by lia.
    specialize SLP with a1 a2; assert (In (a1, a2) ((a1, a2) :: l))... intuition.
    case_eq (InB (a1, a2 + max (domain g)) g). intros.
    case_eq b0; intros.
    specialize H1 with p1; subst; intuition.
    assert (EQ: a2 + max (domain g) - max (domain g) = a2) by lia.
    subst; rewrite EQ, H.
    apply inB_implies_In_2 in H.
    specialize K with (n := (a1, a2)) (pf := pf). assert (In (a1, a2) ((a1, a2) :: l))... intuition. destruct H4 as (t0 &IN). inversion IN. inversion H3.
    (*eapply type_checking_0.typeCheck_hid with (n := (a1, a2))in TC as (t0 &IN). inversion IN. inversion H0.*)
    assert (fst p0 = hid).
    eapply flag_of_map with (g := g)...
    rewrite H4; unfold vis_proj; fold vis_proj;rewrite IHl...
    intros. specialize SLP with x0 x3; intuition.
    intros. 
    A*dmitted.
 *)




#[global] Hint Constructors cons.

Lemma gcons_lin_entry: forall f a1 a2 t pf,  cons ((a1, a2, f, Chan lin empty t) :: nil) pf.
Proof with eauto. 
  intros  f a1 a2 t pf.
  assert (pf' : isMap (removeEntry (a1, a2) ((a1, a2, f, Chan lin empty t) :: nil))).
  eapply isMap_removeEntry...
  eapply Co_lin with (pf' := pf')... 
Qed.

Lemma gcons_un_entry:   forall f a1 a2 p t pf,
    cons ((a1, a2, f, Chan un p t) :: nil) pf.
Proof with eauto. 
  intros  f a1 a2 p t pf.
  assert (pf' : isMap (removeEntry (a1, a2) ((a1, a2, f, Chan un p t) :: nil))).
  eapply isMap_removeEntry...
  eapply Co_un with (pf' := pf')...
Qed.

Lemma gcons_top_entry : forall f a1 a2 pf,
    cons ((a1, a2, f,Top) :: nil) pf.
Proof with eauto. 
  intros  f a1 a2 pf.
  assert (pf' : isMap (removeEntry (a1, a2) ((a1, a2, f, Top) :: nil))).
  eapply isMap_removeEntry...
  eapply Co_top with (pf' := pf')...
Qed. 

Lemma proj_illECast_gcons: forall f (g : typeEnv) (nd_pf : NoDup (domain g)) pf1 pf2,
    (f= vis_proj \/ f = ill_proj) ->
    cons (f g) pf1 ->
    cons (f (illECast g)) pf2.
Proof with eauto.
  intros f g nd_pf pf1 pf2 [H | H] CONS.
  - induction g. simpl...
    revert dependent pf2; destruct a as [[[a1 a2] ff] t]; subst; destruct ff, t; simpl; unfold castF; simpl; try destruct m; simpl;try eapply IHg. eauto. eauto. eauto. eauto. eauto. eauto. 
    + assert (p = empty).
      unfold vis_proj in CONS; fold vis_proj in CONS.
      eapply cons_lin...
      assert (EQ: (a1, a2, vis, Chan lin p t) :: vis_proj (illECast g) = ((a1, a2, vis, Chan lin p t) :: nil) ++ vis_proj (illECast g)). simpl...
      assert (pf: isMap ((a1, a2, vis, Chan lin p t) :: nil)).
      eapply no_dup_isMap; simpl...
      erewrite EQ. intros. erewrite cons_distr with (pf1 := pf).
      assert (EQ2: (a1, a2, vis, Chan lin p t) :: g =
                     ((a1, a2, vis, Chan lin p t) :: nil) ++ g).
      simpl...
      revert dependent pf1; rewrite EQ2,proj_distr. intros.
      eapply cons_distr in CONS; intuition.
      simpl in H0...  
      eapply IHg... eauto.
    + revert dependent pf1. unfold vis_proj; fold vis_proj; intros.
      assert (EQ: (a1, a2, vis, Chan un p t) :: vis_proj (illECast g) = ((a1, a2, vis, Chan un p t) :: nil) ++ vis_proj (illECast g)).
      simpl...
      assert (pf: isMap ((a1, a2, vis, Chan un p t) :: nil)).
      eapply no_dup_isMap; simpl...
      revert dependent pf2. erewrite EQ. intros. erewrite cons_distr with (pf1 := pf).
      assert (EQ2: (a1, a2, vis, Chan un p t) :: vis_proj g =
                     ((a1, a2, vis, Chan un p t) :: nil) ++ vis_proj g). simpl...
      revert dependent pf1. rewrite EQ2. intros.
      eapply cons_distr in CONS; intuition. eauto.
      eapply IHg...
    + revert dependent pf1. unfold vis_proj; fold vis_proj; intros.
      assert (EQ: (a1, a2, vis, Top) :: vis_proj (illECast g) = ((a1, a2, vis, Top) :: nil) ++ vis_proj (illECast g)). simpl...
      assert (pf: isMap ((a1, a2, vis, Top) :: nil)).
      eapply no_dup_isMap; simpl...
      revert dependent pf2. erewrite EQ. intros. erewrite cons_distr with (pf1 := pf).
      assert (EQ2: (a1, a2, vis, Top) :: vis_proj g =
                     ((a1, a2, vis, Top) :: nil) ++ vis_proj g). simpl...
      revert dependent pf1. rewrite EQ2. intros.
      eapply cons_distr in CONS; intuition. eauto.
      eapply IHg...
  -
    induction g. simpl...
    assert (EQ: forall A a (l : list A), a :: l = (a :: nil) ++ l). eauto.
    assert (LEM1:= gcons_lin_entry).
    assert (LEM2:= gcons_un_entry).
    assert (LEM3:= gcons_top_entry).
    assert (LEM4: forall a l pf pf1 pf2,
               cons (a :: l) pf <-> cons (a :: nil) pf1 /\ cons l pf2).
    intros. revert dependent pf; erewrite EQ. intros. eapply cons_distr.
    revert dependent pf2; destruct a as [[[a1 a2] ff] t]; subst; destruct ff, t; simpl; unfold castF; simpl; try destruct m; simpl; intros; try erewrite LEM4; try split; try eapply LEM1,LEM2, LEM3, IHg.
    eauto. eauto. eauto. eauto. eauto. eauto.
    assert (p = empty). eapply cons_lin.  eauto. 
    simpl... subst...
    all: simpl in CONS; try eapply LEM4 in CONS as [K1 K2];try eapply  IHg;
      eauto.
    Unshelve.

    all:simpl in nd_pf;eapply no_dup_cont in nd_pf; try eapply no_dup_isMap.
    all: try (eapply no_dup_vis_proj || eapply no_dup_ill_proj); try erewrite illEC_eq_domain.
    all: simpl; try assumption; try eapply NoDup_cons...
Qed.

