Require Import
        Bool List Lia PeanoNat Program.Equality
        ListAddOns Max RemoveEntry Domain NewEntries
        header
        operations pi_syntax 
        pairEq type_system semantics
        type_operations_1
        split_exists_neutral
        sub_split
        no_dup_split_no_dup
        type_system_rules
        disjoint_newEntries
        proposition27
        split_operations_4.

Require Import CpdtTactics LibTactics.
Import ListNotations.

#[global] Hint Resolve pairEq_eq.
#[global] Hint Resolve pairEq_neq.
#[global] Hint Resolve nonRecTypes.
#[global] Hint Resolve nonRecActions1.
#[global] Hint Resolve nonRecActions2.

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
#[global] Hint Resolve typeOf_removeEntry.
#[global] Hint Resolve split_in_ex.
#[global] Hint Resolve split_in_ex_2.
#[global] Hint Resolve split_exists_neutral.
#[global] Hint Resolve tsub_payload.
#[global] Hint Resolve tsub_io.
#[global] Hint Resolve tsuper_payload.
#[global] Hint Resolve tsuper_top.
#[global] Hint Resolve fsub_hid.
#[global] Hint Resolve fsub_ill.
#[global] Hint Resolve fsub_vis.
#[global] Hint Resolve fsub_hid_r.
#[global] Hint Resolve fsub_ill_r.
#[global] Hint Resolve fsub_vis_r.

#[global] Remove Hints  cons.

#[global] Hint Resolve incl_incl.




#[global] Hint Resolve max_in_domain
     max_not_in_domain
     max_diff_domain
     split_domain_l
     max_same_domain.





Lemma fsuper_flag :
  forall g1 g2 g pf1 pf2 pf a f t f1 t1,
    tEnv_split g1 g2 g pf1 pf2 pf ->
    f <> hid ->
    In (a, f, t) g ->
    In (a, f1, t1) g1 ->
    f = f1.
Proof with eauto.
  intros. destruct a as [a1 a2]. destruct f1. 
  apply fsub_hid with
      (a1 := a1) (a2 := a2) (t := t1) in H.
  inversion H; subst.
  apply flag_of_map with
      (x := (a1, a2)) (f1 := f) (f2 := hid)
    in pf; subst...  
  assumption.
  apply fsub_ill with
      (a1 := a1) (a2 := a2) (t := t1) in H.
  intuition.
  apply flag_of_map with
      (x := (a1, a2)) (f1 := f) (f2 := hid)
    in pf; subst. contradiction.
  all:eauto.
Qed.

#[global] Hint Resolve fsuper_flag.


Lemma type_of_in_action :
  forall g p x1 x2 y1 y2 p' g' pf,
    lts g p (aIn x1 x2 y1 y2) g' p' pf ->
    exists t,
      typeOf g (x1, x2) (Chan lin inp t) \/
      typeOf g (x1, x2) (Chan un inp t) \/
      typeOf g (x1, x2) (Chan un io t).
Proof.
  intros g p x1 x2 y1 y2 p1 g' pf LTS.
  dependent induction LTS.
  - specialize IHLTS with x1 x2 y1 y2; subst; auto.
  - exists t; subst; auto.
    left. apply T_Entry with (f := vis). tauto.
  - exists t; subst; auto.
    right. destruct H as [PINP | PIO].
    subst; auto.
    left. apply T_Entry with (f := vis). tauto.
    subst; auto.
    right. apply T_Entry with (f := vis). tauto.
  - exists t; subst; auto.
    right. destruct H as [PINP | PIO].
    subst; auto.
    left. apply T_Entry with (f := vis). tauto.
    subst; auto.
    right. apply T_Entry with (f := vis). tauto.
  - destruct H as (DIFF1 &_).
    specialize IHLTS with x1 x2 y1 y2; intuition.
    destruct H as (s &IH).
    exists s.
    destruct IH as [IH | [IH |IH]]; inverts IH as IH;
      try rewrite in_app_iff in IH; try destruct IH as [IH | [IH |IH]].
    left; econstructor; try rewrite in_app_iff;
      try left; eauto.
    inv IH; try contradiction.
    left; econstructor; try rewrite in_app_iff;
      try right; right; eauto.
    right; left;  econstructor; try eapply in_app_iff; try left; eauto; eapply removeEntry_in; intuition; eauto.
    inv IH; try contradiction.
    right; left; econstructor;
      try eapply in_app_iff ; repeat right; eauto.
    repeat right; 
      econstructor; try eapply in_app_iff;
        try left; eauto.
    inv IH; try contradiction.
    right; right; econstructor;
      try eapply in_app_iff;
      repeat right; eauto.
Qed.



Lemma type_of_out_action :
  forall g p x1 x2 y1 y2 p' g' pf,
    lts g p (aOut x1 x2 y1 y2) g' p' pf ->
    exists t,
      typeOf g (x1, x2) (Chan lin out t) \/
      typeOf g (x1, x2) (Chan un out t) \/
      typeOf g (x1, x2) (Chan un io t).
Proof with eauto.
  intros g p x1 x2 y1 y2 p1 g' pf LTS.
  dependent induction LTS.
  - specialize IHLTS with x1 x2 y1 y2; subst; auto...
  - exists t; subst.
    left. apply T_Entry with (f := vis). tauto.
  - exists t; subst.
    right. destruct H as [POUT | PIO].
    subst. left...
    subst. right...
  - specialize IHLTS with x1 x2 y1 y2; intuition.
    destruct H0 as [t1 P].
    assert ((x1, x2) <> (y1, y2))...
    destruct P as [P1 | P2].
    inversion P1; subst.
    apply in_inv in H1.
    destruct H1. inversion H1; subst...

    exists t1.
    left...
    destruct P2.
    exists t1; right; left.
    inversion H1; subst.
    apply in_inv in H2.
    destruct H2. inversion H2; subst; eauto.
    specialize no_dup_not_in_removeEntry with (g := (removeEntry (y1, y2) g)) (a := (x1, x2)) (f := f) (t := Chan un out t1) as pf2.
    specialize no_dup_removeEntry_no_dup with  g (y1, y2) as pf3; intuition.
    eauto.

    exists t1.
    right. right.
    inversion H1; subst.
    apply in_inv in H2.
    destruct H2. inversion H2; subst; eauto.
    
    specialize no_dup_not_in_removeEntry with (g := (removeEntry (y1, y2) g)) (a := (x1, x2)) (f := f) (t := Chan un io t1) as pf2.
    specialize no_dup_removeEntry_no_dup with  g (y1, y2) as pf3; intuition.
    eauto.
  - destruct H as (DIFF1 &_).
    specialize IHLTS with x1 x2 y1 y2; intuition.
    destruct H as (s &IH).
    exists s.
    destruct IH as [IH | [IH |IH]]; inverts IH as IH;
      try rewrite in_app_iff in IH; try destruct IH as [IH | [IH |IH]]; eauto.
    left; econstructor; try rewrite in_app_iff;
      try left; eauto.
    inv IH; try contradiction.
    left; econstructor; try rewrite in_app_iff;
      try right; right; eauto.
    right; left;  econstructor; try eapply in_app_iff; try left; eauto; eapply removeEntry_in; intuition; eauto.
    inv IH; try contradiction.
    right; left; econstructor;
      try eapply in_app_iff ; repeat right; eauto.
    repeat right; 
      econstructor; try eapply in_app_iff;
        try left; eauto.
    inv IH; try contradiction.
    right; right; econstructor;
      try eapply in_app_iff;
      repeat right; eauto.
Qed.


#[global] Hint Resolve pol_cup_id.

Lemma split_exists_remove_l :
  forall g1 g2 g pf1 pf2 pf a1 a2 f t t1 t2,
    In (a1, a2, f, t1) g1 ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    type_remove t1 t t2 ->
    exists t1' t2',
      typeOf g (a1, a2) t1' /\
      type_remove t1' t t2'.
Proof.
  intros g1 g2 g pf1 pf2 pf a1 a2 f t t1 t2 IN TSPLIT TREM.
  generalize dependent a1.
  generalize dependent a2.
  generalize dependent f. 
  generalize dependent t.
  generalize dependent t1.
  generalize dependent t2.
  dependent induction TSPLIT.
  - intros; subst; inversion IN.
  - intros; subst.
    case_eq (pair_eq n (a1, a2)).
    + intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
      exists (Chan lin p' t).
      assert (Ta := pf1).
      apply T_Entry in H1.
      apply type_of_map with
          g1 (a1, a2) (Chan lin p t) t1
        in Ta; subst.
      specialize type_remove_lin with
          t t0 t2 as TREM2.
      destruct p.
      * intuition; subst; auto.
        exists (Chan lin p' t). intuition.
        unfold type_remove.
        split. apply Ts_empty.
        split. apply Tp_LinPlus. apply Pp_emptyL.
        unfold is_unrestricted; auto.
      * intuition; subst; auto.
        exists (Chan lin q t). intuition. 
        unfold type_remove.
        split. inversion H0; subst. apply Ts_id. apply Ts_inp.
        split. apply Tp_LinPlus. assumption.
        unfold is_unrestricted; auto.
        intuition.
        destruct H7 as [pp [tt ABS]]. inversion ABS.
        exists (Chan lin p' t). intuition.
        unfold type_remove.
        split. apply Ts_empty.
        split. apply Tp_LinPlus. apply Pp_emptyL.
        unfold is_unrestricted; auto.
      * intuition; subst; auto.
        exists (Chan lin q t). intuition. 
        unfold type_remove.
        split. inversion H0; subst. apply Ts_id. apply Ts_out.
        split. apply Tp_LinPlus. assumption.
        unfold is_unrestricted; auto.
        intuition.
        destruct H6 as [pp [tt ABS]]. inversion ABS.
        exists (Chan lin p' t). intuition.
        unfold type_remove.
        split. apply Ts_empty.
        split. apply Tp_LinPlus. apply Pp_emptyL.
        unfold is_unrestricted; auto.
      * intuition; subst; auto.
        exists (Chan lin empty t). intuition.
        unfold type_remove.
        split. inversion H0; subst. apply Ts_id. 
        split. apply Tp_LinPlus. inversion H0; subst.
        apply Pp_emptyR.
        unfold is_unrestricted; auto.
        intuition.
        destruct H3 as [pp [tt ABS]]. inversion ABS.
        inversion H0; subst.  
        exists (Chan lin out t). intuition.
        inversion H0; subst.
        exists (Chan lin inp t). intuition.
        inversion H0; subst.
        exists (Chan lin io t). intuition.
      * assumption.
      * apply T_Entry in IN; assumption.
    + intros PNEQ. rewrite <-pairEq_neq in PNEQ.
      assert (PNEQ2 :  (a1, a2) <> n); auto.
      apply removeEntry_in
        with (a1, a2) f0 t1 n g1
        in PNEQ2.
      apply IHTSPLIT with t2 t1 t0 f0 a2 a1 in TREM.
      destruct TREM as [t1' [t2' [TOF TREM]]].
      inversion TOF; subst.
      apply in_removeEntry in H3.
      exists t1'.
      exists t2'.
      apply T_Entry in H3; intuition.
      all:assumption.
  - intros; subst.
    case_eq (pair_eq n (a1, a2)).
    + intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
      exists (Chan un p t). exists (Chan un p t). intuition.
      assert (Ta := pf1).
      apply type_of_map with g1 (a1, a2) t1 ( Chan un p t)
        in Ta; subst.
      inversion TREM; subst; auto.
      inversion H2; subst; auto.
      specialize type_remove_un_2 with t (Chan un p t) (Chan un p t) as TREM2.
      destruct p; intuition. 
      specialize type_remove_un_2 with t (Chan un empty t) (Chan un p t) as TREM2.
      destruct p; intuition.
      specialize type_remove_un_2 with t (Chan un inp t) (Chan un io t) as TREM2.
      intuition.
      specialize type_remove_un_2 with t (Chan un out t) (Chan un io t) as TREM2.
      intuition.
      apply T_Entry in IN; assumption.
      apply T_Entry in H0; assumption.
    +  intros PNEQ. rewrite <-pairEq_neq in PNEQ.
       assert (PNEQ2 :  (a1, a2) <> n); auto.
       apply removeEntry_in
         with (a1, a2) f0 t1 n g1
         in PNEQ2.
       apply IHTSPLIT with t2 t1 t0 f0 a2 a1 in TREM.
       destruct TREM as [t1' [t2' [TOF TREM]]].
       inversion TOF; subst.
       apply in_removeEntry in H2.
       exists t1'.
       exists t2'.
       split. 
       apply T_Entry in H2; assumption.
       all:assumption.
  -    intros; subst.
       case_eq (pair_eq n (a1, a2)).
       + intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
         exists Top. exists Top. intuition.
         assert (Ta := pf1).
         apply type_of_map with g1 (a1, a2) t1 Top
           in Ta; subst.
         inversion TREM; subst; auto.
         inversion H2; subst; auto.
         specialize type_remove_top_2 with Top Top as TREM2.
         intuition. 
         apply T_Entry in IN; assumption.
         apply T_Entry in H0; assumption.
       +  intros PNEQ. rewrite <-pairEq_neq in PNEQ.
          assert (PNEQ2 :  (a1, a2) <> n); auto.
          apply removeEntry_in
            with (a1, a2) f0 t1 n g1
            in PNEQ2.
          apply IHTSPLIT with t2 t1 t f0 a2 a1 in TREM.
          destruct TREM as [t1' [t2' [TOF TREM]]].
          inversion TOF; subst.
          apply in_removeEntry in H2.
          exists t1'.
          exists t2'.
          split. 
          apply T_Entry in H2; assumption.
          all:assumption.
Qed.


#[global] Hint Resolve type_of_in_action.
#[global] Hint Resolve type_of_out_action.
#[global] Hint Resolve split_exists_remove_l.



Lemma split_max :
  forall g1 g2 g pf1 pf2 pf ,
    tEnv_split g1 g2 g pf1 pf2 pf ->
    max (domain g1) = max (domain g).
Proof with eauto.
  intros g1 g2 g pf1 pf2 pf TS.
  specialize
    split_domain_l_2 with
      (g1 := g1) (g2 := g2) (g := g)
      (pf1 := pf1) (pf2 := pf2) (pf := pf) as H.
  intuition.
Qed.

#[global] Hint Resolve split_max.

Lemma max_dep_relabel:
  forall g1 g p nd_pf nd_pf1,
    max (domain g) = max (domain g1)  ->
    dep_relabel p (domain g) nd_pf =
    dep_relabel p (domain g1) nd_pf1.
Proof with eauto.
  intros.
  dependent induction p.
  - unfold dep_relabel; fold dep_relabel. tauto.
  - specialize IHp with nd_pf nd_pf1.
    intuition.
    unfold dep_relabel. fold dep_relabel.
    rewrite H0...
  - specialize IHp1 with nd_pf nd_pf1.
    specialize IHp2 with nd_pf nd_pf1.
    unfold dep_relabel; fold dep_relabel.
    intuition. rewrite H0; rewrite H1...
  - specialize IHp with nd_pf nd_pf1.
    unfold dep_relabel; fold dep_relabel.
    intuition. rewrite H...
    rewrite H0...
  - specialize IHp with nd_pf nd_pf1.
    unfold dep_relabel; fold dep_relabel.
    intuition. rewrite H0...
  - specialize IHp with nd_pf nd_pf1.
    unfold dep_relabel; fold dep_relabel.
    intuition. rewrite H0...
Qed.

#[global] Hint Resolve max_dep_relabel.

Lemma split_dep_relabel:
  forall g1 g2 g pf1 pf2 pf p nd_pf nd_pf1,
    tEnv_split g1 g2 g pf1 pf2 pf ->
    dep_relabel p (domain g) nd_pf =
    dep_relabel p (domain g1) nd_pf1.
Proof with eauto.
  intros g1 g2 g pf1 pf2 pf p nd_pf nd_pf1 TS.
  dependent induction p.
  - unfold dep_relabel; fold dep_relabel...
  - specialize IHp with nd_pf nd_pf1.
    unfold dep_relabel; fold dep_relabel.
    intuition. rewrite H...
  - specialize IHp1 with nd_pf nd_pf1.
    specialize IHp2 with nd_pf nd_pf1.
    unfold dep_relabel; fold dep_relabel.
    intuition. rewrite H; rewrite H0...
  - specialize IHp with nd_pf nd_pf1.
    unfold dep_relabel; fold dep_relabel.
    intuition. rewrite H...
    apply split_max in TS as MAXEQ.
    rewrite MAXEQ...
  - specialize IHp with nd_pf nd_pf1.
    unfold dep_relabel; fold dep_relabel.
    intuition. rewrite H...
  - specialize IHp with nd_pf nd_pf1.
    unfold dep_relabel; fold dep_relabel.
    intuition. rewrite H...
Qed.

#[global] Hint Resolve split_dep_relabel.

Lemma no_dup_in_flag : forall a1 a2 b1 b2 t f s t1 g0,
    NoDup (domain ((a1, a2, vis, t) :: (b1, b2, f, s) :: g0))
    ->
    In (b1, b2, vis, t1) ((b1, b2, f, s) :: g0) ->
    f = vis.
Proof with eauto.
  intros a1 a2 b1 b2 t f s t1 g0 nd_pf IN.
  apply no_dup_domain_cons in nd_pf.
  unfold domain in nd_pf; fold domain in nd_pf.
  apply NoDup_cons_iff in nd_pf.
  inversion IN. inversion H; subst...
  apply in_g_in_domain in H.
  intuition.
Qed.

#[global] Hint Resolve no_dup_in_flag.


Lemma lts_rewrite_pf : forall g a p g1 p1 pf (pf1 : NoDup (domain g)),
    lts g p a g1 p1 pf ->
    lts g p a g1 p1 pf1.
Proof with eauto.
  intros.
  dependent induction H.
  all:try econstructor...
  assert (DEPEQ : dep_relabel p (domain g) pf = dep_relabel p (domain g) pf1) by apply dep_relabel_rewrite_pf.
  subst q; rewrite DEPEQ.
  apply uRin with (f := f) (t1 := t1) (pol := pol) (t := t)...
Qed.

#[global] Hint Resolve lts_rewrite_pf.


#[global] Hint Resolve in_eq.
#[global] Hint Resolve in_isMap.


#[global] Hint Resolve in_second.



#[global] Hint Resolve removeEntry_twice.

(*Lemma lts_out_vis_vis : forall a1 a2 b1 b2 t t' t1 s' f p p' g0 pf,  
   lts ((a1, a2, vis, t) :: (b1, b2, vis, t1) :: g0) p 
       (aOut a1 a2 b1 b2) ((a1, a2, vis, t') :: (b1, b2, f, s') :: g0) p' pf ->
   f = vis.
Proof with eauto using flagOf_turnHid.
  intros.
  dependent induction H.
  - specialize IHlts with a1 a2 b1 b2 t t' t1 s' f g0 pf.
  intuition.
  - tauto.
  - specialize pairEq_eq with (a1, a2) (a1, a2) as BEQ; intuition.
    rewrite H in x. inversion x...
    rewrite H in x. inversion x...
  - clear IHlts.
    specialize in_isMap with (b1, b2) hid t0 vis t1 ((a1, a2, vis, t) :: (b1, b2, vis, t1) :: g0) as IN.
    assert ( In (b1, b2, vis, t1) ((a1, a2, vis, t) :: (b1, b2, vis, t1) :: g0)). apply in_second...
    apply no_dup_isMap in pf.
    intuition.
    discriminate.
  - 
    simpl in H1; destruct H1 as (DIFF1 &DIFF2).
    assert (FYP: flagOf g1 (b1, b2) vis).
    rewrite <-flagOf_turnHid,<-H0...
    
    
Qed.

Hint Resolve lts_out_vis_vis.
 *)

Lemma hide_in a1 a2 c1 c2 f t f1 t1 f2 t2 (l1 l2 : typeEnv):
      (a1,a2) <> (c1, c2) ->
      In (a1, a2, f, t) (l1 ++ (c1, c2, f1, t1) :: l2) ->
      In (a1, a2, f, t) (l1 ++ (c1, c2, f2, t2) :: l2).
Proof with eauto.
  introv DIFF IN; eapply in_app_iff in IN as [IN |CONT];
    eapply in_app_iff;
    try inversion CONT as [ABS | CONT2];
    try inv ABS; try contradiction...
  try repeat right...
Qed.

Lemma hide_remove_object b1 b2 c1 c2 l1 l2 f t f1 t1:
  NoDup (domain (l1 ++ (c1, c2, f1, t1) :: l2)) ->
  (b1, b2) <> (c1, c2) ->
  In (b1, b2, f, t) (l1 ++ (c1, c2, f1, t1) :: l2) ->
  (In (b1, b2, f, t) l1 /\
   forall f2 t2,
     removeEntry (b1, b2)(l1 ++ (c1, c2, f2, t2) :: l2) =  removeEntry (b1, b2) l1 ++ (c1, c2, f2, t2) :: l2) \/
  In (b1, b2, f, t) l2 /\
  forall f2 t2,
    removeEntry (b1, b2)(l1 ++ (c1, c2, f2, t2) :: l2) =  l1 ++ (c1, c2, f2, t2) :: removeEntry (b1, b2) l2.
Proof with eauto.
  introv ND DIFF IN;
    eapply in_app_iff in IN as [IN |CONT]...
    left; intuition;
    try eapply removeEntry_app_shift2,in_g_in_domain...
    try inversion CONT as [ABS | CONT2];
    try inv ABS; try contradiction...
    right; intuition.
    erewrite domain_distr in ND; simpl in ND;
      eapply no_dup_iff in ND as (ND1 &ND2 &DIS).
    erewrite removeEntry_app_shift; try intros ABS...
    assert (DIFF2: (c1, c2) <> (b1, b2))...
    simpl; rewrite pairEq_neq in DIFF2; try rewrite DIFF2...
    eapply in_g_in_domain in CONT2;
      try eapply disjoint_absurd...
    try right...
Qed.

Lemma removeEntry_double g a1 a2 (nd_pf: NoDup (domain g)):
  removeEntry (a1, a2) (removeEntry (a1, a2) g) =
    removeEntry (a1, a2) g.
Proof with eauto.
  introv; induction g; simpl...
  destruct a as [[[b1 b2] ff]tt].
  assert (ND:=nd_pf); simpl in nd_pf; eapply no_dup_cont,IHg in nd_pf as IH;
    clear IHg.
  case_eq (pair_eq (b1,b2) (a1,a2)); introv PEQ;
    try rewrite PEQ;
    try rewrite <-pairEq_eq in PEQ; inv PEQ.
  eapply removeEntry_idempot; try intros ABS...
  simpl in ND; inversion ND...
  simpl; rewrite H0; erewrite IH...
Qed.
  
Lemma hide_remove_subject_object a1 a2 b1 b2 c1 c2 l1 l2 f0 t0 f t f1 t1:
  NoDup (domain (l1 ++ (c1, c2, f1, t1) :: l2)) ->
  (b1, b2) <> (c1, c2) ->
  (a1, a2) <> (c1, c2) ->
   In (a1, a2, f0, t0) (l1 ++ (c1, c2, f1, t1) :: l2) ->
  In (b1, b2, f, t) (l1 ++ (c1, c2, f1, t1) :: l2) ->
  ( In (a1, a2, f0, t0) l1 /\ In (b1, b2, f, t) l1 /\
   forall f2 t2,
     removeEntry (a1,a2) (removeEntry (b1, b2)(l1 ++ (c1, c2, f2, t2) :: l2)) =  removeEntry (a1,a2)(removeEntry (b1, b2) l1) ++ (c1, c2, f2, t2) :: l2) \/
  (In (a1, a2, f0, t0) l1 /\ In (b1, b2, f, t) l2 /\
  forall f2 t2,
    removeEntry (a1,a2) (removeEntry (b1, b2)(l1 ++ (c1, c2, f2, t2) :: l2)) =  removeEntry (a1,a2) l1 ++ (c1, c2, f2, t2) :: removeEntry (b1, b2) l2)
  \/
  (In (a1, a2, f0, t0) l2 /\ In (b1, b2, f, t) l1 /\
  forall f2 t2,
    removeEntry (a1,a2) (removeEntry (b1, b2)(l1 ++ (c1, c2, f2, t2) :: l2)) =  removeEntry (b1,b2) l1 ++ (c1, c2, f2, t2) :: removeEntry (a1, a2) l2)
  \/
  (In (a1, a2, f0, t0) l2 /\ In (b1, b2, f, t) l2 /\
  forall f2 t2,
    removeEntry (a1,a2) (removeEntry (b1, b2)(l1 ++ (c1, c2, f2, t2) :: l2)) =   l1 ++ (c1, c2, f2, t2) :: removeEntry (a1, a2) (removeEntry (b1,b2) l2)).
Proof with eauto.
  introv ND DIFF1 DIFF2 IN1 IN2.
  assert (ND' := ND);
    try erewrite domain_distr in ND'; simpl in ND';
    eapply no_dup_iff in ND' as (ND1 &ND2 &DIS).
  assert (DIFFca: (c1, c2) <> (a1, a2))...
  assert (DIFFcb: (c1, c2) <> (b1, b2))...
  rewrite pairEq_neq in DIFFca,DIFFcb.

   eapply in_app_iff in IN1 as [IN1 |CONT1];
    eapply in_app_iff in IN2 as [IN2 |CONT2]...
  
  left; intuition.
  case_eq (pair_eq (a1, a2) (b1, b2));
    introv PEQ; try rewrite <-pairEq_eq in PEQ; inv PEQ.
  repeat erewrite removeEntry_double;
    repeat erewrite removeEntry_app_shift2;
    try eapply in_g_in_domain...
  erewrite domain_distr in *; simpl in *...
  erewrite <-pairEq_neq in *;
    repeat erewrite removeEntry_app_shift2;
    try eapply in_g_in_domain,removeEntry_in;
    try eapply in_g_in_domain...

  try inv CONT2 as [ABS | CONT3];
    try inv ABS; try contradiction...

  right; left; intuition.
  case_eq (pair_eq (a1, a2) (b1, b2));
    introv PEQ; try rewrite <-pairEq_eq in PEQ; inv PEQ.
  eapply disjoint_absurd with (l :=  domain l1) (m := (c1,c2) :: domain l2); try eapply in_g_in_domain; try right;
    try eapply in_g_in_domain...
  rewrite <-pairEq_neq in H0.
  erewrite removeEntry_app_shift;
    try erewrite removeEntry_app_shift2;simpl;
    try eapply in_g_in_domain,removeEntry_in;
    try eapply in_g_in_domain;
    try rewrite DIFFcb;
    try intros ABS...
  eapply in_g_in_domain in CONT3;
    try eapply disjoint_absurd...
  try right...

  try inv CONT1 as [ABS | CONT'];
    try inv ABS; try contradiction...

  right; right; left; intuition.
  case_eq (pair_eq (a1, a2) (b1, b2));
    introv PEQ; try rewrite <-pairEq_eq in PEQ; inv PEQ.
  eapply disjoint_absurd with (l :=  domain l1) (m := (c1,c2) :: domain l2); try eapply in_g_in_domain; try right;
    try eapply in_g_in_domain...
  rewrite <-pairEq_neq in H0.
   erewrite removeEntry_app_shift2;
    try erewrite removeEntry_app_shift;simpl;
    try eapply in_g_in_domain,removeEntry_in;
    try eapply in_g_in_domain;
    try rewrite DIFFca;
    try intros ABS...
   eapply in_g_in_domain in CONT';
     try eapply in_domain_in_g in ABS as (ff &tt &ABS);
     try eapply in_removeEntry,in_g_in_domain in ABS;
   try eapply disjoint_commute in DIS;
    eapply disjoint_absurd with (x := (a1, a2))... 
  try right...

  try inv CONT1 as [ABS | CONT'];
    try inv CONT2 as [ABS2 | CONT''];
    try inv ABS;
    try inv ABS2;
    try contradiction...

  repeat right; intuition.
   case_eq (pair_eq (a1, a2) (b1, b2));
    introv PEQ; try rewrite <-pairEq_eq in PEQ; inv PEQ.
   
   eapply no_dup_cont in ND2 as ND'';
     repeat erewrite removeEntry_double...
   
   repeat erewrite removeEntry_app_shift;
     simpl; try rewrite DIFFcb;
     try eapply in_g_in_domain;
     try intros ABS; try eapply in_g_in_domain in CONT'...
   eapply disjoint_absurd with (x := (b1, b2))...
   repeat right...
  erewrite domain_distr in *; simpl in *...
  erewrite <-pairEq_neq in H0;
    erewrite removeEntry_app_shift; simpl;
     try rewrite DIFFcb;
     try eapply in_g_in_domain;
    try intros ABS; try eapply in_g_in_domain in CONT''...
   erewrite removeEntry_app_shift; simpl;
     try rewrite DIFFca;
     try eapply in_g_in_domain;
     try intros ABS; try eapply in_g_in_domain in CONT''...
   eapply disjoint_absurd with (x := (a1, a2))...
   right; eapply in_g_in_domain...
      eapply disjoint_absurd with (x := (b1, b2))...
      right...
Qed.

(*Lemma hide_flagOf c1 c2 t1 t2 h1 h2 l1 l2 sl1 sl2:
  NoDup (domain (h1 ++ (c1, c2, hid, t1) :: h2)) ->
  NoDup (domain ((l1 ++ (c1, c2, hid, t2) :: l2))) ->
  (forall (x : name * name) (f1 f2 : flag),
         flagOf (h1 ++ (c1, c2, hid, t1) :: h2) x f2 ->
         flagOf (l1 ++ (c1, c2, hid, t2) :: l2) x f1 ->
         f2 <> f1 -> f2 = hid /\ f1 = ill /\ ~ In x sl1) ->
       incl sl2 sl1 ->
  (forall (x : name * name) (f1 f2 : flag),
      flagOf (h1 ++ (c1, c2, vis, t1) :: h2) x f2 ->
      flagOf (l1 ++ (c1, c2, vis, t2) :: l2) x f1 ->
      f2 <> f1 -> f2 = hid /\ f1 = ill /\ ~ In x sl2).
Proof with eauto.
  introv pf pf0 FIFF INCL.
  intros x1 ff1 ff2 FYP2 FYP1 FDIFF;
      specialize FIFF with x1 ff1 ff2;
      simpl in FIFF.
    try inverts FYP2 as IN;
      eapply in_app_iff in IN as [IN2 | IN2].
    try inverts FYP1 as IN;
      eapply in_app_iff in IN as [IN1 | IN1].
    assert (IH2: ff2 = hid /\ ff1 = ill /\ ~ In x1 (sl1)).
    eapply FIFF; try econstructor; try eapply in_app_iff...
    intuition.

    inv IN1 as [EQ | INV1]; try inv EQ.
    assert (False).
    eapply in_g_in_domain in IN2;
      erewrite domain_distr in pf; simpl in pf;
        eapply NoDup_remove_2,not_in_app_and in pf;
        intuition.
    contradiction.

    assert (IH2: ff2 = hid /\ ff1 = ill /\ ~ In x1 sl1).
    eapply FIFF; try econstructor; try eapply in_app_iff... repeat right...
    intuition.

    inv IN2 as [EQ | INV2]; try inv EQ;
      try inverts FYP1 as IN1;
      try eapply in_app_iff in IN1 as [IN1 | IN1].
    assert (False).
    eapply in_g_in_domain in IN1;
      erewrite domain_distr in pf0; simpl in pf0;
        eapply NoDup_remove_2,not_in_app_and in pf0;
        intuition.
    contradiction.

    inv IN1 as [ABS | IN'];
      try inv ABS; try contradiction.
    assert (False).
    eapply in_g_in_domain in IN';
      erewrite domain_distr in pf0; simpl in pf0;
        eapply NoDup_remove_2,not_in_app_and in pf0;
        intuition.
    contradiction.

    assert (IH2: ff2 = hid /\ ff1 = ill /\ ~ In x1 sl1).
    eapply FIFF; try econstructor; try eapply in_app_iff... repeat right...
    intuition.

    inv IN1 as [EQ | IN']; try inv EQ.
    assert (False).
    eapply in_g_in_domain in INV2;
      erewrite domain_distr in pf; simpl in pf;
        eapply NoDup_remove_2,not_in_app_and in pf;
        intuition.
    contradiction.

    assert (IH2: ff2 = hid /\ ff1 = ill /\ ~ In x1 sl1).
    eapply FIFF; try econstructor; try eapply in_app_iff; repeat right...
    intuition.
Qed.
*)

Lemma lts_type_plus_un_in : forall a1 a2 pol t b1 b2 f f1 s s1 s0 s01 q1 q2 g pf g1 pf1 k,
    lts g q1 
        (aIn a1 a2 b1 b2)
        (k ++ (b1, b2, vis, s) :: removeEntry (b1, b2) g) q2 pf ->
    In (a1, a2, vis, Chan un pol t) g ->
    In (b1, b2, f, s1) g ->
    type_plus s01 t s0 ->
    f1 <> hid ->
    In (a1, a2, vis, Chan un pol t) g1 ->
    In (b1, b2, f1, s01) g1 ->
    (forall x,
        In x (domain g) <-> In x (domain g1)) ->
    NoDup (secLabs q1) ->
    incl (secLabs q1) (domain (hid_proj g1)) ->
   (* (forall x f1 f2,
        flagOf g x f2 ->
        flagOf g1 x f1 ->
        f2 <> f1 ->
        f2 = hid /\ f1 = ill /\
        ~In x (secLabs q2)) ->*)
    disjoint (domain k) (domain g) ->
    exists k1,
      lts
        g1 q1
        (aIn a1 a2 b1 b2)
        (k1 ++ (b1, b2, vis, s0) :: removeEntry (b1, b2) g1) q2 pf1.
Proof with eauto using hide_in.
  introv
    LTS INa INb  TP NHID IN1a IN1b
    IFF NDSL INCL. introv  (*FIFF*) DIS.
  assert (DIFF: (a1, a2) <> (b1, b2))...
  assert (IH :  aIn a1 a2 b1 b2 = aIn a1 a2 b1 b2)...
  gen g1.
  dependent induction LTS; try intros...
  - try eapply IHLTS in IH as (k1 &IH)...
    exists k1.
    apply parL...
    simpl in NDSL;
      try eapply no_dup_distr in NDSL;
      intuition.
    simpl in INCL;
      eapply incl_app_inv in INCL;
      intuition.
    (*intros; specialize FIFF with x f0 f2;
      simpl in FIFF; intuition.*)
  -  assert (vis = vis /\ Chan lin inp t0 = Chan un pol t).
     apply in_isMap with (x := (a1, a2)) (g := g)...
     intuition. inversion H5.
  - assert (EQ: vis = vis /\ Chan un pol0 t0 = Chan un pol t).
    apply in_isMap with (x := (a1, a2)) (g := g)...
    destruct EQ as (_&EQ); try inv EQ.
    exists (nil:typeEnv);erewrite app_nil_l;
      eapply uIn...
  -  assert (EQ: vis = vis /\ Chan un pol0 t0 = Chan un pol t).
     apply in_isMap with (x := (a1, a2)) (g := g)...
     destruct EQ as (_&EQ); try inv EQ.

     exists (newEntries g1 (secLabs (dep_relabel p (domain g1) pf1)) (max (domain g1))).
     subst q.
     assert (EQ: dBang a1 a2 x1 x2 (dep_relabel p (domain g) pf)
                 =
                 dBang a1 a2 x1 x2 (dep_relabel p (domain g1) pf1)).
     erewrite max_dep_relabel...
     erewrite EQ; try eapply uRin...
  - Case hide.
    remember b0 as c1. remember b3 as c2. subst b0 b3.
    assert (NH := H); destruct H as (DIFF1 &DIFF2).
    

    assert (IN1: In (c1, c2) (domain g1)).
    eapply IFF; rewrite domain_distr,in_app_iff; simpl...
    eapply in_domain_in_g in IN1 as (ff &t1 &IN1);
      eapply in_split in IN1 as (l1 &l2  &EQ); subst g1.

    assert (ff = hid).
    assert (FYP: flagOf
              (l1 ++ (c1, c2, ff, t1) :: l2)
               (c1, c2)  hid).
    eapply hid_proj_flagOf;
      simpl in INCL;
      eapply incl_app_inv in INCL;
      intuition...
    repeat rewrite domain_distr in pf0;
      simpl in pf0;
      try eapply NoDup_remove_2,ListAddOns.not_in_app_and in pf0.
    inverts FYP as IN;
      try eapply in_app_iff in IN as [ABS |IN2]; try eapply in_g_in_domain in ABS;
      try inverts IN2 as EQ; try inv EQ; 
      try eapply in_g_in_domain in EQ;
      intuition.

    (*destruct ff; try tauto.
    eapply FIFF in F1; simpl in *; intuition.
    econstructor; try eapply in_app_iff; try right; left...
    discriminate.
    eapply FIFF in F1; simpl in *; intuition.
    econstructor; try eapply in_app_iff; try right; left...
    discriminate.*)
    subst ff.
    
    remember (l1 ++ (c1, c2, vis, t1) :: l2) as g1 .
    assert (nd_pf1:
              NoDup (domain g1)).
    subst g1; rewrite domain_distr in *; simpl in *; assumption.
    eapply IHLTS with (s := s) (k := k) (pf1 := nd_pf1) in IH as (k1 &IH); clear IHLTS;
      try assumption.
    
    exists k1.
    eapply hide_remove_object in IN1b as
        [(IN1b &EQ) | (IN1b &EQ)]...

    revert dependent nd_pf1;
      erewrite Heqg1,EQ,EQ; intros.
    assert (EQ2:
              (k1 ++ (b1, b2, vis, s0) :: removeEntry (b1, b2) l1 ++ (c1, c2, hid, t1) :: l2) =
              (k1 ++ (b1, b2, vis, s0) :: removeEntry (b1, b2) l1) ++ (c1, c2, hid, t1) :: l2)...
    erewrite <-app_assoc...
    erewrite EQ2;
      eapply hide with (pf1 := nd_pf1);
      try erewrite <-app_assoc...

    revert dependent nd_pf1;
      erewrite Heqg1,EQ,EQ; intros.
    assert (EQ2:
              (k1 ++ (b1, b2, vis, s0) ::  l1 ++ (c1, c2, hid, t1) :: removeEntry (b1, b2) l2) =
              (k1 ++ (b1, b2, vis, s0) :: l1) ++ (c1, c2, hid, t1) :: removeEntry (b1, b2) l2)...
    erewrite <-app_assoc...
    erewrite EQ2;
      eapply hide with (pf1 := nd_pf1);
      try erewrite <-app_assoc...
    eapply typeEnv_eq_change_flag_removeEntry in x as EQ; try rewrite EQ...

    subst; repeat rewrite domain_distr in *; repeat simpl in *...

    eapply hide_in...
    eapply hide_in...

    simpl in NDSL;
      eapply no_dup_distr in NDSL;
      intuition.

    subst; repeat rewrite domain_distr in *; repeat simpl in *...

    subst; eapply hide_in...
    subst; eapply hide_in...
    subst; repeat rewrite domain_distr in *; repeat simpl in *...

    subst g1.
    rewrite hid_proj_app, domain_distr in *;
      simpl in *;
      unfold incl in *; introv SL.
    assert (SL2 : In a (secLabs p ++ [(c1, c2)])). eapply in_or_app...
    eapply INCL in SL2; clear INCL.

    try rewrite in_app_iff in *;
      try destruct SL2 as [OK | CONT];
      try inv CONT as [ABS | CONT2];
      try inv ABS;
      try eapply NoDup_remove_2 in NDSL;
      try rewrite app_nil_r in *;
      try contradiction...
Qed.

Lemma lts_type_plus_lin_in : forall a1 a2 t b1 b2 f f1 s s1 s0 s01 q1 q2 g pf g1 pf1,
    lts g q1 
        (aIn a1 a2 b1 b2)
        ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, s) :: removeEntry (a1,a2)(removeEntry (b1, b2) g)) q2 pf ->
    In (a1, a2, vis, Chan lin inp t) g ->
    In (b1, b2, f, s1) g ->
    In (a1, a2, vis, Chan lin inp t) g1 ->
    In (b1, b2, f1, s01) g1 ->
    type_plus s01 t s0 ->
    f1 <> hid ->
    (forall x,
        In x (domain g) <-> In x (domain g1)) ->
     NoDup (secLabs q1) ->
    incl (secLabs q1) (domain (hid_proj g1)) ->
    (*
      (forall x f1 f2,
        flagOf g x f2 ->
        flagOf g1 x f1 ->
        f2 <> f1 ->
        f2 = hid /\ f1 = ill /\
          ~In x (secLabs q1)) ->
    *)
    lts
      g1 q1 
      (aIn a1 a2 b1 b2)
      ((a1, a2, vis, Chan lin empty t)
         :: (b1, b2, vis, s0) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) q2 pf1.
Proof with eauto using in_g_in_domain.
  introv LTS INa INb IN1a IN1b TREM DIFF IFF NDSL INCL.
  assert ((a1, a2) <> (b1, b2))...
  assert (IH :  aIn a1 a2 b1 b2 = aIn a1 a2 b1 b2)...
  gen g1;
  dependent induction LTS; try intros...
  - eapply IHLTS in IH; try eapply parL...
     simpl in NDSL;
      try eapply no_dup_distr in NDSL;
      intuition.
    simpl in INCL;
      eapply incl_app_inv in INCL;
      intuition.
    (*intros x ff1 ff2; specialize FIFF with x ff1 ff2;
      simpl in *; intuition.*)
  - apply lIn with (f := f1) (t1 := s01)...
  - assert (ABS: Chan un pol t0 =  Chan lin inp t)...
    inv ABS...
  - assert (ABS: Chan un pol t0 =  Chan lin inp t)...
    inv ABS...
  - Case hide.
    remember b0 as c1; remember b3 as c2; subst b0 b3.
    assert (HEQ1:=x); assert (HEQ2 := H0); clear x H0; assert (NH := H);
      destruct H as (DIFF1 &DIFF2).

    assert (IN1: In (c1, c2) (domain g1)).
    eapply IFF; rewrite domain_distr,in_app_iff; simpl...
    eapply in_domain_in_g in IN1 as (ff &t1 &IN1);
      eapply in_split in IN1 as (l1 &l2  &EQ); subst g1.

    assert (ff = hid).
     assert (FYP: flagOf
              (l1 ++ (c1, c2, ff, t1) :: l2)
               (c1, c2)  hid).
    eapply hid_proj_flagOf;
      simpl in INCL;
      eapply incl_app_inv in INCL;
      intuition...
    repeat rewrite domain_distr in pf0;
      simpl in pf0;
      try eapply NoDup_remove_2,ListAddOns.not_in_app_and in pf0.
    inverts FYP as IN;
      try eapply in_app_iff in IN as [ABS |IN2]; try eapply in_g_in_domain in ABS;
      try inverts IN2 as EQ; try inv EQ; 
      try eapply in_g_in_domain in EQ;
      intuition.
    
    (*assert (F1: flagOf (h1 ++ (c1, c2, hid, t0) :: h2) (c1, c2) hid).
    econstructor; try eapply in_app_iff; try right; left...
    destruct ff; try tauto.
    eapply FIFF in F1; simpl in *; intuition.
    econstructor; try eapply in_app_iff; try right; left...
    discriminate.
    eapply FIFF in F1; simpl in *; intuition.
    econstructor; try eapply in_app_iff; try right; left...
    discriminate.*)
    subst ff.
    
    remember (l1 ++ (c1, c2, vis, t1) :: l2) as g1 .
    assert (nd_pf1:
              NoDup (domain g1)).
    subst g1; rewrite domain_distr in *; simpl in *; assumption.
    eapply IHLTS with (s := s)  (pf1 := nd_pf1) in IH; clear IHLTS;
      try assumption.
    assert (PF := pf0).
    eapply hide_remove_subject_object with
        (a1 :=a1) (a2 :=a2)in PF as
        [(IN1a' &IN1b' &EQ) |
         [(IN1a' &IN1b' &EQ) |
          [(IN1a' &IN1b' &EQ) |
           (IN1a' &IN1b' &EQ)]]]...

     revert dependent nd_pf1;
      erewrite Heqg1,EQ,EQ; intros.
    assert (EQ2:
              ((a1, a2, vis, Chan lin empty t)
     :: (b1, b2, vis, s0)  :: removeEntry (a1, a2)(removeEntry (b1, b2) l1) ++ (c1, c2, hid, t1) :: l2) =((a1, a2, vis, Chan lin empty t)
     :: (b1, b2, vis, s0)  :: removeEntry (a1, a2)(removeEntry (b1, b2) l1)) ++ (c1, c2, hid, t1) :: l2)...
    erewrite EQ2;
      eapply hide with (pf1 := nd_pf1);
      try erewrite <-app_assoc...

    revert dependent nd_pf1;
      erewrite Heqg1,EQ,EQ; intros.
    assert (EQ2:
              ((a1, a2, vis, Chan lin empty t)
     :: (b1, b2, vis, s0)  :: removeEntry (a1, a2)l1 ++ (c1, c2, hid, t1) :: removeEntry (b1,b2)l2) =((a1, a2, vis, Chan lin empty t)
     :: (b1, b2, vis, s0)  :: removeEntry (a1, a2)  l1) ++ (c1, c2, hid, t1) :: removeEntry (b1, b2) l2)...
    erewrite EQ2;
      eapply hide with (pf1 := nd_pf1);
      try erewrite <-app_assoc...

revert dependent nd_pf1;
      erewrite Heqg1,EQ,EQ; intros.
    assert (EQ2:
              ((a1, a2, vis, Chan lin empty t)
     :: (b1, b2, vis, s0)  :: removeEntry (b1, b2)l1 ++ (c1, c2, hid, t1) :: removeEntry (a1,a2)l2) =((a1, a2, vis, Chan lin empty t)
     :: (b1, b2, vis, s0)  :: removeEntry (b1, b2)  l1) ++ (c1, c2, hid, t1) :: removeEntry (a1, a2) l2)...
    erewrite EQ2;
      eapply hide with (pf1 := nd_pf1);
      try erewrite <-app_assoc...

    revert dependent nd_pf1;
      erewrite Heqg1,EQ,EQ; intros.
    assert (EQ2:
              ((a1, a2, vis, Chan lin empty t)
     :: (b1, b2, vis, s0)  :: l1 ++ (c1, c2, hid, t1) :: removeEntry (a1, a2)(removeEntry (b1,b2)l2)) =((a1, a2, vis, Chan lin empty t)
     :: (b1, b2, vis, s0)  ::   l1) ++ (c1, c2, hid, t1) :: removeEntry (a1, a2)(removeEntry (b1, b2) l2))...
    erewrite EQ2;
      eapply hide with (pf1 := nd_pf1);
      try erewrite <-app_assoc...

    eapply typeEnv_eq_change_flag_removeEntry_app in HEQ1; try erewrite HEQ1...

    eapply hide_in...
    eapply hide_in...
    eauto.
     simpl in NDSL;
      eapply no_dup_distr in NDSL;
      intuition.
    subst; eapply hide_in...
    subst; eapply hide_in...
    subst; repeat rewrite domain_distr in *; repeat simpl in *...

       subst g1.
    rewrite hid_proj_app, domain_distr in *;
      simpl in *;
      unfold incl in *; introv SL.
    assert (SL2 : In a (secLabs p ++ [(c1, c2)])). eapply in_or_app...
    eapply INCL in SL2; clear INCL.

    try rewrite in_app_iff in *;
      try destruct SL2 as [OK | CONT];
      try inv CONT as [ABS | CONT2];
      try inv ABS;
      try eapply NoDup_remove_2 in NDSL;
      try rewrite app_nil_r in *;
      try contradiction...
    
(*     subst; eapply hide_flagOf...
     simpl; eapply incl_appl...*)
Qed.

Lemma type_plus_unique: forall s t t1 t2,
    type_plus s t t1 ->
    type_plus s t t2 ->
    
    t1 = t2.
Proof with eauto.
  intros.
  destruct s. destruct t.
  inversion H. inversion H0.
  subst.
  inversion H8; inversion H16; subst.
  eauto. eauto. inversion H4. inversion H4. eauto. eauto.
  inversion H5. inversion H5. inversion H4. inversion H5.
  eauto. eauto. inversion H4. inversion H5. eauto.
  eauto. subst. inversion H10. subst.
  inversion H0; inversion H; subst.
  eauto. inversion H; inversion H0; subst.
  inversion H; inversion H0; subst.
  tauto.
Qed.

#[global] Hint Resolve type_plus_unique.


(*Fixpoint sethid x (g : typeEnv) :=
  match g with
  | nil => nil
  | (y, f, t) :: tl =>
      if nat_pair_eq_dec x  y
      then (y, hid , t) :: tl
      else (y, f, t) :: sethid x tl
  end.

Lemma setHid_app_cons g1 x f t g2:
  ~In x (domain g1) ->
  sethid x (g1 ++ (x, f, t) :: g2) =
    g1 ++ (x, hid, t) :: g2.
Proof with eauto.
  introv NIN.
  
  
Lemma sethid_once  x g g1 g2 f t:
  count_occ nat_pair_eq_dec (domain g) x = 1 ->
  g = g1 ++ (x, f, t) :: g2 ->
  sethid x g = g1 ++ (x, hid, t) :: g2. 
Proof with eauto using setHid_app_cons.
  introv CNT EQ; subst;
    rewrite domain_distr, count_occ_app in *; simpl in *.
  case_eq (nat_pair_eq_dec x x); introv EQ;
    rewrite EQ in *; try contradiction.
  assert  (ZERO1 :count_occ nat_pair_eq_dec (domain g1) x=0) by lia.
   assert (NIN1 : not (count_occ nat_pair_eq_dec (domain g1) x > 0)) by lia.
   erewrite <-count_occ_In in *...
Qed.   
*)

Lemma lts_un_input_action:   forall g p a1 a2 b1 b2 g1 p' nd_pf pol t s r,
    lts g p (aIn a1 a2 b1 b2) g1 p' nd_pf ->
    typeOf g (a1, a2) (Chan un pol t) ->
    typeOf g (b1, b2) s ->
    type_plus s t r ->
    sl_pos p ->
    max (secLabs p) <= max (domain g) ->
    exists k,
      disjoint (domain k) (domain g) /\
      g1 = k ++ ((b1, b2), vis, r) :: removeEntry (b1, b2) g.
Proof with eauto.
  introv LTS TYPa TYPb TP SLP MAX.
  dependent induction LTS.
  
  - eapply sl_pos_par_l in SLP;
      eapply max_sl_par in MAX as (MAX&_);
      specialize IHLTS with a1 a2 b1 b2...
  - inverts TYPa as IN.
    assert (vis = f0 /\ Chan lin inp t0 = Chan un pol t).
    apply in_isMap with (x := (a1, a2)) (g := g)...
    intuition. inversion H5...
  - assert (DISNIL:
              forall g, disjoint nil (domain g)).
    introv; try erewrite <-disjoint_car;
      try eapply dis_nil...
    inverts TYPb as INb.
    assert (EQ: f = f0 /\ t1 = s).
    apply in_isMap with (x := (b1, b2)) (g := g)...
    intuition; subst.
    inverts TYPa as INa.
    assert (EQ: vis = f /\ Chan un inp t0 = Chan un pol t).
    apply in_isMap with (x := (a1, a2)) (g := g)...
    destruct EQ as [EQ1 EQ2]; inv EQ2; subst.
    assert (t2 = r)... subst.
    exists (nil:typeEnv)...
     inverts TYPa as INa.
    assert (EQ: vis = f /\ Chan un io t0 = Chan un pol t).
    apply in_isMap with (x := (a1, a2)) (g := g)...
    destruct EQ as [EQ1 EQ2]; inv EQ2; subst.
    assert (t2 = r)... subst.
    exists (nil:typeEnv)...
  - inverts TYPb as INb.
    assert (f = f0 /\ t1 = s).
    apply in_isMap with (x := (b1, b2)) (g := g)...
    intuition; subst.
    inverts TYPa as INa.
    assert (EQ: vis = f /\ Chan un inp t0 = Chan un pol t).
    apply in_isMap with (x := (a1, a2)) (g := g)...
    destruct EQ as [EQ1 EQ2]; inv EQ2; subst.
    assert (t2 = r)... subst.
    exists (newEntries g (secLabs q) (max (domain g))); split...
    erewrite disjoint_commute; eapply new_entries_disjoint...
    inverts TYPa as INa.
    assert (EQ: vis = f /\ Chan un io t0 = Chan un pol t).
    apply in_isMap with (x := (a1, a2)) (g := g)...
    destruct EQ as [EQ1 EQ2]; inv EQ2; subst.
    assert (t2 = r)... subst.
    exists (newEntries g (secLabs q) (max (domain g))); split...
    erewrite disjoint_commute; eapply new_entries_disjoint...
  - remember b0 as c1. remember b3 as c2.
    subst b0 b3.
    try destruct H as (DIFF1 &DIFF2).
    assert (IH:
             aIn a1 a2 b1 b2 = aIn a1 a2 b1 b2)...
    eapply IHLTS in IH; clear IHLTS...
    destruct IH as (k &DIS &EQ);
      exists k.

    split.

    rewrite domain_distr in *; simpl in *...

    assert (NIN0: ~In (c1, c2) (domain k)).
    introv ABS; eapply disjoint_absurd...
    try rewrite domain_distr,in_app_iff;
      simpl;
      try right...
    assert (C0: count_occ nat_pair_eq_dec (domain k)  (c1, c2) = 0)...
    erewrite count_occ_In
      with (eq_dec := nat_pair_eq_dec) in NIN0;
      try lia...
    assert (CNT := pf1). move CNT at bottom. 
    erewrite NoDup_count_occ'
      with (decA := nat_pair_eq_dec)in CNT...
    assert (IN: In (c1, c2)
                  (domain (h1 ++ (c1, c2, vis, t0) :: h2))).
    rewrite domain_distr,in_app_iff; simpl;right...
    eapply CNT in IN...
    repeat rewrite domain_distr,count_occ_app with
      (eq_dec :=nat_pair_eq_dec) in IN;
      simpl in IN;
      case_eq( nat_pair_eq_dec (c1, c2) (c1, c2)); introv BEQ; try rewrite BEQ in *; try contradiction...
    assert (C1: count_occ nat_pair_eq_dec (domain h1) (c1, c2) = 0) by lia.
    assert (C2: count_occ nat_pair_eq_dec (domain h2) (c1, c2) = 0) by lia.
    assert (NIN1 : not (count_occ nat_pair_eq_dec (domain h1) (c1, c2) > 0)) by lia...
    assert (NIN2 : not (count_occ nat_pair_eq_dec (domain h2) (c1, c2) > 0)) by lia...
    rewrite <-count_occ_In in *.

    eapply typeEnv_eq_change_flag_removeEntry...
    rewrite domain_distr in *; simpl in *...
    eapply typeOf_hide_app...
    eapply typeOf_hide_app...
    eapply sl_pos_nu...
    
    eapply max_sl_nu in MAX.
    erewrite max_same_domain with (m :=(domain (h1 ++ (c1, c2, vis, t0) :: h2)))...

    repeat rewrite domain_distr; simpl...
    intuition.
Qed.


Lemma lts_type_remove_lin_out : forall a1 a2 t b1 b2 f f1 s s1 s0 s01 p1 p2 g0 pf0 g1 pf1,
    lts g0 p1
        (aOut a1 a2 b1 b2)
        ((a1, a2, vis, Chan lin empty t) :: (b1, b2, f1, s1) :: (removeEntry (a1, a2) (removeEntry (b1, b2) g0))) p2 pf0 ->
    In (a1, a2, vis, Chan lin out t) g0 ->
    In (b1, b2, f, s) g0 ->
    type_remove s0 t s01 ->
    In (a1, a2, vis, Chan lin out t) g1 ->
    In (b1, b2, f, s0) g1 ->
    (forall x,
        In x (domain g0) <-> In x (domain g1)) ->
     NoDup (secLabs p1) ->
    incl (secLabs p1) (domain (hid_proj g1)) ->
    lts g1 p1
        (aOut a1 a2 b1 b2)
        ((a1, a2, vis, Chan lin empty t) :: (b1, b2, f1, s01) :: (removeEntry (a1, a2) (removeEntry (b1, b2) g1))) p2 pf1.
Proof with eauto.
  introv LTS INa INb TREM INa1 INb1 IFF
  NDSL INCL.
  assert ((a1, a2) <> (b1, b2))...
  assert (IH :  aOut a1 a2 b1 b2 = aOut a1 a2 b1 b2)...
  generalize dependent f. generalize dependent g1.
  dependent induction LTS.
  
  - specialize IHLTS with
        (a1 := a1) (a2 := a2)
        (b1 := b1) (b2 := b2)
        (t := t)
        (s1 := s1)  (f1 := f1). 
    simpl; intros.
    eapply IHLTS in IH...
    apply parL...
     simpl in NDSL;
      try eapply no_dup_distr in NDSL;
      intuition.
    simpl in INCL;
      eapply incl_app_inv in INCL;
      intuition.
    (*intros x ff1 ff2; specialize FIMPL with x ff1 ff2; intuition.*)
  - intros. apply lOut with (t1 := s0).
    specialize flag_of_map with g (b1, b2) vis f as FYP...
    assumption.
    specialize flag_of_map with g (b1, b2) vis f as FYP.
    assert (isMap g)...
    assert (flagOf g (b1, b2) vis)...
    assert ( flagOf g (b1, b2) f)...
    intuition. subst...
  - intuition.
  - intros. assert (f = hid)... subst.
    assert (pf4 : NoDup (domain ((b1, b2, vis, s0) :: removeEntry (b1, b2) g1))). apply no_dup_cons_removeEntry...
    specialize IHLTS with
        (a1 := a1) (a2 := a2)
        (b1 := b1) (b2 := b2) (t := t)
        (s1 := s1) (f1 := f1)
        (f := vis)
        (pf1 := pf4).
    
    remember (removeEntry (a1, a2) (removeEntry (b1, b2) g)) as g0.
    assert (REM: removeEntry (a1, a2) (removeEntry (b1, b2) ((b1, b2, vis, t0) :: removeEntry (b1, b2) g)) = g0).
    unfold removeEntry at 2; fold removeEntry.
    assert (pair_eq (b1, b2) (b1, b2) = true)...
    rewrite H1...
    rewrite REM in IHLTS.
    (*apply removeEntry_in...*)
    assert (In (a1, a2, vis, Chan lin out t) ((b1, b2, vis, s0) :: removeEntry (b1, b2) g1)). 
    apply in_app_iff with (l := ((b1, b2, vis, s0) :: nil)). right.
    apply removeEntry_in...
    assert (In (a1, a2, vis, Chan lin out t) ((b1, b2, vis, t0) :: removeEntry (b1, b2) g)).
     apply in_app_iff with (l := ((b1, b2, vis, t0) :: nil)). 
    right. 
    apply removeEntry_in...
    
    specialize in_isMap with (b1, b2) hid t0 hid s g as IN.
    apply IN in H... destruct H;
                     subst.
    assert (In (b1, b2, vis, s) ((b1, b2, vis, s) :: removeEntry (b1, b2) g) )...
    assert (In (b1, b2, vis, s0) ((b1, b2, vis, s0) :: removeEntry (b1, b2) g1) )...

    eapply IHLTS in IH; clear IHLTS...

    apply open  with (t := s0) (pf1 := pf4).
    all:eauto.
    assert (removeEntry (a1, a2)
                        (removeEntry (b1, b2) ((b1, b2, vis, s0) :: removeEntry (b1, b2) g1))
                         = removeEntry (a1, a2) (removeEntry (b1, b2) g1)).
    unfold removeEntry at 2; fold removeEntry.
    assert (PEQ: pair_eq (b1, b2) (b1, b2) = true)...
    rewrite PEQ...
    rewrite H5 in *...

    simpl in NDSL;
      eapply no_dup_distr in NDSL; intuition.

    intros [x1 x2];  unfold domain; fold domain; split; try introv IN2;
      try inv IN2 as [EQ|IN3]; try inv EQ...
    
    right.
    assert (IN4 := IN3);
      eapply in_domain_in_g in IN3 as (ff &tt &IN3);
      eapply in_removeEntry,in_g_in_domain,IFF in IN3;
      eapply in_domain_in_g in IN3 as (ff1 &tt1 &IN3).
    try eapply in_g_in_domain;
      try eapply removeEntry_in; try intros ABS; try inv ABS...
    try eapply in_domain_in_g in IN4 as (ff2 &tt2 &IN4);
      try eapply no_dup_not_in_removeEntry in IN4...

    right.
    assert (IN4 := IN3);
      eapply in_domain_in_g in IN3 as (ff &tt &IN3);
      eapply in_removeEntry,in_g_in_domain,IFF in IN3;
      eapply in_domain_in_g in IN3 as (ff1 &tt1 &IN3).
    try eapply in_g_in_domain;
      try eapply removeEntry_in; try intros ABS; try inv ABS...
    try eapply in_domain_in_g in IN4 as (ff2 &tt2 &IN4);
      try eapply no_dup_not_in_removeEntry in IN4...

    
    move NDSL at bottom; simpl in *;
      unfold incl in INCL; introv SL.
    assert (SL2 : In a (secLabs p ++ [(b1, b2)])). eapply in_or_app...
    eapply INCL in SL2; clear INCL; simpl.
    eapply in_domain_in_g in SL2 as (f2 &t2 &SL2);
      eapply  removeEntry_in with (y := (b1, b2)),in_g_in_domain in SL2;
      try rewrite <-hid_proj_removeEntry...
      try introv ABS;subst;
      eapply no_dup_disjoint in NDSL;
        try eapply disjoint_absurd...
    
  

    
  - intros.
    remember b0 as c1. remember b3 as c2. subst b0 b3.
    assert (NH:= H); destruct H as (DIFF1 &DIFF2).

    assert (IN1: In (c1, c2) (domain g1)).
    erewrite <-IFF; 
      erewrite domain_distr; 
      try eapply in_app_iff; try right;simpl...
    eapply in_domain_in_g in IN1 as (ff1 &tt1 &IN1);
      eapply in_split in IN1 as (l1 &l2 &EQ); subst g1.

    assert (IH2: flagOf (h1 ++ (c1, c2, hid, t0) :: h2) (c1,c2) hid ).
    econstructor; try eapply in_app_iff; right...

    assert (EQ: ff1 = hid).
    assert (FYP: flagOf
              (l1 ++ (c1, c2, ff1, tt1) :: l2)
               (c1, c2)  hid).
    eapply hid_proj_flagOf;
      simpl in INCL;
      eapply incl_app_inv in INCL;
      intuition...
    repeat rewrite domain_distr in pf0;
      simpl in pf0;
      try eapply NoDup_remove_2,ListAddOns.not_in_app_and in pf0.
    inverts FYP as IN;
      try eapply in_app_iff in IN as [ABS |IN2]; try eapply in_g_in_domain in ABS;
      try inverts IN2 as EQ; try inv EQ; 
      try eapply in_g_in_domain in EQ;
      intuition.

    subst ff1.
    remember (l1 ++ (c1, c2, vis, tt1) :: l2) as g1.
    assert (nd_pf1 : NoDup (domain g1)).
    subst g1; rewrite domain_distr in *;
      simpl in *...

    assert (HEQ1 := x).
    eapply IHLTS with (f1 := f1)(s1 := s1)(t := t)(pf1 := nd_pf1) in IH;
      try tauto; try assumption.

     assert (PF := pf0).
    eapply hide_remove_subject_object with
        (a1 :=a1) (a2 :=a2)in PF as
        [(IN1a' &IN1b' &EQ) |
         [(IN1a' &IN1b' &EQ) |
          [(IN1a' &IN1b' &EQ) |
           (IN1a' &IN1b' &EQ)]]]...

     revert dependent nd_pf1;
      erewrite Heqg1,EQ,EQ; intros.
    assert (EQ2:
              ((a1, a2, vis, Chan lin empty t)
     :: (b1, b2, f1, s01)  :: removeEntry (a1, a2)(removeEntry (b1, b2) l1) ++ (c1, c2, hid, tt1) :: l2) =((a1, a2, vis, Chan lin empty t)
     :: (b1, b2, f1, s01)  :: removeEntry (a1, a2)(removeEntry (b1, b2) l1)) ++ (c1, c2, hid, tt1) :: l2)...
    erewrite EQ2;
      eapply hide with (pf1 := nd_pf1);
      try erewrite <-app_assoc...

    revert dependent nd_pf1;
      erewrite Heqg1,EQ,EQ; intros.
    assert (EQ2:
              ((a1, a2, vis, Chan lin empty t)
     :: (b1, b2, f1, s01)  :: removeEntry (a1, a2)l1 ++ (c1, c2, hid, tt1) :: removeEntry (b1,b2)l2) =((a1, a2, vis, Chan lin empty t)
     :: (b1, b2, f1, s01)  :: removeEntry (a1, a2)  l1) ++ (c1, c2, hid, tt1) :: removeEntry (b1, b2) l2)...
    erewrite EQ2;
      eapply hide with (pf1 := nd_pf1);
      try erewrite <-app_assoc...

revert dependent nd_pf1;
      erewrite Heqg1,EQ,EQ; intros.
    assert (EQ2:
              ((a1, a2, vis, Chan lin empty t)
     :: (b1, b2, f1, s01)  :: removeEntry (b1, b2)l1 ++ (c1, c2, hid, tt1) :: removeEntry (a1,a2)l2) =((a1, a2, vis, Chan lin empty t)
     :: (b1, b2, f1, s01)  :: removeEntry (b1, b2)  l1) ++ (c1, c2, hid, tt1) :: removeEntry (a1, a2) l2)...
    erewrite EQ2;
      eapply hide with (pf1 := nd_pf1);
      try erewrite <-app_assoc...

    revert dependent nd_pf1;
      erewrite Heqg1,EQ,EQ; intros.
    assert (EQ2:
              ((a1, a2, vis, Chan lin empty t)
     :: (b1, b2, f1, s01)  :: l1 ++ (c1, c2, hid, tt1) :: removeEntry (a1, a2)(removeEntry (b1,b2)l2)) =((a1, a2, vis, Chan lin empty t)
     :: (b1, b2, f1, s01)  ::   l1) ++ (c1, c2, hid, tt1) :: removeEntry (a1, a2)(removeEntry (b1, b2) l2))...
    erewrite EQ2;
      eapply hide with (pf1 := nd_pf1);
      try erewrite <-app_assoc...

    eapply typeEnv_eq_change_flag_removeEntry_app in HEQ1; try erewrite HEQ1...

    eapply hide_in...
     simpl in NDSL;
      eapply no_dup_distr in NDSL;
       intuition.
    
     subst; eapply hide_in...
    subst; repeat rewrite domain_distr in *; repeat simpl in *...
    
       subst g1.
    rewrite hid_proj_app, domain_distr in *;
      simpl in *;
      unfold incl in *; introv SL.
    assert (SL2 : In a (secLabs p ++ [(c1, c2)])). eapply in_or_app...
    eapply INCL in SL2; clear INCL.

    try rewrite in_app_iff in *;
      try destruct SL2 as [OK | CONT];
      try inv CONT as [ABS | CONT2];
      try inv ABS;
      try eapply NoDup_remove_2 in NDSL;
      try rewrite app_nil_r in *;
      try contradiction...

    erewrite in_app_iff in *;
      destruct INb as [LEFT | CONT].   
      try left...
      inv CONT as [ABS | CONT2];
        try inv ABS; try contradiction...
      repeat right...

      subst g1.
      erewrite in_app_iff in *;
      destruct INb1 as [LEFT | CONT].   
      try left...
      inv CONT as [ABS | CONT2];
        try inv ABS; try contradiction...
      repeat right...
    
 
      
Qed.
    

Lemma lts_type_remove_un_out : forall a1 a2 pol t b1 b2 f f1 s s1 s0 s01 p1 p2 g pf g1 pf1,
    In (a1, a2, vis, Chan un pol t) g ->
    In (b1, b2, f, s) g ->
    lts g p1
        (aOut a1 a2 b1 b2)
        ((b1, b2, f1, s1) :: removeEntry (b1, b2) g) p2 pf ->
    type_remove s0 t s01 ->
    In (a1, a2, vis, Chan un pol t) g1 ->
    In (b1, b2, f, s0) g1 ->
    (forall x,
        In x (domain g) <-> In x (domain g1)) ->
     NoDup (secLabs p1) ->
     incl (secLabs p1) (domain (hid_proj g1)) ->
    (* (forall x f1 f2,
        flagOf g x f2 ->
        flagOf g1 x f1 ->
        f2 <> f1 ->
        f2 = hid /\ f1 = ill /\
        ~In x (secLabs p1)) ->*)
    lts g1 p1
        (aOut a1 a2 b1 b2)
        ((b1, b2, f1, s01) :: removeEntry (b1, b2) g1) p2 pf1.
Proof with eauto.
  intros a1 a2 pol t b1 b2 f f1 s s1 s0 s01 p1 p2 g pf g1 pf1
         INa INb LTS TREM INa1 INb1 IFF NDSL INCL.
  assert ((a1, a2) <> (b1, b2))...
  assert (IH :  aOut a1 a2 b1 b2 = aOut a1 a2 b1 b2)...
  generalize dependent f.
  generalize dependent g1.
  dependent induction LTS.
  
  - simpl; intros.
    eapply IHLTS with
        (a1 := a1) (a2 := a2)
        (b1 := b1) (b2 := b2) (pf := pf)
        (s1 := s1) (g := g) (f1 := f1) 
        (pf1 := pf1) in IH...
    apply parL...
     simpl in NDSL;
      try eapply no_dup_distr in NDSL;
      intuition.
    simpl in INCL;
      eapply incl_app_inv in INCL;
      intuition.
   (* intros x ff1 ff2; specialize FIMPL with x ff1 ff2; intuition.*)
  -  contradiction.
  - intros.
    apply uOut with (pol := pol0) (t := t) (t1 := s0).
    all:eauto.
    specialize type_of_map with
        g (a1, a2)  (Chan un pol0 t0) (Chan un pol t) as TYP.
    apply no_dup_isMap in pf as pf_m.
    apply TYP in pf_m. inversion pf_m; subst...
    all:eauto.
    specialize flag_of_map with
        g (b1, b2) vis f as FYP.
    apply no_dup_isMap in pf as pf_m.
    apply FYP in pf_m. subst...
    all:eauto.
  - intros. assert (f = hid)... subst.
    specialize IHLTS with
        (g1 := (b1, b2, vis, s0) :: removeEntry (b1, b2) g1).
    assert (pf1' : NoDup (domain ((b1, b2, vis, t0) :: removeEntry (b1, b2) g1))).
    apply no_dup_cons_removeEntry...
    

    assert (IN: In (a1, a2, vis, Chan un pol t) ((b1, b2, vis, t0) :: removeEntry (b1, b2) g)).
    apply in_app_iff with (l := (b1, b2, vis, t0) :: nil).
    right.
    apply removeEntry_in...
    assert (IN1: In (a1, a2, vis, Chan un pol t) ((b1, b2, vis, s0) :: removeEntry (b1, b2) g1)).
    right.
    apply removeEntry_in...
    assert (EQ: (b1, b2, f1, s1) :: removeEntry (b1, b2) g =
                (b1, b2, f1, s1) :: removeEntry (b1, b2) ((b1, b2, vis, t0) :: removeEntry (b1, b2) g)).
    unfold removeEntry at 2.
    assert (BEQ: pair_eq (b1, b2) (b1, b2) = true)...
    rewrite BEQ...
    rewrite EQ in IHLTS.
    intuition.
    assert (s = t0)... subst t0.
    
    
    assert (IN3: In (b1, b2, vis, s) ((b1, b2, vis, s) :: removeEntry (b1, b2) g)) by apply in_eq.
    assert (IN4: In (b1, b2, vis, s0) ((b1, b2, vis, s0) :: removeEntry (b1, b2) g1)) by apply in_eq.
    

    eapply  IHLTS with
        (f1 := f1)  (a1 := a1) (a2 := a2)
        (b1 := b1) (b2 := b2) 
        (s1 := s1)  (g := (b1, b2, vis, s) :: removeEntry (b1, b2) g)
        (pf := pf1) (pf1 := pf1') in IH...

    

    apply open with (t := s0) (pf := pf0) (pf1 := pf1')...
    assert (EQ2:removeEntry (b1, b2) ((b1, b2, vis, s0) :: removeEntry (b1, b2) g1) = removeEntry (b1, b2) g1).
    unfold removeEntry.  assert (BEQ: pair_eq (b1, b2) (b1, b2) = true)...
    rewrite BEQ...
    rewrite EQ2 in *...

    simpl in NDSL;
      eapply no_dup_distr in NDSL; intuition.
    
      intros [x1 x2];  unfold domain; fold domain; split; try introv IN2;
      try inv IN2 as [EQ'|IN3']; try inv EQ'...
    
    right.
    assert (IN4' := IN3');
      eapply in_domain_in_g in IN3' as (ff &tt &IN3');
      eapply in_removeEntry,in_g_in_domain,IFF in IN3';
      eapply in_domain_in_g in IN3' as (ff1 &tt1 &IN3').
    try eapply in_g_in_domain;
      try eapply removeEntry_in; try intros ABS; try inv ABS...
    try eapply in_domain_in_g in IN4' as (ff2 &tt2 &IN4');
      try eapply no_dup_not_in_removeEntry in IN4'...

    right.
    assert (IN4' := IN3');
      eapply in_domain_in_g in IN3' as (ff &tt &IN3');
      eapply in_removeEntry,in_g_in_domain,IFF in IN3';
      eapply in_domain_in_g in IN3' as (ff1 &tt1 &IN3').
    try eapply in_g_in_domain;
      try eapply removeEntry_in; try intros ABS; try inv ABS...
    try eapply in_domain_in_g in IN4' as (ff2 &tt2 &IN4');
      try eapply no_dup_not_in_removeEntry in IN4'...

    
    move NDSL at bottom; simpl in *;
      unfold incl in INCL; introv SL.
    assert (SL2 : In a (secLabs p ++ [(b1, b2)])). eapply in_or_app...
    eapply INCL in SL2; clear INCL; simpl.
    eapply in_domain_in_g in SL2 as (f2 &t2 &SL2);
      eapply  removeEntry_in with (y := (b1, b2)),in_g_in_domain in SL2;
      try rewrite <-hid_proj_removeEntry...
      try introv ABS;subst;
      eapply no_dup_disjoint in NDSL;
        try eapply disjoint_absurd...
    
    
  - intros.

    remember b0 as c1. remember b3 as c2. subst b0 b3.
    assert (NH:= H); destruct H as (DIFF1 &DIFF2).

    assert (IN1: In (c1, c2) (domain g1)).
    erewrite <-IFF; 
      erewrite domain_distr; 
      try eapply in_app_iff; try right;simpl...
    eapply in_domain_in_g in IN1 as (ff1 &tt1 &IN1);
      eapply in_split in IN1 as (l1 &l2 &EQ); subst g1.

    assert (IH2: flagOf (h1 ++ (c1, c2, hid, t0) :: h2) (c1,c2) hid ).
    econstructor; try eapply in_app_iff; right...

     assert (EQ: ff1 = hid).
    assert (FYP: flagOf
              (l1 ++ (c1, c2, ff1, tt1) :: l2)
               (c1, c2)  hid).
    eapply hid_proj_flagOf;
      simpl in INCL;
      eapply incl_app_inv in INCL;
      intuition...
    repeat rewrite domain_distr in pf0;
      simpl in pf0;
      try eapply NoDup_remove_2,ListAddOns.not_in_app_and in pf0.
    inverts FYP as IN;
      try eapply in_app_iff in IN as [ABS |IN2]; try eapply in_g_in_domain in ABS;
      try inverts IN2 as EQ; try inv EQ; 
      try eapply in_g_in_domain in EQ;
      intuition.

    subst ff1.
    remember (l1 ++ (c1, c2, vis, tt1) :: l2) as g1.
    assert (nd_pf1 : NoDup (domain g1)).
    subst g1; rewrite domain_distr in *;
      simpl in *...

    assert (HEQ1 := x).
    eapply IHLTS with (f1 := f1)(s1 := s1)(pf1 := nd_pf1) in IH;
      try tauto; try assumption.

    assert (PF := pf0).
    eapply hide_remove_object with
        (b1 :=b1) (b2 :=b2) in PF as
        [(IN1b' &EQ) |
           (IN1b' &EQ)]...

     revert dependent nd_pf1;
      erewrite Heqg1,EQ,EQ; intros.
    assert (EQ2:
              ( (b1, b2, f1, s01)  :: removeEntry (b1, b2) l1) ++ (c1, c2, hid, tt1) :: l2 =( (b1, b2, f1, s01)  :: (removeEntry (b1, b2) l1) ++ (c1, c2, hid, tt1) :: l2))...
    erewrite <-EQ2;
      eapply hide with (pf1 := nd_pf1);
      try erewrite <-app_assoc...

    revert dependent nd_pf1;
      erewrite Heqg1,EQ,EQ; intros.
    assert (EQ2:
              ((b1, b2, f1, s01)  :: l1 ++ (c1, c2, hid, tt1) :: removeEntry (b1,b2)l2) =((b1, b2, f1, s01)  ::   l1) ++ (c1, c2, hid, tt1) :: removeEntry (b1, b2) l2)...
    erewrite EQ2;
      eapply hide with (pf1 := nd_pf1);
      try erewrite <-app_assoc...

     eapply hide_in...

     (*  h' ++ (c1, c2, vis, t') :: h'' ~=
  (b1, b2, f1, s1) :: removeEntry (b1, b2) (h1 ++ (c1, c2, vis, t0) :: h2) *)
     eapply typeEnv_eq_change_flag_removeEntry with (k1 := h')(k2 := h'')(h:=nil)(h1 := h1)
       in DIFF2;
       repeat rewrite app_nil_l in *;
       try rewrite DIFF2...

     simpl...

     simpl in NDSL;
      eapply no_dup_distr in NDSL;
       intuition.
    
     subst; eapply hide_in...
    subst; repeat rewrite domain_distr in *; repeat simpl in *...
    
       subst g1.
    rewrite hid_proj_app, domain_distr in *;
      simpl in *;
      unfold incl in *; introv SL.
    assert (SL2 : In a (secLabs p ++ [(c1, c2)])). eapply in_or_app...
    eapply INCL in SL2; clear INCL.

    try rewrite in_app_iff in *;
      try destruct SL2 as [OK | CONT];
      try inv CONT as [ABS | CONT2];
      try inv ABS;
      try eapply NoDup_remove_2 in NDSL;
      try rewrite app_nil_r in *;
      try contradiction...

    erewrite in_app_iff in *;
      destruct INb as [LEFT | CONT].   
      try left...
      inv CONT as [ABS | CONT2];
        try inv ABS; try contradiction...
      repeat right...

      subst g1.
      erewrite in_app_iff in *;
      destruct INb1 as [LEFT | CONT].   
      try left...
      inv CONT as [ABS | CONT2];
        try inv ABS; try contradiction...
      repeat right...
Qed.
