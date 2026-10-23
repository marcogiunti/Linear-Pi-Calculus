Require Import
        Bool List Lia PeanoNat Program.Equality
        ListAddOns Max RemoveEntry Domain Classical
        header
        operations pi_syntax
        pairEq type_system semantics 
        type_operations_1
        split_exists_neutral
        sub_split
        split_existential
        no_dup_split_no_dup
        split_not_exists
        split_operations
        lts_operations
        split_operations_2
        split_operations_3
        proposition27
        type_checking_0
        type_system_rules
        disjoint_newEntries.

Require Import CpdtTactics LibTactics.

#[global] Hint Resolve nonRecTypes.
#[global] Hint Resolve nonRecActions1.
#[global] Hint Resolve nonRecActions2.

(* List Operations *)

#[global] Hint Resolve projections_injective.
#[global] Hint Resolve rec_In.
#[global] Hint Resolve fold_In.
#[global] Hint Resolve incl_distr.
#[global] Hint Resolve rec_disjoint.
#[global] Hint Resolve dis_nil.
#[global] Hint Resolve dis_cons.
#[global] Hint Resolve disjoint_cons_l.
#[global] Hint Resolve disjoint_cons_r.
#[global] Hint Resolve disjoint_l_cons.
#[global] Hint Resolve disjoint_r_cons.
#[global] Hint Resolve disjoint_commute.
#[global] Hint Resolve disjoint_app_l.
#[global] Hint Resolve disjoint_app_r.
#[global] Hint Resolve disjoint_2_cons_l.
#[global] Hint Resolve disjoint_2_l_cons.
#[global] Hint Resolve disjoint_car.
#[global] Hint Resolve disjoint_2_comm.
#[global] Hint Resolve not_in_app_and.
#[global] Hint Resolve no_dup_app_l.
#[global] Hint Resolve no_dup_app_r.
#[global] Hint Resolve no_dup_distr.
#[global] Hint Resolve no_dup_disjoint.
#[global] Hint Resolve no_dup_iff.
#[global] Hint Resolve map_app.

#[global] Hint Resolve NoDup_nil.
#[global] Hint Resolve NoDup_cons.
#[global] Hint Resolve NoDup_cons_iff.

(* Type Operations *)
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
#[global] Hint Resolve tsub_payload.
#[global] Hint Resolve tsuper_payload.
#[global] Hint Resolve tsuper_payload_r.
#[global] Hint Resolve tsuper_top.
#[global] Hint Resolve tsuper_top_r.

#[global] Hint Resolve fsub_hid.
#[global] Hint Resolve fsub_ill.
#[global] Hint Resolve fsub_vis.
#[global] Hint Resolve fsub_hid_r.
#[global] Hint Resolve fsub_ill_r.
#[global] Hint Resolve fsub_vis_r.
#[global] Hint Resolve fsuper_vis.

#[global] Hint Resolve type_of_in_action.
#[global] Hint Resolve type_of_out_action.
#[global] Hint Resolve flag_of_split_l.
#[global] Hint Resolve split_of_split.
#[global] Hint Resolve split_exists_remove_l.
#[global] Hint Resolve split_not_exists_lts.
#[global] Hint Resolve split_lts_exists_remove_l.
(*Hint Resolve split_lts_exists_lts.*)


#[global] Hint Resolve unique_remove.
#[global] Hint Resolve no_dup_not_in_removeEntry.
#[global] Hint Resolve no_dup_removeEntry_no_dup.
#[global] Hint Resolve no_dup_isMap.
#[global] Hint Resolve cons_isMap.
#[global] Hint Resolve cons_removeEntry.
#[global] Hint Resolve cons_removeEntry_app.
#[global] Hint Resolve sl_pos_par_l.
#[global] Hint Resolve sl_pos_par_r.
#[global] Hint Resolve typeCheck_vis.
#[global] Hint Resolve typeCheck_hid.

#[global] Hint Resolve count_occ_removeEntry.
#[global] Hint Resolve count_occ_removeEntry_neq.
#[global] Hint Resolve no_dup_split_no_dup_l.
#[global] Hint Resolve no_dup_split_no_dup_r.
#[global] Hint Resolve super_in_sub.
           
  
#[global] Hint Unfold nonRec_typable.
#[global] Hint Resolve typeCheck_object_neq_subject.
#[global] Hint Resolve incl_nil_l incl_l_nil.


Lemma no_dup_cons_removeEntry_app_1 : forall u x f1 t1 f2 t2 g (pf : NoDup(domain g)),
    u <> x ->
    ~In x (domain g) ->
    NoDup (domain ((u, f1, t1) :: (x, f2, t2) :: removeEntry u g)).
Proof with eauto.
  intros. 
  induction g.
  unfold domain; fold domain.
  rewrite NoDup_cons_iff...
  intuition.
  inversion H1; subst; intuition.
  apply no_dup_domain_cons in pf as pf1. apply IHg in pf1 as K; clear IHg.
  unfold domain; fold domain; rewrite NoDup_cons_iff...
  unfold domain in K; fold domain in K; rewrite NoDup_cons_iff in K...
  split. intro.
  inversion H1; subst...
  apply in_domain_in_g in H2. destruct H2 as [f3 [t3 IN]]. 
  eapply no_dup_not_in_removeEntry in IN...
  rewrite NoDup_cons_iff...
  split... intro. apply in_domain_in_g in H1.
  destruct H1 as [f3 [t3 IN]].
  apply in_removeEntry in IN.
  apply in_g_in_domain in IN...
  intro. destruct a as [[a f3] t3].
  unfold domain in H0; fold domain in H0.
  intuition.
Qed.

(*Hint Resolve in_domain_removeEntry.*)

Lemma typeCheck_no_dup : forall g p pf,
    NoDup (domain g) ->
    typeCheck g pf p->
    (incl (secLabs p)  (domain g) /\
    NoDup (secLabs p)).
Proof with eauto.
  intros g p pf nd_pf TC.
  apply typeCheck_object_neq_subject in TC as NT.
  dependent induction TC.
  - unfold secLabs... 
  - unfold secLabs; fold secLabs.
    unfold domain in IHTC; fold domain in IHTC.
    apply no_dup_removeEntry_no_dup with
        g n
      in nd_pf as nd_pf1.
    assert (In n (domain (removeEntry n g)) -> False).
    intros ABS.
    apply in_domain_in_g in ABS.
    destruct ABS as [f1 [ t1 ABS]].
    specialize no_dup_not_in_removeEntry with
        g n f1 t1 as CONTRA.
    move n at top; apply CONTRA in nd_pf as IHH; contradiction.
    assert (NoDup (n :: domain (removeEntry n g))).
    apply NoDup_cons with
        (x := n) (l := domain (removeEntry n g))
      in nd_pf1 as nd_pf2...
    apply IHTC in H1. destruct H1.
    split.
    eapply incl_app. unfold incl; intros; unfold incl in H1.
    specialize H1 with a... intuition.
    inversion H4... subst...
    eapply in_g_in_domain...
    apply in_domain_in_g in H1.
    destruct H1 as [f1 [t1 IN]]. 
    eapply in_g_in_domain...
    rewrite <-surjective_pairing...
    unfold incl. intros. inversion H3. subst. 
    apply in_g_in_domain in H... inversion H4.
    apply typeCheck_vis with (n := n) (t := t) in TC...
    apply no_dup_iff.
    split...
    split.
    rewrite <-surjective_pairing.
    eauto.
    apply disjoint_cons_r.
    split.
    apply disjoint_car; apply disjoint_2_comm; apply  dis_nil.
    rewrite <-surjective_pairing...
    all:eauto.
  - apply no_dup_split_no_dup_l with
        g1 g2 g pf1 pf2 pf
      in nd_pf as nd_pf1.
    apply no_dup_split_no_dup_r with
        g1 g2 g pf1 pf2 pf
      in nd_pf as nd_pf2.
    apply IHTC1 in nd_pf1 as K1.
    apply IHTC2 in nd_pf2 as K2.
    clear IHTC1 IHTC2.
    unfold secLabs; fold secLabs.
    split.
    intuition.
    eapply incl_app... unfold incl.
    intros.
    apply split_domain_r with (pf1 := pf1) (pf2 := pf2) (pf := pf)...
    unfold incl; intros;
    apply split_domain_l with (pf1 := pf1) (pf2 := pf2) (pf := pf)...
    apply no_dup_iff... intuition.

    apply Peirce; intros DIS.
    apply not_disjoint in DIS.
    destruct DIS as [n [IN2 IN1]].
    specialize typeCheck_hid with
        (n := n) (g := g1) (pf := pf1) (p := p1) as TYP1.
    specialize typeCheck_hid with
        (n := n) (g := g2) (pf := pf2) (p := p2) as TYP2.
    intuition.
    destruct H6 as [t2 TYP2].
    destruct H5 as [t1 TYP1].
    destruct n.
    apply finv_hid_r with
        (g1 := g1) (g := g)
        (pf1 := pf1) (pf2 := pf2) (pf := pf) in TYP2.
    inversion TYP2; subst.
    apply flag_of_map with
        g1 (n, n0) hid ill in pf1 as ABS.
    inversion ABS.
    all:eauto.
  - unfold secLabs; fold secLabs.
    unfold domain in IHTC; fold domain in IHTC.
    apply no_dup_removeEntry_no_dup with
        g u
      in nd_pf as nd_pf1.
    remember  (removeEntry u g) as g1.
    apply no_dup_removeEntry_no_dup with
        g1 v
      in nd_pf1 as nd_pf2.
    remember  (removeEntry v g1) as g2.
    specialize no_dup_not_in_removeEntry with
        (g := g1) as ND.
    assert (K : NoDup (u :: v :: domain g2)).
    apply no_dup_iff with (l1 := u :: v :: nil).
    split.
    assert (u <> v);
      unfold nonRec_typable in NT;
      fold nonRec_typable in NT;
      rewrite  <-surjective_pairing in NT;
      rewrite  <-surjective_pairing in NT;
      destruct NT as [NT1 NT2]. assumption.
    apply no_dup_iff with (l1 := u :: nil).
    split...
    split. eauto.
    apply disjoint_cons_l  with (a := u); intuition.
    inversion H4; intuition.
    split.
    assumption.
    apply disjoint_cons_l with (a := u).
    split.
    apply disjoint_cons_l with (a := v).
    split. apply disjoint_car...
    unfold not; intros ABS.
    apply in_domain_in_g in ABS.
    destruct ABS as [f3 [t3 IN]].
    specialize ND with v f3 t3; intuition.
    subst g2; eauto.
    unfold not; intros ABS.
    apply in_domain_in_g in ABS.
    destruct ABS as [f3 [t3 IN]].
    subst g1 g2.
    apply in_removeEntry in IN.
    specialize no_dup_not_in_removeEntry with
        g u f3 t3 as ND2.
    intuition.
    apply IHTC in K; clear IHTC.
    intuition.    
    unfold incl; intros.
    unfold incl in H3.
    specialize H3 with a.
    intuition.
    inversion H6. subst.
    eapply in_g_in_domain...
    inversion H3. subst.
    eapply in_g_in_domain...
    subst.
    apply in_domain_in_g in H7.
    destruct H7 as [f1 [t3 IN1]].
    apply in_removeEntry in IN1.
    apply in_removeEntry in IN1.
    apply in_g_in_domain in IN1...
    eauto.
  - unfold secLabs; fold secLabs.
    assert ( NoDup (domain ((v, vis, t2) :: removeEntry v g))).
    apply no_dup_cons_removeEntry...
    apply IHTC in H3. destruct H3. clear IHTC.
    split...
    unfold incl; intros...
    unfold incl in H3; specialize H3 with a.
    apply H3 in H5 as K3.
    unfold domain in K3; fold domain in K3.
    inversion K3. subst a.
    assert (~In v (secLabs q)).
    eapply typeCheck_vis...
    contradiction.
    apply in_domain_in_g in H6. destruct H6 as [f1 [t1 IN]].
    apply in_removeEntry in IN... apply in_g_in_domain in IN...
    
    assert (u <> v);
      unfold nonRec_typable in NT;
      fold nonRec_typable in NT;
      rewrite  <-surjective_pairing in NT;
      rewrite  <-surjective_pairing in NT;
      destruct NT as [NT1 NT2]. assumption. assumption.
  - assert (K: NoDup (domain ((u, vis, t1) :: (x, vis, t) :: removeEntry u g))).
    apply no_dup_cons_removeEntry_app_1...
    unfold not; intros; subst.
    apply in_g_in_domain in H0; contradiction.
    apply IHTC in K. clear IHTC.
    unfold secLabs; fold secLabs.
    intuition.
    unfold incl; intros.

    unfold incl in H3; specialize H3 with a.
    apply H3 in H5 as K3.
    unfold domain in K3; fold domain in K3.
    inversion K3. subst a.
    assert (~In u (secLabs q)).
    eapply typeCheck_vis...
    contradiction.
    inversion H6. subst a.
    assert (~In x (secLabs q)).
    eapply typeCheck_vis...
    contradiction.
    apply in_domain_in_g in H7. destruct H7 as [f1 [t2 IN]].
    apply in_removeEntry in IN... apply in_g_in_domain in IN...
    
    unfold nonRec_typable in NT;
      fold nonRec_typable in NT;
      rewrite  <-surjective_pairing in NT;
      rewrite  <-surjective_pairing in NT;
      destruct NT as [NT1 NT2]. assumption.
  - assert (K: NoDup (domain ((x, vis, t) :: g))).
    unfold domain; fold domain; apply NoDup_cons_iff...
    apply IHTC in K... clear IHTC.
    unfold secLabs; fold secLabs.
    unfold domain in K; fold domain in K.
    destruct K.
    split. unfold incl; unfold incl in H3; intros.
    specialize H3 with a. apply H3 in H5 as K4.
    inversion K4. subst a. 
    assert (~In x (secLabs q)).
    eapply typeCheck_vis...
    contradiction.
    all:assumption.
  - assert (K: NoDup (domain ((x, vis, t) :: g))).
    unfold domain; fold domain; apply NoDup_cons_iff...
    apply IHTC in K... clear IHTC.
    unfold secLabs; fold secLabs.
    unfold domain in K; fold domain in K.
    destruct K.
    split. unfold incl; unfold incl in H4; intros.
    specialize H4 with a. apply H4 in H6 as K4.
    inversion K4. subst a. 
    assert (~In x (secLabs q)).
    eapply typeCheck_vis...
    contradiction.
    all:assumption.
Qed.


 Lemma cons2_rewrite_pf: forall g pf1 pf2,
      cons g pf1 -> cons g pf2.
  Proof with eauto.
    intros g pf1 pf2 CO.
    dependent induction CO.
    subst. apply Co_nil...
    eapply Co_top...
    eapply Co_un...
    eapply Co_lin...
  Qed.

  
#[global] Hint Resolve cons2_rewrite_pf.



  #[global] Hint Resolve split_rewrite_pf.
    
Lemma typeCheck_rewrite_pf : forall g p pf1 pf2,
    typeCheck g pf1 p -> typeCheck g pf2 p.
Proof with eauto.
   intros.
   intuition.
   remember H as TC. subst H.
   dependent induction TC.
   apply TNil...
   eapply TNew...
   eapply TPar...
   eapply TOutL...
   eapply TOutUn...
   eapply TInL...
   eapply TInUn...
   eapply TInU...
Qed.


 #[global] Hint Resolve typeCheck_rewrite_pf
   in_g_in_domain.

 

   Lemma typeCheck_hid_proj g p pf (nd_pf : NoDup (domain g)):
    typeCheck g pf p ->
    incl (secLabs p) (domain (hid_proj g)).
  Proof with eauto using typeCheck_no_dup, typeCheck_hid,in_hid_proj.
    intros TC;
      eapply typeCheck_no_dup with (p:= p) in nd_pf as (INCL &_); unfold incl in *; intros;
        try specialize INCL with a;
        intuition...
    eapply typeCheck_hid with (n := a) in TC as (t &TC)...
  Qed.

 
      
      
    
  Lemma typeCheck_hid_proj_par g p pf q (nd_pf : NoDup (domain g)):
    typeCheck g pf (dPar p q)->
    incl (secLabs p) (domain (hid_proj g)).
  Proof with eauto using
             typeCheck_no_dup,
             typeCheck_hid,
             typeCheck_hid_proj,
             split_hid_proj.
    intros TC; inverts TC.
    eapply typeCheck_hid_proj in H2;
      unfold incl in *; intros;
        try specialize H2 with a; intuition;
          try eapply no_dup_split_no_dup_l...
  Qed.



