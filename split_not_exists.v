Require Import
        Bool List Lia PeanoNat Program.Equality
        ListAddOns Max RemoveEntry Domain
        header
        operations pi_syntax 
        pairEq type_system semantics
        type_operations_1
        split_exists_neutral
        sub_split
        no_dup_split_no_dup
	split_existential
        split_cons_remove
        disjoint_newEntries
        sne_premises
        split_operations_2
        Permutation.

Require Import CpdtTactics LibTactics.
Import ListNotations.

#[global] Hint Resolve no_dup_split_no_dup_r no_dup_split_no_dup_l.

#[global] Hint Resolve beq_nat_refl.


      #[global] Hint Constructors flag_plus.



Lemma split_type_plus : forall g1 g2 g pf1 pf2 pf a t1 t,
    typeOf g1 a t1 ->
    typeOf g a t ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    exists t2,
      typeOf g2 a t2 /\
      type_plus t1 t2 t.
Proof with eauto.
    intros  g1 g2 g pf1 pf2 pf a t1 t TYP1 TYP TS.
    dependent induction TS.
    - subst. inversion TYP1. inversion H.
    - destruct a as [a1 a2]; destruct n as [n1 n2].
      case_eq (pair_eq (n1, n2) (a1, a2)). intros PEQ. 
      rewrite <-pairEq_eq in PEQ; inversion PEQ; subst.
      exists  (Chan lin q t0).
      split...
      inversion TYP1; inversion TYP; inversion H5; subst.
      assert (f = f0 /\ Chan lin p t0 = t1).
      apply in_isMap with (x := (a1, a2)) (g := g1)...
      assert (f1 = f2 /\ t =  Chan lin p' t0).
      apply in_isMap with (x := (a1, a2)) (g := g3)...
      destruct H6; destruct H7; subst.
      apply Tp_LinPlus...
      intros PNEQ. assert (PNEQ2 := PNEQ).
      rewrite <-pairEq_neq in PNEQ.
      inversion TYP1. subst.
      assert ( In (a1, a2, f0, t1)  (removeEntry (n1, n2) g1)).
      apply removeEntry_in...
      apply T_Entry in H3 as IHH.
      apply IHTS in IHH.
      destruct IHH as [t2 [TYP2 TP]].
      exists t2.
      split. inversion TYP2.  subst. apply in_removeEntry in H7...
      eauto.
      inversion TYP; subst. apply removeEntry_in with (y := (n1, n2)) in H7...
    - destruct a as [a1 a2]; destruct n as [n1 n2].
      case_eq (pair_eq (n1, n2) (a1, a2)). intros PEQ. 
      rewrite <-pairEq_eq in PEQ; inversion PEQ; subst.
      exists  (Chan un p t0).
      split...
      inversion TYP1; inversion TYP; inversion H4; subst.
      assert (f = f0 /\ Chan un p t0 = t1).
      apply in_isMap with (x := (a1, a2)) (g := g1)...
      assert (f1 = f2 /\ t =  Chan un p t0).
      apply in_isMap with (x := (a1, a2)) (g := g3)...
      destruct H5; destruct H6; subst.
      assert (POLEQ : pol_cup p p = p)...
      rewrite <-POLEQ at 3.
      apply Tp_UnPlus...
      intros PNEQ. assert (PNEQ2 := PNEQ).
      rewrite <-pairEq_neq in PNEQ.
      inversion TYP1. subst.
      assert ( In (a1, a2, f0, t1)  (removeEntry (n1, n2) g1)).
      apply removeEntry_in...
      apply T_Entry in H2 as IHH.
      apply IHTS in IHH.
      destruct IHH as [t2 [TYP2 TP]].
      exists t2.
      split. inversion TYP2.  subst. apply in_removeEntry in H6...
      eauto.
      inversion TYP; subst. apply removeEntry_in with (y := (n1, n2)) in H6...
      - destruct a as [a1 a2]; destruct n as [n1 n2].
      case_eq (pair_eq (n1, n2) (a1, a2)). intros PEQ. 
      rewrite <-pairEq_eq in PEQ; inversion PEQ; subst.
      exists  Top.
      split...
      inversion TYP1; inversion TYP; inversion H4; subst.
      assert (f = f0 /\ Top = t1).
      apply in_isMap with (x := (a1, a2)) (g := g1)...
      assert (f1 = f2 /\ t =  Top).
      apply in_isMap with (x := (a1, a2)) (g := g3)...
      destruct H5; destruct H6; subst.
      apply Tp_Base...
      intros PNEQ. assert (PNEQ2 := PNEQ).
      rewrite <-pairEq_neq in PNEQ.
      inversion TYP1. subst.
      assert ( In (a1, a2, f0, t1)  (removeEntry (n1, n2) g1)).
      apply removeEntry_in...
      apply T_Entry in H2 as IHH.
      apply IHTS in IHH.
      destruct IHH as [t2 [TYP2 TP]].
      exists t2.
      split. inversion TYP2.  subst. apply in_removeEntry in H6...
      eauto.
      inversion TYP; subst. apply removeEntry_in with (y := (n1, n2)) in H6...
Qed.

Lemma in_hid_proj: forall a t g,
    In (a, hid, t) g -> In (a, hid, t) (hid_proj g).
Proof with eauto.
  introv IN; induction g;
    inv IN; destruct a; simpl; intuition;
      try destruct b0; try right...
Qed.

 Lemma in_hid_proj_2 a f t g1 :
    NoDup (domain g1) ->    
    In (a, f, t) g1 ->
    In a (domain (hid_proj g1)) ->
    f = hid.
  Proof with eauto using hid_proj_flagOf.
    intros pf IN INH.
    destruct a as [a1 a2].
    assert (FYP: flagOf g1 (a1, a2) hid).
    eapply hid_proj_flagOf...
    inverts FYP.
    eapply no_dup_isMap in pf;
      eapply flag_of_map with (x := (a1, a2))...
  Qed.

   Lemma split_hid_proj a g1 g2 g pf1 pf2 pf (nd_pf: NoDup (domain g1)) :
    tEnv_split g1 g2 g pf1 pf2 pf ->
    In a (domain (hid_proj g1)) ->
    In a (domain (hid_proj g)).
  Proof with eauto using in_g_in_domain,in_hid_proj.
    intros TS IN;
      assert (IN2 := IN);
      eapply in_domain_in_g in IN as (f &t &IN); eapply incl_hid_proj in IN.
    assert (f = hid).
    eapply in_hid_proj_2...
    subst.
    destruct a; eapply fsub_hid in IN...
    try inverts IN...
Qed.      

Lemma split_incl_hid_proj : forall g1 g2 g pf1 pf2 pf (nd_pf : NoDup (domain g1)),
    tEnv_split g1 g2 g pf1 pf2 pf ->
    incl (domain (hid_proj g1))
      (domain (hid_proj g)).
Proof with eauto.
  introv nd_pf TS IN;
    eapply split_hid_proj...
Qed.
  
 Lemma type_remove_entry m p t:
   type_remove (Chan m p t) (Chan m empty t) (Chan m p t).
 Proof with eauto.
   intros; unfold type_remove; intuition; destruct m, p; simpl; try econstructor...
 Qed.

 Lemma not_lin_is_unrestricted:  forall p t,
     is_unrestricted (Chan lin p t) -> False.
 Proof with eauto.
   unfold is_unrestricted; intros. destruct H as [pp [tt ABS]]; inversion ABS.
 Qed.

 
#[global] Hint Constructors type_sub.
#[global] Hint Constructors type_plus.
Lemma type_remove_super: forall s s1 s2 t t2,
  type_remove s t t2  ->
  type_plus s1 s s2 ->
  exists t2,  type_remove s2 t t2.
Proof with eauto.
  intros;
  destruct s; try destruct m, p;
    try eapply type_remove_lin in H;
    intuition;
    try inversion H0;
    try inversion H6;
    subst;
     try match goal with
         | [ _ : _ |- exists _, type_remove ?t (Chan _ empty _) _ ] =>
           exists t;
              unfold type_remove; intuition
         | [ _ : _ |- exists _, type_remove (Chan lin ?p ?t) (Chan lin ?p ?t) _ ] =>
           exists (Chan lin empty t);
              unfold type_remove; intuition
         | [ _ : _ |- exists _, type_remove (Chan lin inp ?t) _ _ ] =>
           exists (Chan lin out t);
             unfold type_remove; intuition
         | [ _ : _ |- exists _, type_remove _ (Chan lin inp ?t) _] =>
           exists (Chan lin out t);
             unfold type_remove; intuition
         | [ _ : _ |- exists _, type_remove _ (Chan lin out ?t) _] =>
           exists (Chan lin inp t);
             unfold type_remove; intuition
         | [ TR : type_remove (Chan un ?p _) _ _ |- exists _, type_remove ?t1 _ _ ] =>
           exists t1;
             try eapply type_remove_un in TR;
             try eapply type_remove_entry;
             unfold type_remove;
             intuition; subst;
               try destruct p, p1; simpl;
                 econstructor
         | [ TR : type_remove Top _ _ |- exists _, type_remove ?t1 ?t _ ] =>
           exists Top;
             try eapply type_remove_top in TR;
             intuition; subst
        end;
    
  try match goal with
         | [ ABS :  is_unrestricted (Chan lin _ _) |- _ ] =>
           try eapply not_lin_is_unrestricted in ABS;
             try contradiction end;
  match goal with
  | [ TR : type_remove (Chan un ?p _) _ _ |-
    exists _, type_remove ?t1 _ _] =>
    exists t1;
      try eapply type_remove_un in TR;
      try eapply type_remove_entry;
      unfold type_remove;
      intuition; subst;
        try destruct p1; simpl; econstructor
  | _ => repeat econstructor
  end.
Qed.

(*Lemma split_exists_out  a1 a2 t b1 b2 s s1 g1 p2 pf0 g0 g2 g2 pf1 pf2 pf:
  lts ((a1, a2, vis, Chan lin out t) :: (b1, b2, vis, s) :: g1) p1 (aOut a1 a2 b1 b2)
           ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, s1) :: g1) p2 pf0 ->
  tEnv_split g0 g2 g pf1 pf2 pf ->
  In (b1, b2, vis, s) g0 ->
  In (a1, a2, vis, Chan lin io t) g ->
  typeOf g2 (b1, b2) t2 ->
  type_plus t2 s r ->
  type_remove r t s2 ->
 *)

(* USED WHERE??? 
Lemma split_exists_tau g1 g2 g pf1 pf2 pf k1 nd_pf1 nd_pf p p1 a1 a2:
  tEnv_split g1 g2 g pf1 pf2 pf ->
  lts g1 p (aTau a1 a2) k1 p1 nd_pf1 ->
  exists k,
    lts g p (aTau a1 a2) k p1 nd_pf.
Proof with eauto.
  introv TS LTS.
  dependent induction LTS;
    try eapply IHLTS in TS as (k&TS)...
  - econstructor;eapply parL...
  - clear IHLTS1 IHLTS2.
    eapply tsub_io with (pf := pf) in H0 as K...
    assert (INb := H1).
    assert (TYP: typeOf g0 (b1, b2) s)...
    eapply split_domain_l with (x := (b1, b2))
      in TS as IFF;
      eapply in_g_in_domain,IFF,in_domain_in_g in H1;
      destruct H1 as (ff &r &IN).
    eapply fsub_vis with (a1 := b1) ( a2 := b2) in TS as FYP...
    assert (ff = vis)...
    eapply fsub_vis with (a1 := a1) ( a2 := a2) in TS as FYP2...
    inv K.
    assert (f = vis)...
    subst.
    eapply split_type_plus with (pf2 := pf2) (pf := pf) (t := r) in TYP as (t2 &TYP &TP)...
    eapply type_plus_comm in TP;
      eapply type_remove_super in H as (s2 &TREM)...
    econstructor; eapply lcomL with (b1 := b1)(b2 := b2) (s :=r) (t := t)...
*)

Lemma split_rewrite_pf: forall g1 g2 g pf1 pf2 pf pf',
    tEnv_split g1 g2 g pf1 pf2 pf ->
    tEnv_split g1 g2 g pf1 pf2 pf'.
  Proof with eauto.
    intros g1 g2 g pf1 pf2 pf pf' TS. 
    dependent induction TS.
    subst; apply SpNil...
    assert (pfk :  isMap (removeEntry n g3)).
    apply isMap_removeEntry...
    apply SpLin with
        n f f' g p q p' t (removeEntry n g3)  pf'0 pf'' pfk.
    all:eauto.
    subst g'''; specialize IHTS with pfk...
     assert (pfk :  isMap (removeEntry n g3)).
    apply isMap_removeEntry...
    apply SpUn with
        n f f' g p t (removeEntry n g3)  pf'0 pf'' pfk.
    all:eauto.
    subst g'''; specialize IHTS with pfk...
     assert (pfk :  isMap (removeEntry n g3)).
    apply isMap_removeEntry...
    apply SpTop with
        n f f' g (removeEntry n g3)  pf'0 pf'' pfk.
    all:eauto.
    subst g'''; specialize IHTS with pfk...
  Qed.

  #[global] Hint Resolve split_rewrite_pf.

 #[global] Hint Resolve removeEntry_iff_cons.
(*      fimpl_removeEntry_l
      fimpl_removeEntry_r.
 *)

 Lemma split_removeEntry_domain :
  forall b1 b2 f1 s1 f2 s2 g1 g2 g pf1 pf2 pf x
         (nd_pf : NoDup (domain g)),
    tEnv_split g1 g2 g pf1 pf2 pf ->
      In x (domain ((b1, b2, f1, s1) :: removeEntry (b1, b2) g)) <->
      In x (domain ((b1, b2, f2, s2) :: removeEntry (b1, b2) g1)).
  Proof with eauto.
    intros b1 b2 f1 s1 f2 s2 g1 g2 g pf1 pf2 pf x nd_pf TS.
    intuition.
    unfold domain in H; fold domain in H.
    unfold domain; fold domain.
    apply in_app_iff with (l := (b1, b2)::nil) in H.
    destruct H.
    inversion H. inversion H0; subst...
    inversion H0.
    assert (pf1' : isMap (removeEntry (b1, b2) g1)).
    apply isMap_removeEntry...
    assert (pf2' : isMap (removeEntry (b1, b2) g2)).
    apply isMap_removeEntry...
    assert (pf' : isMap (removeEntry (b1, b2) g)).
    apply isMap_removeEntry...
    assert (TS' :
              tEnv_split (removeEntry (b1, b2) g1)
                         (removeEntry (b1, b2) g2)
                         (removeEntry (b1, b2) g)
                         pf1' pf2' pf').
    apply split_remove with (pf1 := pf1) (pf2 := pf2) (pf3 := pf)...
    specialize split_domain_l with   (removeEntry (b1, b2) g1) (removeEntry (b1, b2) g2)
          (removeEntry (b1, b2) g) pf1' pf2' pf' (a, b) as SPD.
    intuition.

     intuition.
    unfold domain in H; fold domain in H.
    unfold domain; fold domain.
    apply in_app_iff with (l := (b1, b2)::nil) in H.
    destruct H.
    inversion H. subst. 
    inversion H0...
    inversion H0.
    assert (pf1' : isMap (removeEntry (b1, b2) g1)).
    apply isMap_removeEntry...
    assert (pf2' : isMap (removeEntry (b1, b2) g2)).
    apply isMap_removeEntry...
    assert (pf' : isMap (removeEntry (b1, b2) g)).
    apply isMap_removeEntry...
    assert (TS' :
              tEnv_split (removeEntry (b1, b2) g1)
                         (removeEntry (b1, b2) g2)
                         (removeEntry (b1, b2) g)
                         pf1' pf2' pf').
    apply split_remove with (pf1 := pf1) (pf2 := pf2) (pf3 := pf)...
    specialize split_domain_l with   (removeEntry (b1, b2) g1) (removeEntry (b1, b2) g2)
          (removeEntry (b1, b2) g) pf1' pf2' pf' (a, b) as SPD.
    intuition.
  Qed.


Lemma payload_occurs  g1 p1 a1 a2 b1 b2 g2 p2 pf:
lts g1 p1 (aOut a1 a2 b1 b2) g2 p2 pf ->
In (b1, b2) (fn p1) \/ In (b1, b2) (secLabs p1).
Proof with eauto.
  introv LTS.
  dependent induction LTS; simpl;
    assert (IH:  aOut a1 a2 b1 b2 = aOut a1 a2 b1 b2) by eauto; try eapply IHLTS in IH; intuition...
  left; destruct H as [DIFF1 DIFF2]; eapply in_in_remove...
Qed.

          
Lemma split_not_exists_lts :
  forall g1 g2 g k1 p a  p' pf1 pf2 pf nd_pf1 (nd_pf2 : NoDup (domain g2)) nd_pf,
    tEnv_split g1 g2 g pf1 pf2 pf ->
    lts g1 p a k1 p' nd_pf1 ->
     NoDup (secLabs p) ->
     incl (secLabs p) (domain (hid_proj g1)) ->
    (*(forall x f1 f2,
        flagOf g1 x f2 ->
        flagOf g x f1 ->
        f2 <> f1 ->
        f2 = hid /\ f1 = ill /\ ~In x (secLabs p)) ->*)
     wf p -> 
     sl_pos p ->
     max (secLabs p) <= max (domain g1) ->
    (~ exists g', lts g p a g' p' nd_pf) ->
    exists x1 x2 y1 y2 t,
      (a = aIn x1 x2 y1 y2 /\
       typeOf g1 (x1, x2) (Chan lin inp t) /\
       typeOf g (x1, x2) (Chan lin io t)) \/
      ((a = aIn x1 x2 y1 y2 /\
        exists m p ty,
          typeOf g1 (x1, x2) (Chan m p t) /\
          typeOf g (y1, y2) ty /\
          ~exists t1, type_plus t ty t1)) \/
      ((a = aIn x1 x2 y1 y2 /\
        flagOf g1 (y1, y2) ill /\
        flagOf g (y1, y2) hid))   \/
      (a = aOut x1 x2 y1 y2 /\
       typeOf g1 (x1, x2) (Chan lin out t) /\
       typeOf g (x1, x2) (Chan lin io t)).
Proof with eauto.
  intros
    g1 g2 g k1 p a p' pf1 pf2 pf nd_pf1 nd_pf2 nd_pf
    TSPLIT LTS NDSL INCL WF SLP MAX.
  generalize dependent g.
  generalize dependent g2.
  dependent induction LTS.
  intros g2 pf2 nd_pf2 g0 pf0 nd_pf0 TSPLIT  NLTS.
  - Case parL.
    eapply sl_pos_par_l in SLP;
      eapply max_sl_par in MAX as (MAX &_).
    apply IHLTS with
        pf1 g2 pf2 g0 pf0 nd_pf0 in TSPLIT; try assumption.
    (*simpl in FIMPL; intros [x1 x2] f1 f2; introv FYP2 FYP1 DIFF;
      specialize FIMPL with (x1, x2) f1 f2; intuition.*)
     simpl in NDSL;
      try eapply no_dup_distr in NDSL;
      intuition.
    simpl in INCL;
      eapply incl_app_inv in INCL;
      intuition.
    eapply wf_par in WF; intuition.
    unfold not; intros ABSURD. destruct ABSURD as [g0' ABSURD].
    elim NLTS. exists g0'.
    apply parL with (q := q) in ABSURD.
    assumption.
  - Case lOut.
    intros g2 pf2 nd_pf2 g0 pf0 nd_pf0 TSPLIT NLTS.
    assert (TIN := H0).
    assert (TINb := H1).
    remember pf as nd_pf. subst pf.
    remember pf1 as pf. subst pf1.
    exists a1. exists a2. exists b1. exists b2. exists t.
    right. right. right. split. tauto. split.
    apply T_Entry with (f := vis). assumption.
    specialize tsub_out with
        g g2 g0 pf pf2 pf0 a1 a2 vis lin t as TYP.
    apply TYP in H0.
    + specialize split_exists_remove_l with
          g g2 g0 pf pf2 pf0 b1 b2 vis t t1 t2 as TYP2.
      apply TYP2 in H1.
      * destruct H1 as [t1' [t2' [TYP_b TREM]]].
        destruct H0 as [POUT | PIO].
        ** inversion POUT; subst; auto.
           apply lOut with
               g0 p a1 a2 b1 b2 nd_pf0 t t1' t2' in TREM
             as LTS.
           remember  ((a1, a2, vis, Chan lin empty t)
                        :: (b1, b2, vis, t2') :: removeEntry (a1, a2) (removeEntry (b1, b2) g0)) as g0'.
           elim NLTS.
           exists g0'.
           assumption.
           apply fsub_vis with
               g g2 g0 pf pf2 pf0 a1 a2 (Chan lin out t)
             in TIN as FIN.
           inversion FIN; subst; auto...
           assert (TVIS := pf0). 
           apply flag_of_map with
               g0 (a1, a2) f vis
             in TVIS.
           subst; assumption.
           apply F_Entry in H0; assumption.
           apply F_Entry in H0; assumption.
           assumption.
           inversion TYP_b; subst; auto...
           apply fsub_vis with
               g g2 g0 pf pf2 pf0 b1 b2 t1
             in TINb as FIN.
           inversion FIN; subst; auto...
           assert (TVIS := pf0). 
           apply flag_of_map with
               g0 (b1, b2) f0 vis
             in TVIS.
           subst; assumption.
           apply F_Entry in H1; assumption.
           apply F_Entry in H1; assumption.
           assumption.
        ** assumption.
      * assumption.
      * assumption.
    + assumption.
  - Case uOut.
    intros g2 pf2 nd_pf2 g0 pf0 nd_pf0 TSPLIT NLTS.
    assert (TIN := H1).
    elim NLTS.
    remember ((b1, b2, vis, t2) :: removeEntry (b1, b2) g0) as g'.
    exists g'.
    specialize split_exists_remove_l with
        g g2 g0 pf1 pf2 pf0 b1 b2 vis t t1 t2 as TYP2.
    apply TYP2 in H2 as TYP_b.
    destruct TYP_b as [t1' [t2' [TYP_b TREM]]].
    apply uOut with
        g0 pol p a1 a2 b1 b2 nd_pf0 t t1' t2'
      in H.
    clear TYP2.
    remember ((b1, b2, vis, t2') :: removeEntry (b1, b2) g0) as g0'.
    elim NLTS.
    exists g0'.
    assumption.
    assumption.
    apply tsub_un
      with g g2 g0 pf1 pf2 pf0 a1 a2 vis pol t
      in H1.
    inversion H1; subst; auto...
    apply fsub_vis
      with g g2 g0 pf1 pf2 pf0 a1 a2 (Chan un pol t)
      in TIN.
    inversion TIN.
    assert (FIN := pf0).
    apply flag_of_map with
        g0 (a1, a2) f vis
      in FIN; subst; auto...
    apply F_Entry in H3; assumption.
    assumption.
    inversion TYP_b; subst; auto...
    apply fsub_vis with
        g g2 g0 pf1 pf2 pf0 b1 b2 t1
      in H2.
    inversion H2; subst; auto...
    assert (TVIS := pf0). 
    apply flag_of_map with
        g0 (b1, b2) f vis
      in TVIS.
    subst; assumption.
    apply F_Entry in H3; assumption.
    apply F_Entry in H4; assumption.
    all:assumption.
  - Case lIn.
    intros g2 pf2 nd_pf2 g0 pf0 nd_pf0 TSPLIT NLTS.
    remember pf as nd_pf. subst pf.
    remember pf1 as pf. subst pf1.
    exists a1. exists a2. exists b1. exists b2. exists t.
    specialize tsub_in with
        g g2 g0 pf pf2 pf0 a1 a2 vis lin t as TYP.
    specialize fsub_vis with
        g g2 g0 pf pf2 pf0 a1 a2 (Chan lin inp t) as FYP.
    intuition.
    inversion H3; inversion H5; subst.
    apply flag_of_map with
        g0 (a1, a2) f0 vis in pf0 as FYP; subst...
    destruct t1. 
    + apply tsub_payload with
          g g2 g0 pf pf2 pf0 b1 b2 f m p0 t1
        in H2 as TYPb.
      destruct TYPb as [p1 TYPb]; inversion TYPb; subst.
      

      inversion H; subst.
      right.
      *destruct f0.
       ** destruct f. contradiction. 
          right. left. eauto.
          assert (hid = vis).
          assert (K2 := H2).
          apply fsub_vis with
              g g2 g0 pf pf2 pf0 b1 b2 (Chan lin p0 t1)
            in K2...
          inversion H7.
       ** left. split. tauto.
          exists lin. exists inp. exists (Chan lin p1 t1).
          split. eauto.
          split. eauto.
          intros ABS. destruct ABS as [t2 ABS].
          elim NLTS.
          remember (Chan lin p3 t1) as T.
          remember (Chan lin p1 t1) as Tb.
          apply type_plus_comm in ABS.
          exists ((((a1, a2), vis, Chan lin empty T )
                     :: ((b1, b2), vis, t2)
                     :: (removeEntry (a1, a2)
                                     (removeEntry (b1, b2) g0)))).
          apply lIn with
              g0 p a1 a2 x1 x2 b1 b2 nd_pf0 ill
              T Tb t2
            in ABS; eauto.
          discriminate.
       ** left. split. tauto.
          exists lin. exists inp. exists (Chan lin p1 t1).
          split. eauto.
          split. eauto.
          intros ABS. destruct ABS as [t2 ABS].
          elim NLTS.
          remember (Chan lin p3 t1) as T.
          remember (Chan lin p1 t1) as Tb.
          apply type_plus_comm in ABS.
          exists ((((a1, a2), vis, Chan lin empty T )
                     :: ((b1, b2), vis, t2)
                     :: (removeEntry (a1, a2)
                                     (removeEntry (b1, b2) g0)))).
          apply lIn with
              g0 p a1 a2 x1 x2 b1 b2 nd_pf0 vis
              T Tb t2
            in ABS; eauto.
          discriminate.
      * destruct f0.
        ** destruct f. contradiction. 
           right. right. left. eauto.
           assert (hid = vis).
           assert (K2 := H2).
           apply fsub_vis with
               g g2 g0 pf pf2 pf0 b1 b2 (Chan un p0 t1)
             in K2...
           inversion H7.
        **
          right. left. split. tauto.
          exists lin. exists inp. exists (Chan un p1 t1).
          split. eauto.
          split. eauto.
          intros ABS. destruct ABS as [t2 ABS].
          elim NLTS.
          remember (Chan un p3 t1) as T.
          remember (Chan un p1 t1) as Tb.
          apply type_plus_comm in ABS.
          exists ((((a1, a2), vis, Chan lin empty T )
                     :: ((b1, b2), vis, t2)
                     :: (removeEntry (a1, a2)
                                     (removeEntry (b1, b2) g0)))).
          apply lIn with
              g0 p a1 a2 x1 x2 b1 b2 nd_pf0 ill
              T Tb t2
            in ABS; eauto.
          discriminate.
        **  right. left. split. tauto.
            exists lin. exists inp. exists (Chan un p1 t1).
            split. eauto.
            split. eauto.
            intros ABS. destruct ABS as [t2 ABS].
            elim NLTS.
            remember (Chan un p3 t1) as T.
            remember (Chan un p1 t1) as Tb.
            apply type_plus_comm in ABS.
            exists ((((a1, a2), vis, Chan lin empty T )
                       :: ((b1, b2), vis, t2)
                       :: (removeEntry (a1, a2)
                                       (removeEntry (b1, b2) g0)))).
            apply lIn with
                g0 p a1 a2 x1 x2 b1 b2 nd_pf0 vis
                T Tb t2
              in ABS; eauto.
            discriminate.
      * eauto.
    +    apply tsub_top with
             g g2 g0 pf pf2 pf0 b1 b2 f 
        in H2 as TYPb.
         inversion TYPb; subst.
         inversion H; subst.
         right.
         *destruct f0.
          ** destruct f. contradiction. 
             right. left. eauto.
             assert (hid = vis).
             assert (K2 := H2).
             apply fsub_vis with
                 g g2 g0 pf pf2 pf0 b1 b2 Top
               in K2...
             inversion H7.
          ** left. split. tauto.
             exists lin. exists inp. exists Top.
             split. eauto.
             split. eauto.
             intros ABS. destruct ABS as [t2 ABS]. inversion ABS; subst.
             elim NLTS.
             exists ((((a1, a2), vis, Chan lin empty Top )
                        :: ((b1, b2), vis, Top)
                        :: (removeEntry (a1, a2)
                                        (removeEntry (b1, b2) g0)))).
             apply lIn with
                 g0 p a1 a2 x1 x2 b1 b2 nd_pf0 ill
                 Top Top Top in ABS;  eauto.
             discriminate.
          ** left. split. tauto.
             exists lin. exists inp. exists Top.
             split. eauto.
             split. eauto.
             intros ABS. destruct ABS as [t2 ABS].
             inversion ABS; subst.
             elim NLTS.
             apply type_plus_comm in ABS.
             exists ((((a1, a2), vis, Chan lin empty Top )
                        :: ((b1, b2), vis, Top)
                        :: (removeEntry (a1, a2)
                                        (removeEntry (b1, b2) g0)))).
             apply lIn with
                 g0 p a1 a2 x1 x2 b1 b2 nd_pf0 vis
                 Top Top Top
               in ABS; eauto.
             discriminate.
         * eauto.
    + left. split. eauto.
      eauto.
  - Case uIn.
    intros g2 pf2 nd_pf2 g0 pf0 nd_pf0 TSPLIT NLTS.
    remember pf as nd_pf. subst pf.
    remember pf1 as pf. subst pf1.
    exists a1. exists a2. exists b1. exists b2. exists t.
    specialize tsub_un with
        g g2 g0 pf pf2 pf0 a1 a2 vis pol t as TYP.
    specialize fsub_vis with
        g g2 g0 pf pf2 pf0 a1 a2 (Chan un pol t) as FYP.
    intuition.
    + inversion H; inversion H6; subst.
      apply flag_of_map with
          g0 (a1, a2) f1 vis in pf0 as FYP; subst...
      destruct t1. 
      *  apply tsub_payload with
             g g2 g0 pf pf2 pf0 b1 b2 f m p0 t1
          in H3 as TYPb.
         destruct TYPb as [p1 TYPb]; inversion TYPb; subst.
         inversion H; subst.
         right.
         ** destruct f0.
            *** destruct f. contradiction. 
                right. left. eauto.
                assert (hid = vis).
                assert (K2 := H3).
                apply fsub_vis with
                    g g2 g0 pf pf2 pf0 b1 b2 (Chan m p0 t1)
                  in K2...
                inversion H8.
            *** left. split. tauto.
                exists un. exists inp. exists (Chan m p1 t1).
                split. eauto.
                split. eauto.
                intros ABS. destruct ABS as [t2' ABS].
                elim NLTS.
                remember (Chan m p1 t1) as Tb.
                apply type_plus_comm in ABS.
                exists (((b1, b2), vis, t2')
                          :: (removeEntry (b1, b2) g0)).
                assert (ABS2: inp = inp \/ inp = io) by eauto.
                apply uIn with
                    g0 inp p a1 a2 x1 x2 b1 b2 nd_pf0 ill
                    t Tb t2'
                  in ABS2...
                discriminate...
            *** left. split. tauto.
                exists un. exists inp. exists (Chan m p1 t1).
                split. eauto.
                split. eauto.
                intros ABS. destruct ABS as [t2' ABS].
                elim NLTS.
                remember (Chan m p1 t1) as Tb.
                apply type_plus_comm in ABS.
                exists (((b1, b2), vis, t2')
                          :: (removeEntry (b1, b2) g0)).
                assert (ABS2: inp = inp \/ inp = io) by eauto.
                apply uIn with
                    g0 inp p a1 a2 x1 x2 b1 b2 nd_pf0 vis
                    t Tb t2'
                  in ABS; eauto.
                discriminate.
         ** eauto. 
      * apply tsub_top with
            g g2 g0 pf pf2 pf0 b1 b2 f 
          in H3 as TYPb.
        inversion TYPb; subst.
        inversion H; subst.
        right.
        **destruct f0.
          *** destruct f. contradiction. 
              right. left. eauto.
              assert (hid = vis).
              assert (K2 := H3).
              apply fsub_vis with
                  g g2 g0 pf pf2 pf0 b1 b2 Top
                in K2...
              inversion H8.
          *** left. split. tauto.
              exists un. exists inp. exists Top.
              split. eauto.
              split. eauto.
              intros ABS. destruct ABS as [t2' ABS]. inversion ABS; subst.
              elim NLTS.
              exists (((b1, b2), vis, Top)
                        :: (removeEntry (b1, b2) g0)).
              assert (ABS2: inp = inp \/ inp = io) by eauto.
              apply uIn with
                  g0 inp p a1 a2 x1 x2 b1 b2 nd_pf0 ill
                  Top Top Top in ABS...
              discriminate.
          *** left. split. tauto.
              exists un. exists inp. exists Top.
              split. eauto.
              split. eauto.
              intros ABS. destruct ABS as [t2' ABS].
              inversion ABS; subst.
              elim NLTS.
              exists (((b1, b2), vis, Top)
                        :: (removeEntry (b1, b2) g0)).
              assert (ABS2: inp = inp \/ inp = io) by eauto.
              apply uIn with
                  g0 inp p a1 a2 x1 x2 b1 b2 nd_pf0 vis
                  Top Top Top in ABS...
              discriminate.
        ** eauto.
    + inversion H; inversion H6; subst.
      apply flag_of_map with
          g0 (a1, a2) f1 vis in pf0 as FYP; subst...
      destruct t1. 
      * apply tsub_payload with
            g g2 g0 pf pf2 pf0 b1 b2 f m p0 t1
          in H3 as TYPb.
        destruct TYPb as [p1 TYPb]; inversion TYPb; subst.
        inversion H; subst.
        right.
        ** destruct f0.
           *** destruct f. contradiction. 
               right. left. eauto.
               assert (hid = vis).
               assert (K2 := H3).
               apply fsub_vis with
                   g g2 g0 pf pf2 pf0 b1 b2 (Chan m p0 t1)
                 in K2...
               inversion H8.
           *** left. split. tauto.
               exists un. exists io. exists (Chan m p1 t1).
               split. eauto.
               split. eauto.
               intros ABS. destruct ABS as [t2' ABS].
               elim NLTS.
               remember (Chan m p1 t1) as Tb.
               apply type_plus_comm in ABS.
               exists (((b1, b2), vis, t2')
                         :: (removeEntry (b1, b2) g0)).
               assert (ABS2: io = inp \/ io = io) by eauto.
               apply uIn with
                   g0 io p a1 a2 x1 x2 b1 b2 nd_pf0 ill
                   t Tb t2'
                 in ABS2...
               discriminate...
           *** left. split. tauto.
               exists un. exists io. exists (Chan m p1 t1).
               split. eauto.
               split. eauto.
               intros ABS. destruct ABS as [t2' ABS].
               elim NLTS.
               remember (Chan m p1 t1) as Tb.
               apply type_plus_comm in ABS.
               exists (((b1, b2), vis, t2')
                         :: (removeEntry (b1, b2) g0)).
               assert (ABS2: io = inp \/ io = io) by eauto.
               apply uIn with
                   g0 io p a1 a2 x1 x2 b1 b2 nd_pf0 vis
                   t Tb t2'
                 in ABS; eauto.
               discriminate.
        ** eauto.
      * apply tsub_top with
            g g2 g0 pf pf2 pf0 b1 b2 f 
          in H3 as TYPb.
        inversion TYPb; subst.
        inversion H; subst.
        right.
        **destruct f0.
          *** destruct f. contradiction. 
              right. left. eauto.
              assert (hid = vis).
              assert (K2 := H3).
              apply fsub_vis with
                  g g2 g0 pf pf2 pf0 b1 b2 Top
                in K2...
              inversion H8.
          *** left. split. tauto.
              exists un. exists io. exists Top.
              split. eauto.
              split. eauto.
              intros ABS. destruct ABS as [t2' ABS]. inversion ABS; subst.
              elim NLTS.
              exists (((b1, b2), vis, Top)
                        :: (removeEntry (b1, b2) g0)).
              assert (ABS2: io = inp \/ io = io) by eauto.
              apply uIn with
                  g0 io p a1 a2 x1 x2 b1 b2 nd_pf0 ill
                  Top Top Top in ABS...
              discriminate.
          *** left. split. tauto.
              exists un. exists io. exists Top.
              split. eauto.
              split. eauto.
              intros ABS. destruct ABS as [t2' ABS].
              inversion ABS; subst.
              elim NLTS.
              exists (((b1, b2), vis, Top)
                        :: (removeEntry (b1, b2) g0)).
              assert (ABS2: io = inp \/ io = io) by eauto.
              apply uIn with
                  g0 io p a1 a2 x1 x2 b1 b2 nd_pf0 vis
                  Top Top Top in ABS...
              discriminate.
        ** eauto.
  - Case uRin.
    intros g2 pf2 nd_pf2 g0 pf0 nd_pf0 TSPLIT NLTS.
    remember pf as nd_pf. subst pf.
    remember pf1 as pf. subst pf1.
    exists a1. exists a2. exists b1. exists b2. exists t.
    specialize tsub_un with
        g g2 g0 pf pf2 pf0 a1 a2 vis pol t as TYP.
    specialize fsub_vis with
        g g2 g0 pf pf2 pf0 a1 a2 (Chan un pol t) as FYP.
    intuition.
    + inversion H; inversion H6; subst.
      apply flag_of_map with
          g0 (a1, a2) f1 vis in pf0 as FYP; subst...
      destruct t1. 
      *  apply tsub_payload with
             g g2 g0 pf pf2 pf0 b1 b2 f m p0 t1
          in H3 as TYPb.
         destruct TYPb as [p1 TYPb]; inversion TYPb; subst.
         inversion H; subst.
         right.
         ** destruct f0.
            *** destruct f. contradiction. 
                right. left. eauto.
                assert (hid = vis).
                assert (K2 := H3).
                apply fsub_vis with
                    g g2 g0 pf pf2 pf0 b1 b2 (Chan m p0 t1)
                  in K2...
                inversion H8.
            *** left. split. tauto.
                exists un. exists inp. exists (Chan m p1 t1).
                split. eauto.
                split. eauto.
                intros ABS. destruct ABS as [t2' ABS].
                elim NLTS.
                remember (Chan m p1 t1) as Tb.
                apply type_plus_comm in ABS.
                remember
                  (newEntries
                     g0
                     (secLabs
                        (dep_relabel p (domain g0) nd_pf0))
                     (max (domain g0))) as l.
                
                exists (( l ++ ((b1, b2), vis, t2')
                            :: (removeEntry (b1, b2) g0))).
                assert (ABS2: inp = inp \/ inp = io) by eauto.
                assert (LEM:
                          dep_relabel p (domain g0) nd_pf0 =
                          dep_relabel p (domain g) nd_pf).
                apply split_dep_relabel with
                    g2 pf pf2 pf0...
                apply uRin with
                    g0 inp p a1 a2 x1 x2 b1 b2 nd_pf0 ill
                    t Tb t2' in ABS2; subst l q. rewrite <-LEM...
                eauto.
                discriminate.
                all:eauto.
            *** left. split. tauto.
                exists un. exists inp. exists (Chan m p1 t1).
                split. eauto.
                split. eauto.
                intros ABS. destruct ABS as [t2' ABS].
                elim NLTS.
                remember (Chan m p1 t1) as Tb.
                apply type_plus_comm in ABS.
                remember
                  (newEntries
                     g0
                     (secLabs
                        (dep_relabel p (domain g0) nd_pf0))
                     (max (domain g0))) as l.
                exists (( l ++ ((b1, b2), vis, t2')
                            :: (removeEntry (b1, b2) g0))).
                assert (ABS2: inp = inp \/ inp = io) by eauto.
                assert (LEM:
                          dep_relabel p (domain g0) nd_pf0 =
                          dep_relabel p (domain g) nd_pf).
                apply split_dep_relabel with
                    g2 pf pf2 pf0...
                apply uRin with
                    g0 inp p a1 a2 x1 x2 b1 b2 nd_pf0 vis
                    t Tb t2' in ABS2; subst l q. rewrite <-LEM...
                eauto.
                discriminate.
                all:eauto.
         ** eauto. 
      * apply tsub_top with
            g g2 g0 pf pf2 pf0 b1 b2 f 
          in H3 as TYPb.
        inversion TYPb; subst.
        inversion H; subst.
        right.
        **destruct f0.
          *** destruct f. contradiction. 
              right. left. eauto.
              assert (hid = vis).
              assert (K2 := H3).
              apply fsub_vis with
                  g g2 g0 pf pf2 pf0 b1 b2 Top
                in K2...
              inversion H8.
          *** left. split. tauto.
              exists un. exists inp. exists Top.
              split. eauto.
              split. eauto.
              intros ABS. destruct ABS as [t2' ABS]. inversion ABS; subst.
              elim NLTS.
              remember
                (newEntries
                   g0
                   (secLabs
                      (dep_relabel p (domain g0) nd_pf0))
                   (max (domain g0))) as l.
              exists (( l ++ ((b1, b2), vis, Top)
                          :: (removeEntry (b1, b2) g0))).
              assert (ABS2: inp = inp \/ inp = io) by eauto.
              assert (LEM:
                        dep_relabel p (domain g0) nd_pf0 =
                        dep_relabel p (domain g) nd_pf).
              apply split_dep_relabel with
                  g2 pf pf2 pf0...
              apply uRin with
                  g0 inp p a1 a2 x1 x2 b1 b2 nd_pf0 ill
                  Top Top Top in ABS2; subst l q. rewrite <-LEM...
              eauto.
              discriminate.
              all:eauto.
          *** left. split. tauto.
              exists un. exists inp. exists Top.
              split. eauto.
              split. eauto.
              intros ABS. destruct ABS as [t2' ABS].
              inversion ABS; subst.
              elim NLTS.
              remember
                (newEntries
                   g0
                   (secLabs
                      (dep_relabel p (domain g0) nd_pf0))
                   (max (domain g0))) as l.
              exists (( l ++ ((b1, b2), vis, Top)
                          :: (removeEntry (b1, b2) g0))).
              assert (ABS2: inp = inp \/ inp = io) by eauto.
              assert (LEM:
                        dep_relabel p (domain g0) nd_pf0 =
                        dep_relabel p (domain g) nd_pf).
              apply split_dep_relabel with
                  g2 pf pf2 pf0...
              apply uRin with
                  g0 inp p a1 a2 x1 x2 b1 b2 nd_pf0 vis
                  Top Top Top in ABS2; subst l q. rewrite <-LEM...
              eauto.
              discriminate.
              all:eauto.
        ** eauto.
    + inversion H; inversion H6; subst.
      apply flag_of_map with
          g0 (a1, a2) f1 vis in pf0 as FYP; subst...
      destruct t1. 
      * apply tsub_payload with
            g g2 g0 pf pf2 pf0 b1 b2 f m p0 t1
          in H3 as TYPb.
        destruct TYPb as [p1 TYPb]; inversion TYPb; subst.
        inversion H; subst.
        right.
        ** destruct f0.
           *** destruct f. contradiction. 
               right. left. eauto.
               assert (hid = vis).
               assert (K2 := H3).
               apply fsub_vis with
                   g g2 g0 pf pf2 pf0 b1 b2 (Chan m p0 t1)
                 in K2...
               inversion H8.
           *** left. split. tauto.
               exists un. exists io. exists (Chan m p1 t1).
               split. eauto.
               split. eauto.
               intros ABS. destruct ABS as [t2' ABS].
               elim NLTS.
               remember (Chan m p1 t1) as Tb.
               apply type_plus_comm in ABS.
               remember
                 (newEntries
                    g0
                    (secLabs
                       (dep_relabel p (domain g0) nd_pf0))
                    (max (domain g0))) as l.
               exists (( l ++ ((b1, b2), vis, t2')
                           :: (removeEntry (b1, b2) g0))).
               assert (ABS2: io = inp \/ io = io) by eauto.
               assert (LEM:
                         dep_relabel p (domain g0) nd_pf0 =
                         dep_relabel p (domain g) nd_pf).
               apply split_dep_relabel with
                   g2 pf pf2 pf0...
               apply uRin with
                   g0 io p a1 a2 x1 x2 b1 b2 nd_pf0 ill
                   t Tb t2' in ABS2; subst l q. rewrite <-LEM...
               eauto.
               discriminate.
               all:eauto.
           *** left. split. tauto.
               exists un. exists io. exists (Chan m p1 t1).
               split. eauto.
               split. eauto.
               intros ABS. destruct ABS as [t2' ABS].
               elim NLTS.
               remember (Chan m p1 t1) as Tb.
               apply type_plus_comm in ABS.
               remember
                 (newEntries
                    g0
                    (secLabs
                       (dep_relabel p (domain g0) nd_pf0))
                    (max (domain g0))) as l.
               exists (( l ++ ((b1, b2), vis, t2')
                           :: (removeEntry (b1, b2) g0))).
               assert (ABS2: io = inp \/ io = io) by eauto.
               assert (LEM:
                         dep_relabel p (domain g0) nd_pf0 =
                         dep_relabel p (domain g) nd_pf).
               apply split_dep_relabel with
                   g2 pf pf2 pf0...
               apply uRin with
                   g0 io p a1 a2 x1 x2 b1 b2 nd_pf0 vis
                   t Tb t2' in ABS2; subst l q. rewrite <-LEM...
               eauto.
               discriminate.
               all:eauto.
        ** eauto.
      * apply tsub_top with
            g g2 g0 pf pf2 pf0 b1 b2 f 
          in H3 as TYPb.
        inversion TYPb; subst.
        inversion H; subst.
        right.
        **destruct f0.
          *** destruct f. contradiction. 
              right. left. eauto.
              assert (hid = vis).
              assert (K2 := H3).
              apply fsub_vis with
                  g g2 g0 pf pf2 pf0 b1 b2 Top
                in K2...
              inversion H8.
          *** left. split. tauto.
              exists un. exists io. exists Top.
              split. eauto.
              split. eauto.
              intros ABS. destruct ABS as [t2' ABS]. inversion ABS; subst.
              elim NLTS.
              remember
                (newEntries
                   g0
                   (secLabs
                      (dep_relabel p (domain g0) nd_pf0))
                   (max (domain g0))) as l.
              exists (( l ++ ((b1, b2), vis, Top)
                          :: (removeEntry (b1, b2) g0))).
              assert (ABS2: io = inp \/ io = io) by eauto.
              assert (LEM:
                        dep_relabel p (domain g0) nd_pf0 =
                        dep_relabel p (domain g) nd_pf).
              apply split_dep_relabel with
                  g2 pf pf2 pf0...
              apply uRin with
                  g0 io p a1 a2 x1 x2 b1 b2 nd_pf0 ill
                  Top Top Top in ABS2; subst l q. rewrite <-LEM...
              eauto.
              discriminate.
              all:eauto.
          *** left. split. tauto.
              exists un. exists io. exists Top.
              split. eauto.
              split. eauto.
              intros ABS. destruct ABS as [t2' ABS].
              inversion ABS; subst.
              elim NLTS.
              remember
                (newEntries
                   g0
                   (secLabs
                      (dep_relabel p (domain g0) nd_pf0))
                   (max (domain g0))) as l.
              exists (( l ++ ((b1, b2), vis, Top)
                          :: (removeEntry (b1, b2) g0))).
              assert (ABS2: io = inp \/ io = io) by eauto.
              assert (LEM:
                        dep_relabel p (domain g0) nd_pf0 =
                        dep_relabel p (domain g) nd_pf).
              apply split_dep_relabel with
                  g2 pf pf2 pf0...
              apply uRin with
                  g0 io p a1 a2 x1 x2 b1 b2 nd_pf0 vis
                  Top Top Top in ABS2; subst l q. rewrite <-LEM...
              eauto.
              discriminate.
              all:eauto.
        ** eauto.
  - Case lcomL.
    intros g2 pf3 nd_pf2 g1 pf4 nd_pf0 TSPLIT NLTS.
    elim NLTS.
    assert (DIFFA: (a1, a2) <> (b1, b2))...
    remember (removeEntry (a1, a2) (removeEntry (b1, b2) g1)) as g0'.
    apply split_exists_remove_l with
       g g2 g1 pf1 pf3 pf4 b1 b2 vis t s s1 
      in H1 as K1.
    destruct K1 as [s0 [s01 [TYP TREM]]].
      exists ((a1, a2, vis, Chan lin empty t) :: (b1, b2, vis, s0) :: g0').
    rewrite  Heqg0'.
     apply no_dup_cons_removeEntry_app with
         g1 (a1, a2) (b1, b2) vis (Chan lin out t) vis s0 in nd_pf0 as pf1'.
     apply no_dup_cons_removeEntry_app with
         g1 (a1, a2) (b1, b2) vis (Chan lin inp t) vis s01 in nd_pf0 as pf2'.
          
    apply lcomL with
        (g := g1) (p1 := p1) (q1 := q1) (a1 := a1) (a2 := a2)
        (t := t) (s := s0) (b1 := b1) (b2 := b2) (p2 := p2)
        (q2 := q2) (s1 := s01) (pf := nd_pf0)
    (pf1 := pf1') (pf2 := pf2'). 
    all:eauto.
    apply tsub_io with g g2 g1 pf1 pf3 pf4
                       a1 a2 vis lin t in H0 as K0.
    apply fsub_vis with g g2 g1 pf1 pf3 pf4 a1 a2 (Chan lin io t) in H0.
    inversion K0. inversion H0; subst.
    apply flag_of_map with (x := (a1, a2)) (f1 := f) (f2 := vis) in pf4 as FMAP; subst...
    all:eauto.
    inversion TYP...
    apply fsub_vis with g g2 g1 pf1 pf3 pf4 b1 b2 s in H1.
    inversion H1; subst...
    apply flag_of_map with (x := (b1, b2)) (f1 := f) (f2 := vis) in pf4 as FMAP; subst...
    all:eauto.
    clear IHLTS1 IHLTS2.
    + assert (pf5 : NoDup
                      (domain
                         (removeEntry (a1, a2) (removeEntry (b1, b2) g)))).
      apply no_dup_removeEntry_no_dup.
      apply no_dup_removeEntry_no_dup...
      assert (pf6 : NoDup
                      (domain
                         (removeEntry (a1, a2) (removeEntry (b1, b2) g1)))).
      apply no_dup_removeEntry_no_dup.
      apply no_dup_removeEntry_no_dup...
      specialize lts_type_remove_lin_out  with
          a1 a2 t b1 b2 vis vis s s1 s0 s01 p1 p2
          ((a1, a2, vis, Chan lin out t) :: (b1, b2, vis, s) :: g0) pf0
          ((a1, a2, vis, Chan lin out t)
     :: (b1, b2, vis, s0) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) pf1'
        as LTS3.
      assert (REMEQ3 : removeEntry (a1, a2)
            (removeEntry (b1, b2) ((a1, a2, vis, Chan lin out t) :: (b1, b2, vis, s) :: g0)) = g0).
      unfold removeEntry at 2.
      assert ( pair_eq (b1, b2) (b1, b2) = true)...
      rewrite H2.
      specialize pairEq_neq with (a1, a2) (b1, b2) as BNEQ.
      assert ((a1, a2) <> (b1, b2))...
      intuition.
      rewrite H6.
      unfold removeEntry. fold removeEntry.
      assert (pair_eq (a1, a2) (a1, a2) = true)...
      rewrite H5...
      rewrite REMEQ3 in LTS3.
      assert ( In (a1, a2, vis, Chan lin out t)
                  ((a1, a2, vis, Chan lin out t) :: (b1, b2, vis, s) :: g0))...
      assert (In (b1, b2, vis, s) ((a1, a2, vis, Chan lin out t) :: (b1, b2, vis, s) :: g0))...
      assert (In (a1, a2, vis, Chan lin out t)
           ((a1, a2, vis, Chan lin out t)
              :: (b1, b2, vis, s0) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)))...
       assert (In (b1, b2, vis, s0)
           ((a1, a2, vis, Chan lin out t)
              :: (b1, b2, vis, s0) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)))...
       assert (IFF:
                 (forall x : name * name,
          In x (domain ((a1, a2, vis, Chan lin out t) :: (b1, b2, vis, s) :: g0)) <->
          In x (domain ((a1, a2, vis, Chan lin out t) :: (b1, b2, vis, s0) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1))))).
       subst g0;
         unfold domain; fold domain;
           try eapply removeEntry_iff_cons,
         split_domain_l_2...
       
       eapply LTS3 in LTS1; clear LTS3 Case...
       assert (REMEQ4 : removeEntry (a1, a2)
                  (removeEntry (b1, b2)
                     ((a1, a2, vis, Chan lin out t)
                        :: (b1, b2, vis, s0) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1))) = removeEntry (a1, a2) (removeEntry (b1, b2) g1)).
        unfold removeEntry at 2.
      assert ( pair_eq (b1, b2) (b1, b2) = true)...
      rewrite H6.
      specialize pairEq_neq with (a1, a2) (b1, b2) as BNEQ.
      assert ((a1, a2) <> (b1, b2))...
      intuition.
      rewrite H10.
      unfold removeEntry. fold removeEntry.
      assert (pair_eq (a1, a2) (a1, a2) = true)...
      rewrite H9...
      rewrite REMEQ4 in *...

       simpl in NDSL;
      try eapply no_dup_distr in NDSL;
         intuition.
       
    simpl in INCL;
      eapply incl_app_inv in INCL as [_ INCL].
   (*; simpl;
      unfold incl;  introv IN;
      eapply INCL in IN;
     repeat rewrite <-hid_proj_removeEntry...*)
    eapply split_incl_hid_proj in TSPLIT as INCL2...
    assert (INCL3: incl (secLabs p1) (domain (hid_proj g1))). eapply incl_tran...

    (*incl (secLabs p1)
    (domain
       (hid_proj
          ((a1, a2, vis, Chan lin out t)
           :: (b1, b2, vis, s0) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)))) *)
    simpl.
    assert (IFF2: forall x,
               In x (domain (hid_proj g1)) ->
               In x (domain (hid_proj (removeEntry (a1, a2) (removeEntry (b1, b2) g1))))).
    introv IN.
    eapply fsub_vis in H0...
    eapply fsub_vis in H1...
    assert (IN2 := IN).
    eapply in_domain_in_g in IN2 as (ff &tt &IN2).
    repeat rewrite <-hid_proj_removeEntry;
      try eassumption.
      eapply in_g_in_domain;
      repeat eapply removeEntry_in;
      try introv ABS; subst;
      try eapply hid_proj_flagOf in IN.
    try inv IN...
    assert (vis = hid).
    eapply flag_of_map with (x := (a1,a2))...
    discriminate.
    eauto.
    assert (vis = hid).
    eapply flag_of_map with (x := (b1,b2))...
    discriminate.
    eauto.
    eauto.
    eauto.
    
    unfold incl;  introv IN;
      eapply INCL in IN;
       (* repeat rewrite <-hid_proj_removeEntry; *)
      try eapply IFF2...
    

      (*subst g0; introv FIMPL2 FIMPL1 DIFF.
      simpl in FIMPL;
        eapply fimpl_removeEntry with
        (a1 :=a1 )(a2 :=a2)(b1 :=b1)(b2 :=b2)
        (x :=x) (f2 :=f2)(f :=f1)in FIMPL;
        try assumption.*)
      
    + clear IHLTS1 IHLTS2.
       unfold type_remove in TREM.
      destruct TREM as [TSUB [TPLUS TUN]].
      apply type_plus_comm in TPLUS.
      assert (DIFF: vis <> hid). discriminate.
      move LTS2 at bottom; subst g0.
      specialize lts_type_plus_lin_in  with
          a1 a2 t b1 b2 vis vis s s1 s0 s01 q1 q2 ((a1, a2, vis, Chan lin inp t)
     :: (b1, b2, vis, s1) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)) pf2
          (((a1, a2, vis, Chan lin inp t)
              :: (b1, b2, vis, s01) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1))) pf2' as LTS3.
      
     
      assert (EQ: forall t s g,
                 removeEntry (a1, a2)
                    (removeEntry (b1, b2)
                       ((a1, a2, vis, t)
                        :: (b1, b2, vis, s)
                        :: g)) =
                   g).
      erewrite pairEq_neq in DIFFA.
      intros; simpl; rewrite DIFFA,pairEq_eq_true;
        simpl; rewrite pairEq_eq_true...
      rewrite EQ with (s := s01) in LTS3;
      eapply LTS3; clear LTS3; try eapply in_eq;
        try rewrite EQ with (s := s1);
        clear EQ;
        try assumption; try right;
          try eapply in_eq.
      simpl; eapply removeEntry_iff_cons...

       simpl in NDSL;
      try eapply no_dup_distr in NDSL;
      intuition.

       (*incl (secLabs q1)
    (domain
       (hid_proj
          ((a1, a2, vis, Chan lin inp t)
           :: (b1, b2, vis, s01) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1))))*)
       simpl. repeat rewrite <-hid_proj_removeEntry.
       simpl in INCL;
         eapply incl_app_inv in INCL as (INCL1 &INCL2).
       eapply incl_tran...
       introv IN...
       destruct a; eapply hid_proj_flagOf in IN.
       assert (IN2 := IN).
       inv IN2; try eapply fsub_hid in H2; try inv H2...
       eapply in_g_in_domain;
         repeat eapply removeEntry_in; try intros ABS;
         try inv ABS.
       eauto. 
       eauto.
       eapply in_hid_proj...
       all:eauto.
  - Case lclsL. intros g2 pf3 nd_pf2 g1 pf4 nd_pf0 TSPLIT NLTS.
    elim NLTS. clear IHLTS1 IHLTS2.
     assert (DIFFA: (a1, a2) <> (b1, b2))...
    remember (removeEntry (a1, a2) (removeEntry (b1, b2) g1)) as g0'.
    apply split_exists_remove_l with
       g g2 g1 pf1 pf3 pf4 b1 b2 hid t s s1 
      in H1 as K1.
    destruct K1 as [s0 [s01 [TYP TREM]]].
      exists ((a1, a2, vis, Chan lin empty t) :: (b1, b2, hid, s0) :: g0').
    rewrite  Heqg0'.
     apply no_dup_cons_removeEntry_app with
         g1 (a1, a2) (b1, b2) vis (Chan lin out t) vis s0 in nd_pf0 as pf1'.
     apply no_dup_cons_removeEntry_app with
         g1 (a1, a2) (b1, b2) vis (Chan lin inp t) vis s01 in nd_pf0 as pf2'.
          
    apply lclsL with
        (g := g1) 
        (p1 := p1) (q1 := q1) (a1 := a1) (a2 := a2)
        (t := t) (s := s0) (b1 := b1) (b2 := b2)
        (p2 := p2)
        (q2 := q2) (s1 := s01) (pf := nd_pf0)
        (pf1 := pf1') (pf2 := pf2'). 
    all:eauto.
    apply tsub_io with g g2 g1 pf1 pf3 pf4
                       a1 a2 vis lin t in H0 as K0.
    apply fsub_vis with g g2 g1 pf1 pf3 pf4 a1 a2 (Chan lin io t) in H0.
    inversion K0. inversion H0; subst.
    apply flag_of_map with (x := (a1, a2)) (f1 := f) (f2 := vis) in pf4 as FMAP; subst...
    all:eauto.
    inversion TYP; subst...
    assert (f = hid)...
    subst...
    + specialize lts_type_remove_lin_out  with
          a1 a2 t b1 b2 hid vis s s1 s0 s01 p1 p2
          ((a1, a2, vis, Chan lin out t) :: (b1, b2, hid, s) :: g0)pf0
         ((a1, a2, vis, Chan lin out t)
     :: (b1, b2, hid, s0) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)) pf1'
        as LTS3.

      assert (REMEQ: removeEntry (a1, a2)
                    (removeEntry (b1, b2)
                                 ((a1, a2, vis, Chan lin out t) :: (b1, b2, hid, s) :: g0)) = g0).
        unfold removeEntry at 2.
      assert ( pair_eq (b1, b2) (b1, b2) = true)...
      rewrite H2.
      specialize pairEq_neq with (a1, a2) (b1, b2) as BNEQ.
      assert ((a1, a2) <> (b1, b2))...
      intuition.
      rewrite H6.
      unfold removeEntry. fold removeEntry.
      assert (pair_eq (a1, a2) (a1, a2) = true)...
      rewrite H5...
      rewrite REMEQ in LTS3.

      eapply LTS3 in LTS1;clear LTS3 Case...
      
     
      
     assert (REMEQ2 : removeEntry (a1, a2)
                  (removeEntry (b1, b2)
                     ((a1, a2, vis, Chan lin out t)
                        :: (b1, b2, hid, s0) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1))) = removeEntry (a1, a2) (removeEntry (b1, b2) g1)).
       unfold removeEntry at 2.
      assert (PEQ: pair_eq (b1, b2) (b1, b2) = true)...
      rewrite PEQ.
      specialize pairEq_neq with (a1, a2) (b1, b2) as BNEQ.
      intuition.
      rewrite H4.
      unfold removeEntry. fold removeEntry.
      assert (pair_eq (a1, a2) (a1, a2) = true)...
      rewrite H3...
      rewrite REMEQ2 in *...

      subst g0;
         unfold domain; fold domain;
           try eapply removeEntry_iff_cons,
        split_domain_l_2...

       simpl in NDSL;
      try eapply no_dup_distr in NDSL;
      intuition.

      (* incl (secLabs p1)
    (domain
       (hid_proj
          ((a1, a2, vis, Chan lin out t)
           :: (b1, b2, hid, s0) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1)))) *)
       (*simpl in INCL;
         eapply incl_app_inv in INCL as [_ INCL].
       simpl.*)
       simpl.
       repeat rewrite <-hid_proj_removeEntry.
       simpl in INCL;
         eapply incl_app_inv in INCL as (INCL1 &INCL2).
       eapply incl_tran...
       introv IN...
       destruct a; eapply hid_proj_flagOf in IN.
       assert (IN2 := IN).
       inv IN2; try eapply fsub_hid in H3; try inv H3...
       case_eq (pair_eq (n,n0)(b1,b2)); introv PEQ;
         try rewrite <-pairEq_eq in PEQ; inv PEQ...
       rewrite <-pairEq_neq in H4; right.
       eapply fsub_hid in H2... inv H2.
       eapply in_g_in_domain;
         repeat eapply removeEntry_in; try intros ABS;
         try inv ABS.
       assert (flagOf g (a1, a2) vis)...
       assert (vis = hid)...
       discriminate.
       contradiction. 
       eapply in_hid_proj...
       all:eauto.
    
      
      
    +  unfold type_remove in TREM.
      destruct TREM as [TSUB [TPLUS TUN]].
      apply type_plus_comm in TPLUS.
      assert (DIFF: vis <> hid). discriminate.
      move LTS2 at bottom; subst g0.
      
      specialize lts_type_plus_lin_in  with
          a1 a2 t b1 b2 ill ill s s1 s0 s01 q1 q2 ((a1, a2, vis, Chan lin inp t)
     :: (b1, b2, ill, s1) :: removeEntry (a1, a2) (removeEntry (b1, b2) g)) pf2
          (((a1, a2, vis, Chan lin inp t)
              :: (b1, b2, ill, s01) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1))) pf2' as LTS3.
      
     
      assert (EQ: forall t s g,
                 removeEntry (a1, a2)
                    (removeEntry (b1, b2)
                       ((a1, a2, vis, t)
                        :: (b1, b2, ill, s)
                        :: g)) =
                          g).
       erewrite pairEq_neq in DIFFA.
      intros; simpl; rewrite DIFFA,pairEq_eq_true;
        simpl; rewrite pairEq_eq_true...
      
      rewrite EQ with (s := s01)  (g :=removeEntry (a1, a2) (removeEntry (b1, b2) g1)) in LTS3;
      eapply LTS3; clear LTS3; try eapply in_eq;
        try rewrite EQ with (s := s1);
        clear EQ;
        try assumption; try right;
          try eapply in_eq; try discriminate.
      simpl; eapply removeEntry_iff_cons...


      simpl in NDSL;
      try eapply no_dup_distr in NDSL;
        intuition.

      (*incl (secLabs q1)
    (domain
       (hid_proj
          ((a1, a2, vis, Chan lin inp t)
           :: (b1, b2, ill, s01) :: removeEntry (a1, a2) (removeEntry (b1, b2) g1))))*)
      assert (NIN: ~In (b1, b2) (secLabs q1)).
      intros ABS.
      eapply payload_occurs in LTS1 as [FN | SL].
      unfold wf in WF; destruct WF as (ND &DIS).
      eapply disjoint_absurd...
      simpl; eapply in_app_iff; left...
      simpl; eapply in_app_iff; left...
      unfold wf in WF; destruct WF as (ND &_).
      simpl in ND; eapply no_dup_iff in ND as (_ &_ &DIS).
      eapply disjoint_absurd...

      simpl. repeat rewrite <-hid_proj_removeEntry.
       simpl in INCL;
         eapply incl_app_inv in INCL as (INCL1 &INCL2).
       introv IN...
       assert (IN2 : In a (domain (hid_proj g))).
       eapply INCL1...
       destruct a; eapply hid_proj_flagOf in IN2; try inverts IN2 as IN2; try eapply fsub_hid with (g := g1) in IN2;
         try inverts IN2 as IN1.
       eapply in_g_in_domain;
         eapply removeEntry_in; try intros ABS;
         try inv ABS.
       assert (flagOf g (a1, a2) hid).
       eapply hid_proj_flagOf...
       assert (flagOf g (a1, a2) vis)...
       eapply removeEntry_in,in_hid_proj; try intros ABS;
         try inv ABS; try contradiction.
       all:eauto.
       
  - Case ucomL.
    intros g2 pf3 nd_pf3 g4 pf4 nd_pf TSPLIT NLTS.
    elim NLTS. clear IHLTS1 IHLTS2.
    assert (DIFF: (a1, a2)<> (b1, b2))...
    apply split_exists_remove_l with
        g g2 g4 pf1 pf3 pf4 b1 b2 vis t s s1 
      in H1 as K1.
    destruct K1 as [s0 [s01 [TYP TREM]]].
    eauto. 
    
    apply lts_un_input_action with
        (pol := io) (t := t) (s := s1) (r := s)
      in LTS2 as GEQ.
    destruct GEQ as (k1 &DIS &GEQ).

    apply no_dup_cons_removeEntry with (b := (b1, b2)) (f1 :=vis) (t1 := s1) in nd_pf as nd_pf2.
    specialize lts_type_plus_un_in with
        (g1 := ((b1, b2, vis, s01) :: removeEntry (b1, b2) g4))
        (pol := io) (t := t) (f := vis) (f1 := vis)
        (s := s) (s1 := s1) (s01 := s01) (s0 := s0) (pf := pf2)
        (a1 := a1) (a2 := a2) (b1 := b1) (b2 := b2)
        (k := k1) (q1 := q1) (q2 := q2)
        (pf1 := nd_pf2)
      as PLUS2.
    

   

   
    
    assert (In (a1, a2, vis, Chan un io t) ((b1, b2, vis, s1) :: removeEntry (b1, b2) g)).
    apply in_app_iff with
        (l := (b1, b2, vis, s1) :: nil). right.
    apply removeEntry_in...
    assert (In (b1, b2, vis, s1) ((b1, b2, vis, s1) :: removeEntry (b1, b2) g))...
    assert (type_plus s01 t s0).
    unfold type_remove in TREM; destruct TREM as [TSUB [TREM TUN]].
    apply type_plus_comm in TREM...
    assert (vis <> hid) by discriminate.
    assert (In (a1, a2, vis, Chan un io t) ((b1, b2, vis, s01) :: removeEntry (b1, b2) g4)).
    apply in_app_iff with
        (l := (b1, b2, vis, s01) :: nil). right.
    apply removeEntry_in.
    eauto.
    apply tsub_io with
        (g1 := g) (g2 := g2) (g := g4)
        (pf1 := pf1) (pf2 := pf3) (pf := pf4) in H0 as K0.
    inversion K0; subst.
    assert (f = vis)... subst...
    eauto.
    assert (In (b1, b2, vis, s01) ((b1, b2, vis, s01) :: removeEntry (b1, b2) g4))...
    assert ((In (a1, a2, vis, Chan un io t) (k1 ++ (b1, b2, vis, s0) :: removeEntry (b1, b2) g4))).
    apply in_app_iff. right.
    apply in_app_iff with
        (l := (b1, b2, vis, s0) :: nil); right.
    apply removeEntry_in.
    eauto.
    apply tsub_io with
        (g1 := g) (g2 := g2) (g := g4)
        (pf1 := pf1) (pf2 := pf3) (pf := pf4) in H0 as K0.
    inversion K0; subst.
    assert (f = vis)... subst...
    eauto.
    assert (In (b1, b2, vis, s0) (k1 ++ (b1, b2, vis, s0) :: removeEntry (b1, b2) g4)).
    apply in_app_iff. right...
    assert(typeOf g' (a1, a2) (Chan un io t)).
    subst g' g0...
    assert (typeOf g' (b1, b2) s1).
    subst g' g0...
    assert (type_plus s1 t s).
    unfold type_remove in H; destruct H as [TSUB [TREM2 TUN]].
    apply type_plus_comm in TREM2...
    assert (lts ((b1, b2, vis, s1) :: removeEntry (b1, b2) g) q1 (aIn a1 a2 b1 b2)
                (k1 ++
                    (b1, b2, vis, s)
                    :: removeEntry (b1, b2) ((b1, b2, vis, s1) :: removeEntry (b1, b2) g)) q2 pf2).
    subst g' g0 g3.
    assumption.
    
    intuition.
    specialize split_domain_l_2 with
        (g1 := g) (g2 := g2) (g := g4)
        (pf1 := pf1) (pf2 := pf3) (pf := pf4) as DOM.
    intuition.

    assert (K16: (forall x : name * name,
         In x (domain ((b1, b2, vis, s1) :: removeEntry (b1, b2) g)) <->
         In x (domain ((b1, b2, vis, s01) :: removeEntry (b1, b2) g4)))).
    intuition.
    elim H18. intros.  inversion H19; subst.
    unfold domain; fold domain...
    intros.
    unfold domain; fold domain...
    apply in_app_iff with (l := (b1, b2) :: nil); right.
    assert ((a,b) = (b1, b2) -> False). intro ABS.
    inversion ABS. subst.
    apply in_domain_in_g in H19 as [f [t1 H19]].
    apply no_dup_not_in_removeEntry in H19 as K19.
    contradiction.
    eauto.
    specialize H17 with (a, b) as K17.
    apply in_domain_in_g in H19 as [f [t1 H19]].
    apply in_removeEntry in H19. apply in_g_in_domain in H19.
    apply K17 in H19 as K18.
    apply in_domain_in_g in K18 as [f2 [t2 K19]].
    apply removeEntry_in with (y := (b1, b2)) in K19.
    apply in_g_in_domain in K19...
    eauto.
    elim H18. intros.  inversion H19; subst.
    unfold domain; fold domain...
    intros.
    unfold domain; fold domain...
    apply in_app_iff with (l := (b1, b2) :: nil); right.
    assert ((a,b) = (b1, b2) -> False). intro ABS.
    inversion ABS. subst.
    apply in_domain_in_g in H19 as [f [t1 H19]].
    apply no_dup_not_in_removeEntry in H19 as K19.
    contradiction.
    eauto.
    specialize H17 with (a, b) as K17.
    apply in_domain_in_g in H19 as [f [t1 H19]].
    apply in_removeEntry in H19. apply in_g_in_domain in H19.
    apply K17 in H19 as K18.
    apply in_domain_in_g in K18 as [f2 [t2 K19]].
    apply removeEntry_in with (y := (b1, b2)) in K19.
    apply in_g_in_domain in K19...
    eauto.
    
    
    apply H16 in K16.
    destruct K16 as [k2 LTS3].
    
    exists
      (k2 ++ (b1, b2, vis, s0) :: removeEntry (b1, b2) g4).
    (*    apply no_dup_cons_removeEntry with (b := (b1, b2)) (f1 :=vis) (t1 := s1) in nd_pf as nd_pf2.*)
    apply ucomL with
        (b1 := b1) (b2 := b2) (s := s0) (s1 := s01) (t := t) (pf1 := nd_pf) (pf2 := nd_pf2) .
    eauto.    
    apply tsub_io with g g2 g4 pf1 pf3 pf4
                       a1 a2 vis un t in H0 as K0.
    apply fsub_vis with g g2 g4 pf1 pf3 pf4 a1 a2 (Chan un io t) in H0.
    inversion K0. inversion H0; subst.
    apply flag_of_map with (x := (a1, a2)) (f1 := f) (f2 := vis) in pf4 as FMAP; subst...
    eauto.
    eauto.

    inversion TYP.
    apply fsub_vis with g g2 g4 pf1 pf3 pf4 b1 b2 s in H1.
    inversion H1; subst.
    apply type_of_map with (x := (b1, b2)) (t1 := s0) (t2 := t1) in pf4 as TMAP; subst...
    eauto.
    specialize lts_type_remove_un_out  with
        a1 a2 io t b1 b2 vis vis s s1 s0 s01 p1 p2
        g pf0 g4 nd_pf
      as LTS4.
    unfold g0 in LTS1.
    apply no_dup_isMap in pf.
    apply tsub_io with
        (g1 := g) (g2 := g2) (g := g4)
        (pf1 := pf1) (pf2 := pf3) (pf := pf4) in H0 as K0.
    inversion K0; subst.
    assert (K1 := H0).
    apply fsub_vis with
        (g1 := g) (g2 := g2) (g := g4)
        (pf1 := pf1) (pf2 := pf3) (pf := pf4) in H0.
    inversion H0.
    apply flag_of_map with (x := (a1, a2)) (f1 := f) (f2 := vis) in pf4 as FMAP; subst.
    assert (In (b1, b2, vis, s0) g4).
    inversion TYP; subst.
    assert (f = vis)... subst...
    assert (IFF:  (forall x : name * name, In x (domain g) <-> In x (domain g4)))...

    eapply LTS4...

    simpl in NDSL;
      try eapply no_dup_distr in NDSL;
      intuition.

    (* incl (secLabs p1) (domain (hid_proj g4))*)
    eapply incl_tran, split_incl_hid_proj with (g1 := g);
      simpl in INCL; eapply incl_app_inv in INCL as [INCL1 INCl2]...
    
    eauto. eauto. eauto. eauto.
    assert (REMEQ: removeEntry (b1, b2) g4 = removeEntry (b1, b2) ((b1, b2, vis, s01) :: removeEntry (b1, b2) g4)).
    unfold removeEntry at 2; fold removeEntry.
    assert (PEQ: pair_eq (b1, b2) (b1, b2) = true)...
    rewrite PEQ...
    rewrite REMEQ at 2.
    assumption.
    
    apply in_app_iff. right.
    (*In (a1, a2, vis, Chan un io t) ((b1, b2, vis, s0) :: removeEntry (b1, b2) g4)*)
    apply in_app_iff with
        (l := (b1, b2, vis, s0) :: nil); right.
    apply removeEntry_in...
    apply tsub_io with
        (g1 := g) (g2 := g2) (g := g4)
        (pf1 := pf1) (pf2 := pf3) (pf := pf4) in H0 as K0.
    inversion K0; subst.
    assert (f = vis)... subst...
    eauto.
    apply in_app_iff. right...
    subst g' g0...

    simpl in NDSL;
      try eapply no_dup_distr in NDSL;
      intuition.

    (* incl (secLabs q1) (domain (hid_proj ((b1, b2, vis, s01) :: removeEntry (b1, b2) g4)))*)
    simpl.
    simpl in INCL; eapply incl_distr in INCL as [INCL _].
    rewrite <-hid_proj_removeEntry.
    introv IN.
    assert (IN2 := IN); destruct a; try eapply INCL,hid_proj_flagOf in IN2; try inverts IN2 as IN2;
      try eapply fsub_hid with (g := g4)in IN2;
      try inverts IN2 as IN4.
    eapply in_g_in_domain,removeEntry_in; try intros ABS;
      try inv ABS.
    eapply fsub_vis in H1...
    eapply in_hid_proj...
    eauto.
    eauto.
    eauto.
   
    
    (*  disjoint (domain k1) (domain ((b1, b2, vis, s1) :: removeEntry (b1, b2) g)) *)
    subst g'...
    subst g' g0... 
    (*typeOf g' (b1, b2) s1*)
    subst g' g0...
    (* type_plus s1 t s*)
    unfold type_remove in H; destruct H as [TSUB [TREM2 TUN]].
    apply type_plus_comm in TREM2...
    eapply sl_pos_par_r...
    subst g' g0.
    eapply max_sl_par in MAX as (_&MAX).
    (* max (secLabs q1) <= max (domain ((b1, b2, vis, s1) :: removeEntry (b1, b2) g))*)
    erewrite <-max_removeEntry_cons;
      try eapply in_g_in_domain...
    all : eauto.
  -  Case open. intros g2 pf3 nd_pf3 g4 pf4 nd_pf TSPLIT NLTS.
     elim NLTS. clear IHLTS1 IHLTS2.
    apply split_exists_remove_l with
        g g2 g4 pf1 pf3 pf4 b1 b2 hid t s s1 
      in H1 as K1.
    destruct K1 as [s0 [s01 [TYP TREM]]].
    eauto. 
    
    apply lts_un_input_action with
        (pol := io) (t := t) (s := s1) (r := s)
      in LTS2 as GEQ.
    destruct GEQ as (k1 &DIS &GEQ).

    apply no_dup_cons_removeEntry with (b := (b1, b2)) (f1 := vis) (t1 := s1) in nd_pf as nd_pf2.

    
    specialize lts_type_plus_un_in with
        (g1 := ((b1, b2, ill, s01) :: removeEntry (b1, b2) g4))
        (pol := io) (t := t) (f := ill) (f1 := ill)
        (s := s) (s1 := s1) (s01 := s01) (s0 := s0) (pf := pf2)
        (a1 := a1) (a2 := a2) (b1 := b1) (b2 := b2)
        (k := k1) (q1 := q1) (q2 := q2)
        (pf1 := nd_pf2)
      as PLUS2.
    
    assert (In (a1, a2, vis, Chan un io t) ((b1, b2, ill, s1) :: removeEntry (b1, b2) g)).
    apply in_app_iff with
        (l := (b1, b2, ill, s1) :: nil). right.
    apply removeEntry_in...
    assert (In (b1, b2, ill, s1) ((b1, b2, ill, s1) :: removeEntry (b1, b2) g))...
    assert (type_plus s01 t s0).
    unfold type_remove in TREM; destruct TREM as [TSUB [TREM TUN]].
    apply type_plus_comm in TREM...
    assert (ill <> hid) by discriminate.
    assert (In (a1, a2, vis, Chan un io t) ((b1, b2, ill, s01) :: removeEntry (b1, b2) g4)).
    apply in_app_iff with
        (l := (b1, b2, ill, s01) :: nil). right.
    apply removeEntry_in.
    eauto.
    apply tsub_io with
        (g1 := g) (g2 := g2) (g := g4)
        (pf1 := pf1) (pf2 := pf3) (pf := pf4) in H0 as K0.
    inversion K0; subst.
    assert (f = vis)... subst...
    eauto.
    assert (In (b1, b2, ill, s01) ((b1, b2, ill, s01) :: removeEntry (b1, b2) g4))...
    assert ((In (a1, a2, vis, Chan un io t) (k1 ++ (b1, b2, vis, s0) :: removeEntry (b1, b2) g4))).
    apply in_app_iff. right.
    apply in_app_iff with
        (l := (b1, b2, vis, s0) :: nil); right.
    apply removeEntry_in.
    eauto.
    apply tsub_io with
        (g1 := g) (g2 := g2) (g := g4)
        (pf1 := pf1) (pf2 := pf3) (pf := pf4) in H0 as K0.
    inversion K0; subst.
    assert (f = vis)... subst...
    eauto.
    assert (In (b1, b2, ill, s0) (k1 ++ (b1, b2, ill, s0) :: removeEntry (b1, b2) g4)).
    apply in_app_iff. right...
    assert(typeOf g' (a1, a2) (Chan un io t)).
    subst g' g0...
    assert (typeOf g' (b1, b2) s1).
    subst g' g0...
    assert (type_plus s1 t s).
    unfold type_remove in H; destruct H as [TSUB [TREM2 TUN]].
    apply type_plus_comm in TREM2...
    assert (lts ((b1, b2, ill, s1) :: removeEntry (b1, b2) g) q1 (aIn a1 a2 b1 b2)
                (k1 ++
                    (b1, b2, vis, s)
                    :: removeEntry (b1, b2) ((b1, b2, vis, s1) :: removeEntry (b1, b2) g)) q2 pf2).
    subst g' g0 g3.
    unfold removeEntry at 2 in LTS2.
    assert (BEQ: pair_eq (b1, b2) (b1, b2)=true)...
    rewrite BEQ in LTS2. 
    unfold removeEntry at 2. rewrite BEQ.
     unfold removeEntry in PLUS2. rewrite BEQ in PLUS2. 
     assumption.
     assert (BEQ: pair_eq (b1, b2) (b1, b2)=true)...
     unfold removeEntry at 2 in H15. rewrite BEQ in H15.
 unfold removeEntry at 2 in PLUS2. rewrite BEQ in PLUS2. 

    intuition.
    specialize split_domain_l_2 with
        (g1 := g) (g2 := g2) (g := g4)
        (pf1 := pf1) (pf2 := pf3) (pf := pf4) as DOM.
    intuition.

    assert (K16: (forall x : name * name,
         In x (domain ((b1, b2, ill, s1) :: removeEntry (b1, b2) g)) <->
         In x (domain ((b1, b2, vis, s01) :: removeEntry (b1, b2) g4)))).
    intuition. 
    elim H18. intros.  inversion H19; subst.
    unfold domain; fold domain...
    intros.
    unfold domain; fold domain...
    apply in_app_iff with (l := (b1, b2) :: nil); right.
    assert ((a,b) = (b1, b2) -> False). intro ABS.
    inversion ABS. subst.
    apply in_domain_in_g in H19 as [f [t1 H19]].
    apply no_dup_not_in_removeEntry in H19 as K19.
    contradiction.
    eauto.
    specialize H17 with (a, b) as K17.
    apply in_domain_in_g in H19 as [f [t1 H19]].
    apply in_removeEntry in H19. apply in_g_in_domain in H19.
    apply K17 in H19 as K18.
    apply in_domain_in_g in K18 as [f2 [t2 K19]].
    apply removeEntry_in with (y := (b1, b2)) in K19.
    apply in_g_in_domain in K19...
    eauto.
    elim H18. intros.  inversion H19; subst.
    unfold domain; fold domain...
    intros.
    unfold domain; fold domain...
    apply in_app_iff with (l := (b1, b2) :: nil); right.
    assert ((a,b) = (b1, b2) -> False). intro ABS.
    inversion ABS. subst.
    apply in_domain_in_g in H19 as [f [t1 H20]].
    apply no_dup_not_in_removeEntry in H20 as K20.
    contradiction.
    eauto.
    specialize H17 with (a, b) as K17.
    apply in_domain_in_g in H19 as [f [t1 H21]].
    apply in_removeEntry in H21.
    apply in_g_in_domain in H21.
    apply K17 in H21 as K18.
    apply in_domain_in_g in K18 as [f2 [t2 K19]].
    apply removeEntry_in with (y := (b1, b2)) in K19.
    apply in_g_in_domain in K19...
    eauto.
    
    
    apply H16 in K16.
    destruct K16 as [k2 LTS3].
    
     remember  (k2 ++
            (b1, b2, vis, s0) :: removeEntry (b1, b2) ((b1, b2, ill, s01) :: removeEntry (b1, b2) g4)) as k3.
    exists
      ((b1, b2, hid, s0) :: removeEntry (b1, b2) k3).
    
     apply uclsL with
         (b1 := b1) (b2 := b2) (s := s0) (s1 := s01) (t := t)
         (pf1 := nd_pf) (pf2 := nd_pf2) .
    eauto.    
    apply tsub_io with g g2 g4 pf1 pf3 pf4
                       a1 a2 vis un t in H0 as K0.
    apply fsub_vis with g g2 g4 pf1 pf3 pf4 a1 a2 (Chan un io t) in H0.
    inversion K0. inversion H0; subst.
    apply flag_of_map with (x := (a1, a2)) (f1 := f) (f2 := vis) in pf4 as FMAP; subst...
    eauto.
    eauto.

    inversion TYP.
    apply fsub_hid with g g2 g4 pf1 pf3 pf4 b1 b2 s in H1.
    inversion H1; subst.
    apply type_of_map with (x := (b1, b2)) (t1 := s0) (t2 := t1) in pf4 as TMAP; subst...
    eauto.

    specialize lts_type_remove_un_out  with
        a1 a2 io t b1 b2 hid vis s s1 s0 s01 p1 p2
        g pf0 g4 nd_pf
      as LTS4.
    unfold g0 in LTS1.
    apply no_dup_isMap in pf.
    apply tsub_io with
        (g1 := g) (g2 := g2) (g := g4)
        (pf1 := pf1) (pf2 := pf3) (pf := pf4) in H0 as K0.
    inversion K0; subst.
    assert (K1 := H0).
    apply fsub_vis with
        (g1 := g) (g2 := g2) (g := g4)
        (pf1 := pf1) (pf2 := pf3) (pf := pf4) in H0.
    inversion H0.
    apply flag_of_map with (x := (a1, a2)) (f1 := f) (f2 := vis) in pf4 as FMAP; subst.
    assert (In (b1, b2, hid, s0) g4).
    inversion TYP; subst.
    assert (f = hid)... subst...
    
    assert (IFF: (forall x : name * name,
         In x (domain ((b1, b2, ill, s01) :: removeEntry (b1, b2) g4)) <->
           In x (domain ((b1, b2, ill, s1) :: removeEntry (b1, b2) g)))).
    intros; eapply split_removeEntry_domain...

    eapply LTS4...

    simpl in NDSL;
      try eapply no_dup_distr in NDSL;
      intuition.

    simpl in INCL;
      eapply incl_app_inv in INCL as [_ INCL].
    (*incl (secLabs p1) (domain (hid_proj g4))*)
    eapply incl_tran, split_incl_hid_proj with (g1 := g);
      simpl in INCL... 

    eauto. 
    eauto.
    eauto.
    eauto.
    eauto.
    rewrite Heqk3.
    apply in_app_iff with ( l := k2). right. 
    apply in_app_iff with (l := (b1, b2, vis, s0) :: nil). right.
    unfold removeEntry at 1.  rewrite BEQ.
    apply in_app_iff with (l :=(b1, b2, ill, s01)::nil) in H8 as [ABS | H8].
    inversion ABS. inversion H8.  inversion H8...
    eauto.
    rewrite Heqk3.
    apply in_app_iff with ( l := k2). right...

     simpl in NDSL;
      try eapply no_dup_distr in NDSL;
      intuition.

     simpl in INCL;
      eapply incl_app_inv in INCL;
       intuition.
     simpl.
     (*incl (secLabs q1) (domain (hid_proj (removeEntry (b1, b2) g4)))*)
      assert (NIN: ~In (b1, b2) (secLabs q1)).
      intros ABS.
      eapply payload_occurs in LTS1 as [FN | SL].
      unfold wf in WF; destruct WF as (ND &DIS2).
      eapply disjoint_absurd with (1 := DIS2)...
      simpl; eapply in_app_iff; left...
      simpl; eapply in_app_iff; left...
      simpl in NDSL; try eapply no_dup_iff in NDSL as (_ &_ &DIS3).
      eapply disjoint_absurd...

      simpl. repeat rewrite <-hid_proj_removeEntry.
      assert (INCL1 := H18).
       introv IN...
       assert (IN2 : In a (domain (hid_proj g))).
       eapply INCL1...
       destruct a; eapply hid_proj_flagOf in IN2; try inverts IN2 as IN2; try eapply fsub_hid with (g := g4) in IN2;
         try inverts IN2 as IN1.
       eapply in_g_in_domain;
         eapply removeEntry_in; try intros ABS;
         try inv ABS; try contradiction.
       eapply in_hid_proj...
       eauto.
       eauto.
     
    subst g' g0.
    eauto.
    eauto.
    subst g' g0...
    subst g' g0...
    unfold type_remove in H. destruct H as [TSUB [TPLUS TUN]].
    apply type_plus_comm...
    eauto.
    eapply sl_pos_par_r...
    subst g' g0;
       eapply max_sl_par in MAX as (_ &MAX)...
    (* max (secLabs q1) <= max (domain ((b1, b2, ill, s1) :: removeEntry (b1, b2) g))*)
    erewrite <-max_removeEntry_cons;
      try eapply in_g_in_domain...
    all:eauto.
  - intros.
    assert (DIS: disjoint (secLabs p) [(b1, b2)] ).
    simpl in NDSL; try eapply no_dup_disjoint...
    exists a1. exists a2. exists b1. exists b2.

    
    apply no_dup_isMap in pf0 as pf0_m.
    
    specialize split_domain_l with g g2 g0 pf1 pf2 pf3 (b1, b2)
      as SD.
    apply SD in TSPLIT as IFF.
    apply in_g_in_domain in H as K. apply IFF in K as TYPb0.
    apply in_domain_in_g in TYPb0.
    destruct TYPb0 as [f1 [tb0 TYPb0]].
     specialize split_domain_m with g g2 g0 pf1 pf2 pf3 (b1, b2)
      as SD2.
      apply SD2 in TSPLIT as IFF2.
    apply in_g_in_domain in H as K2. apply IFF2 in K2 as TYPb2.
    apply in_domain_in_g in TYPb2.
    destruct TYPb2 as [f2 [tb2 TYPb2]].

    remember ((b1, b2, vis, tb0) :: removeEntry (b1, b2) g0) as k0.
    remember ((b1, b2, vis, tb2) :: removeEntry (b1, b2) g2) as k2.
    assert (pfk0 : NoDup (domain k0)).
    apply no_dup_removeEntry_no_dup with (a := (b1, b2)) in nd_pf as nd_pf0'.
    subst k0; unfold domain; fold domain.
    apply NoDup_cons...
    intro.
    apply in_domain_in_g in H1 as [f3 [t3 ABS]].
    apply no_dup_not_in_removeEntry in ABS...
    
    assert (pfk2 : NoDup (domain k2)). subst k2.
    apply no_dup_cons_removeEntry...
    apply no_dup_isMap in pfk0 as pfk0_m.
    apply no_dup_isMap in pfk2 as pfk2_m. 
    
    specialize IHLTS with
        (pf1 := pf0_m) (nd_pf := pfk0) (pf2 := pfk2_m)
        (pf := pfk0_m) .
    assert (TSPLIT2 : tEnv_split ((b1, b2, vis, t) :: removeEntry (b1, b2) g) k2 k0 pf0_m pfk2_m
                       pfk0_m).
    subst k0 k2.
    specialize split_cons_remove with
        (b1 := b1) (b2 := b2)
        (pf1 := pf1) (pf2 := pf2) (pf3 := pf3)
        (t1 := t) (t2 := tb2) (t3 := tb0)
        (f1 := hid) (f2 := f2) (f3 := f1)
        (pf1' := pf0_m) (pf2' := pfk2_m)
        (pf3' := pfk0_m ) as TSPLITREM.
    eauto.
    
    intuition.
    
    assert (((exists g' : typeEnv, lts k0 p (aOut a1 a2 b1 b2) g' p' pfk0) -> False)). intros ABS.
    destruct ABS as [k' ABS].
    elim H0.
    subst.
    exists k'. apply open with (t := tb0) (pf1 := pfk0).
    assert (FLHID: flagOf g0 (b1, b2) hid).
    specialize fsub_hid with g g2 g0 pf1 pf2 pf3 b1 b2 t as FHID.
      intuition.
    inversion FLHID; subst.
    assert (f1 = hid /\ tb0 = t0).
    apply in_isMap with (x := (b1, b2)) (g := g0)...
    intuition; subst...
    eauto.

    assert (SLP1: sl_pos p).
    eapply sl_pos_nu...
    assert (MAX1:
               max (secLabs p) <= max (domain ((b1, b2, vis, t) :: removeEntry (b1, b2) g)))...
    eapply max_sl_nu in MAX.
    (*  max (secLabs p) <= max (domain ((b1, b2, vis, t) :: removeEntry (b1, b2) g)) *)
    erewrite <-max_removeEntry_cons...
    
     simpl in NDSL;
       try eapply no_dup_distr in NDSL as [IH _]; try eapply IHLTS in IH as [x1 [x2 [y1 [y2 [t0 [IH1 | [IH2 | [IH3 | IH4]]]]]]]];
       try intuition.
     
    inversion H10.
    intuition.
    inversion H10.
    intuition.
    inversion H10.
    intuition.
    inversion H10.
    subst x1 x2 y1 y2.
    
    exists t0. right. right. right.
    split...
    split.
    subst.
    inversion H12. subst.
    apply in_app_iff with (l := (b1, b2, vis, t) :: nil) in H11 as [HEAD | TAIL].
    inversion HEAD. inversion H11; subst... inversion H11.
    apply in_removeEntry in TAIL...
    subst k0. inversion H13. subst.
    apply in_app_iff with (l := (b1, b2, vis, tb0) :: nil) in H11 as [HEAD | TAIL].
    inversion HEAD. inversion H11; subst... inversion H11.
    apply in_removeEntry in TAIL...

    (*incl (secLabs p) (domain (hid_proj ((b1, b2, vis, t) :: removeEntry (b1, b2) g)))*)
    move DIS at bottom.
    simpl in *; eapply incl_app_inv in INCL as [INCL INCL2]; try rewrite <-hid_proj_removeEntry;
      try eassumption;
      introv IN.
    assert (DIFF: a <> (b1, b2)).
    try introv ABS; subst;
      try eapply disjoint_absurd...
    eapply INCL in IN;
    try eapply in_domain_in_g in IN as (ff2 &tt2 &IN2);
      try  eapply in_g_in_domain,removeEntry_in...

    eapply wf_res...

  - Case hide. intros.
    
    remember g0 as g3. subst g0.

    assert (DIS: disjoint (secLabs p) [(b1, b2)] ).
    simpl in NDSL; try eapply no_dup_disjoint...
    
    assert (IN: In  (b1, b2, hid, t) g).
    subst g; eapply in_app_iff; right...
    assert (IN3:=IN).
    eapply in_g_in_domain in IN;
      erewrite split_domain_m in IN;
    eapply in_domain_in_g in IN as (f2 &t2 &IN2)...
     eapply in_g_in_domain in IN3;
       erewrite split_domain_l_2 in IN3;
       eapply in_domain_in_g in IN3 as (f3 &t3 &IN3)...

     eapply sl_pos_nu in SLP as IH.
     
    

     
    
    
    
     assert (EX: exists t3',
                typeOf g3 (b1,b2) t3' /\ type_plus t t2 t3').
     eapply split_type_plus_r...
     subst;econstructor;eapply in_app_iff;right...
     destruct EX as (t3' & TYP3 &TP3).
     assert (t3'=t3)...
     subst t3'.

      assert (nd_pfv1:
               NoDup (
                   domain (
                       (b1, b2, vis, t)
                         :: removeEntry (b1,b2) g))).
     eapply no_dup_cons_removeEntry...
     assert (nd_pfv2:
               NoDup (
                   domain (
                       (b1, b2, vis, t2)
                         :: removeEntry (b1,b2) g2))).
     eapply no_dup_cons_removeEntry...
     assert (nd_pfv3:
               NoDup (
                   domain (
                       (b1, b2, vis, t3)
                         :: removeEntry (b1,b2) g3))).
     eapply no_dup_cons_removeEntry...

    
     eapply no_dup_isMap in nd_pfv1 as pfv1;
       eapply no_dup_isMap in nd_pfv2 as pfv2;
       eapply no_dup_isMap in nd_pfv3 as pfv3;
       eapply tEnv_split_add_vis
         with (pf' := pfv1)
              (pf'' := pfv2)
              (pf''' := pfv3) in TP3 as TS.

    
     eapply no_dup_isMap in pf0 as pfv'.
     assert (TS':
             tEnv_split (h1 ++ (b1, b2, vis, t) :: h2) ((b1, b2, vis, t2) :: removeEntry (b1, b2) g2)
                        ((b1, b2, vis, t3) :: removeEntry (b1, b2) g3) pfv' pfv2 pfv3).
     eapply split_comm in TS; eapply split_comm.
     eapply split_iff2 with (pf2 := pfv1)...
     assert (EQ:
               removeEntry (b1, b2) g = h1 ++ h2).
     subst g.
     erewrite removeEntry_app_shift; simpl;
       try rewrite pairEq_eq_true; try intros ABS...
     assert (ND := pf0); rewrite domain_distr in ND; simpl in ND;
       try eapply no_dup_iff in ND as (_&_&DISS); eapply disjoint_absurd...
     rewrite EQ.

     (* In x ((b1, b2, vis, tt) :: h1 ++ h2) <-> In x (h1 ++ (b1, b2, vis, tt) :: h2)*)

    assert (P0: Permutation ((b1, b2, vis, t) :: h1 ++ h2)(h1 ++ (b1, b2, vis, t) :: h2)).
     specialize Permutation_cons_append with (l := h1) (x :=  (b1, b2, vis, t)) as P1.
     assert (EQ2: ((b1, b2, vis, t) :: h1 ++ h2 =
                   ((b1, b2, vis, t) :: h1 )++h2))...
     assert (EQ3: h1 ++ (b1, b2, vis, t) :: h2 =
                  (h1 ++ (b1, b2, vis, t) :: nil) ++ h2).
     erewrite cons_app,<-app_assoc...
     erewrite EQ2,EQ3;
       eapply Permutation_app...
     intros; split; try eapply Permutation_in...
     try eapply Permutation_sym...

     assert (IN: In (b1, b2,hid, t) g).
    subst; eapply in_app_iff; right...
     eapply fsub_hid with (pf := pf3) in IN;
       try inverts IN as IN.
     assert (EQ3:f3 = hid /\ t3 = t0)...
     destruct EQ3; subst f3 t0.
     eapply in_split in IN as (l1 &l2 &EQ3).

     

     assert (nd_pfv3' : NoDup (domain ( l1 ++ (b1, b2, vis, t3) :: l2))).
     assert (pf00':= nd_pf); subst g3;
       try rewrite domain_distr in *; simpl in *...
     eapply no_dup_isMap in nd_pfv3' as pfv3'.
     assert (TS'':
             tEnv_split (h1 ++ (b1, b2, vis, t) :: h2) ((b1, b2, vis, t2) :: removeEntry (b1, b2) g2)
          (l1 ++ (b1, b2, vis, t3) :: l2) pfv' pfv2 pfv3').  
     eapply split_iff with (pf := pfv3)...
     subst g3.
     assert (EQ3: removeEntry (b1, b2) (l1 ++ (b1, b2, hid, t3) :: l2) =
                 l1 ++ l2).
      erewrite removeEntry_app_shift; simpl;
       try rewrite pairEq_eq_true; try intros ABS...
     assert (ND :=   nd_pfv3'); rewrite domain_distr in ND; simpl in ND;
       try eapply no_dup_iff in ND as (_&_&DISS); eapply disjoint_absurd...

     (*  forall x : name * name * flag * piType,
  In x ((b1, b2, vis, t3) :: removeEntry (b1, b2) (l1 ++ (b1, b2, hid, t3) :: l2)) <->
  In x (l1 ++ (b1, b2, vis, t3) :: l2) *)
     gen pfv3. rewrite EQ3. introv.
     assert (P0: Permutation ((b1, b2, vis, t3) :: l1 ++ l2)(l1 ++ (b1, b2, vis, t3) :: l2)).
     specialize Permutation_cons_append with (l := l1) (x :=  (b1, b2, vis, t3)) as P1.
     assert (EQ2: ((b1, b2, vis, t3) :: l1 ++ l2 =
                   ((b1, b2, vis, t3) :: l1 )++l2))...
     assert (EQ4: l1 ++ (b1, b2, vis, t3) :: l2 =
                  (l1 ++ (b1, b2, vis, t3) :: nil) ++ l2).
     erewrite cons_app,<-app_assoc...
     erewrite EQ2,EQ4;
       eapply Permutation_app...
     intros; split; try eapply Permutation_in...
     try eapply Permutation_sym...
     

    
     eapply IHLTS with (pf1 := pfv') (pf2 := pfv2)(pf := pfv3') (nd_pf := nd_pfv3') in nd_pfv2; clear IHLTS; try assumption.
     destruct nd_pfv2 as (x1 &x2 &y1 &y2 &tt &[A | [B | [C | D]]]).
     

     intuition;
       subst a; destruct H as (DIFF1 &DIFF2).
     exists x1 x2 y1 y2 tt.
     left; subst; intuition.
     inverts H4 as IN4;
       try eapply in_app_iff in IN4  as
         [IN5 | IN6];
       try econstructor;
       try eapply in_app_iff...
     right...
     inv IN6 as [ABS | IN7];try inv ABS; try contradiction...
     repeat right...
     inverts H5 as INB;
       try eapply in_app_iff in INB  as [IN6 | IN7];
       econstructor; eapply in_app_iff.
     left...
     try inv IN7 as [ABS | IN8]; try inv ABS; try contradiction;
       repeat  right...
     
     destruct B as (EQ2& m &p2&tt2& B);
       intuition;
        subst a; destruct H as (DIFF1 &DIFF2).
     exists x1 x2 y1 y2 tt; right;left; intuition.
     exists m p2 tt2; intuition...
     subst g;
       inverts H2 as IN4;
       try eapply in_app_iff in IN4  as
         [IN5 | IN6];
       try econstructor;
       try eapply in_app_iff...
     right...
     inv IN6 as [ABS | IN7];try inv ABS; try contradiction...
     repeat right...
     subst;
       inverts H4 as INB;
       eapply in_app_iff in INB as [IN8 | IN9];
       econstructor; try eapply in_app_iff...
     inv IN9 as [ABS | IN7];try inv ABS; try contradiction...
     repeat right...
     
     
      intuition;
       subst a; destruct H as (DIFF1 &DIFF2).
     exists x1 x2 y1 y2 tt; right;right;  left; intuition.
     subst g;
       inverts H4 as INB;
        try eapply in_app_iff in INB  as
         [IN5 | IN6];
       try econstructor;
       try eapply in_app_iff...
     right...
     inv IN6 as [ABS | IN7];try inv ABS; try contradiction...
     repeat right...

     subst g3;
       inverts H5 as INB;
       try  eapply in_app_iff in INB as [IN6 | IN7];econstructor; eapply in_app_iff...
     inv IN7 as [ABS | IN8];try inv ABS; try contradiction...
     repeat right...
     
     intuition;
        subst a; destruct H as (DIFF1 &DIFF2).
     exists x1 x2 y1 y2 tt; repeat right; intuition.
      subst g; inverts H4 as IN4;
       try eapply in_app_iff in IN4  as
         [IN5 | IN6];
       try econstructor;
       try eapply in_app_iff...
     inv IN6 as [ABS | IN7];try inv ABS; try contradiction...
     repeat right...
     inverts H5 as INB;
       subst g3;
       try eapply in_app_iff in INB as [IN6 | IN7];
       econstructor; try eapply in_app_iff... 
      inv IN7 as [ABS | IN8];try inv ABS; try contradiction...
      repeat right...

       simpl in NDSL;
      try eapply no_dup_distr in NDSL;
         intuition.

       subst g;
         simpl in *;
         eapply incl_app_inv in INCL as [INCL _];
         rewrite hid_proj_app,domain_distr in *;
         simpl in *;
         introv IN.
       assert (DIFF: a0<> (b1, b2)).
       intros ABS; subst;
         try eapply disjoint_absurd...
       eapply INCL,in_app_iff in IN; try destruct IN as [INH1 |INH2];
         try eapply in_app_iff;
         try inv INH2;
         try contradiction...

       eapply wf_res...
     
     eapply max_sl_nu in MAX.
     move MAX at bottom; subst g;
       rewrite domain_distr in *;
       simpl in MAX...

    (*~ (exists g' : typeEnv, lts (l1 ++ (b1, b2, vis, t3) :: l2) p a g' p' nd_pfv3')*)
     assert (AX := H1); clear H1; intros (g' &ABS).
     assert (LEM: forall x t g p g' pf,
                In (x, vis, t) g ->
                lts g p a g' p' pf ->
              exists t',
                In (x, vis, t') g').
     introv INLM LTSLM.
     assert (FYP: flagOf g'0 x vis).
     destruct x; eapply lts_flagOf_vis_entry...
     inv FYP; eexists...
     assert (ABS2 := ABS);
     eapply LEM with (x := (b1, b2)) in ABS2 as (r &IN');
     try eapply in_split in IN' as (k1 &k2 &EQ'); clear LEM...
     subst g'.

     
     assert (HD:  lts g3
                      (dNu b1 b2 p) a (k1 ++ (b1, b2, hid, r) :: k2)
                      (dNu  b1 b2 p') nd_pf).
     subst g3; eapply hide...

     elim AX.
     eexists...

     eapply in_app_iff; right...

     eauto.
     eauto.
     
     intros ISUN; destruct ISUN as (p3 &tt &EQ); subst t3.
     assert (IN3' := IN3).
     eapply tsuper_payload with (pf1 := pf1) (pf2 :=pf2) (pf := pf3) in IN3' as (p1 &TYP1);
       try inverts TYP1 as IN1; try assumption.
     assert (t = Chan un p1 tt).
     eapply in_isMap with (g := g); subst g...
     try eapply in_app_iff; try right...
     subst t.
     eapply tsuper_payload_r with (pf1 := pf1) (pf2 :=pf2) (pf := pf3) in IN3 as (p2 &TYP2);
       try inverts TYP2 as IN2; try assumption.
     assert (t2 =  Chan un p2 tt).
     eapply in_isMap with (g := g2)...
     subst t2.
     inv TYP3; eapply split_plus_un with (pf1 := pf1) (pf2 :=pf2) (pf3 := pf3)
                               (p1 := p1) (p2 := p2) (p3 := p3)in IN1;
       intuition; subst; try assumption...

     Unshelve.
     all:eauto.
     

Qed.

