Require Import
        Bool List Lia PeanoNat Program.Equality
        ListAddOns Max Domain RemoveEntry NewEntries Replication
        header
        operations pi_syntax 
        pairEq type_system
        semantics  
        type_operations_1 
        split_exists_neutral
        sub_split
        no_dup_split_no_dup
        proposition27
        split_existential 
        split_not_exists
        split_operations
        type_checking_0
        lts_operations 
        split_operations_2 
        split_operations_3
        split_existential_2 
        type_checking_1
        lts_no_dup 
        proposition27
        disjoint_newEntries
        tc_prelim
        tc_substitution
        type_system_rules
        tc_dep_relabel_premises
        tc_premises_4
        tc_premises_5
        tc_premises_6
        substitution_prelim
        tc_dep_relabel_premises_2
        typeCheck_dep_relabel1
        sne_premises.

Require Import CpdtTactics LibTactics.


Require Import Coq.Logic.Classical_Prop.




Import ListNotations.


Lemma in_hid_proj: forall a t g,
    In (a, hid, t) g -> In (a, hid, t) (hid_proj g).
Proof with eauto.
  introv IN; induction g;
    inv IN; destruct a; simpl; intuition;
      try destruct b0; try right...
Qed.
#[global] Hint Constructors NoDup.

Lemma nin_illEProj: forall a1 a2 g l,
  ~In (a1, a2) (domain g) ->
  In (a1, a2) (domain (illEProj g l)) -> False.
Proof with eauto.
  introv NIN ABS;
    eapply in_domain_in_g in ABS as (f &t &ABS);
    assert (INCL: incl (illEProj g l) (illECast g)) by eapply incl_illEP_illEC;
    unfold incl in INCL; specialize INCL with (a1, a2, f, t);
      intuition;
      eapply in_g_in_domain in H;
      erewrite illEC_eq_domain in *;
      try contradiction.
Qed.
  
Lemma NoDup_illEProj: forall g l,
    NoDup (domain g) -> NoDup (domain (illEProj g l)).
Proof with eauto using nin_illEProj.
  introv ND; induction g; simpl; try destruct a as [[[a1 a2] f] t].
  - eauto.
  - simpl in *; eapply NoDup_cons_iff in ND; intuition;
      try destruct f; try destruct (In2 (a1, a2) l );
                           simpl; try econstructor;
        try intros ABS...
Qed.

Lemma illEProj_app:  forall l1 l2 l,
    illEProj (l1 ++ l2) l=
    illEProj l1 l ++ illEProj l2 l.
Proof with eauto.
  intros; induction l1; simpl;
    try destruct a as [[[a1 a2] f] t];
    try destruct f;
    try destruct ( In2 (a1, a2) l);
    try rewrite   IHl1...
Qed.

Lemma illEProj_inv:  forall a1 a2 f t g l,
    In (a1, a2, f, t) (illEProj g l) ->
    In (a1, a2) l /\
    exists t',
      In (a1, a2, hid, t') g /\
      cast (a1,a2,hid,t')=(a1, a2, f, t).
  Proof with eauto.
    intros; dependent induction g;
      try destruct a as [[[b1 b2] ff] tt];
      try rewrite cons_app, illEProj_app,in_app_iff in H; inv H;
        try destruct H as (t1 &H);
         repeat simpl in *;
          case_eq (In2 (b1, b2) l); intros IN;
            try rewrite IN in *.
    - destruct ff; inv H0; inv H;
        intuition;
        try exists tt...
                   - destruct ff; inv H0...
                   - eapply IHg in H0; intuition... destruct H1 as (t' &IN1); exists t'; intuition. 
                   - eapply IHg in H0; intuition... destruct H1 as (t' &IN1); exists t'; intuition.
Qed.    
    
Lemma disjoint_map_illEProj : forall p g f M (nd_pf : NoDup (domain g)),
    sl_pos p ->
    max (domain g) <= M ->
    f = (fun x : name * name * flag * piType =>
            let (y, t) := x in
            let (y0, ff) := y in let (a1, a2) := y0 in if In2 (a1, a2) (secLabs p) then (a1, a2 +  M, ff, t) else cast x) ->
  disjoint (domain (map f g)) (domain (illEProj g (secLabs p))).
Proof with eauto using incl_illEP_illEC.
  introv nd_pf POS MAX Heqf. 
  apply Peirce; intros.
  assert (ABS: exists x,
             In x (domain ( (map f g))) /\
             In x (domain (illEProj g (secLabs p)))).
  eapply not_disjoint...
  destruct ABS as ((a1 &a2) &ABS1 &ABS2).
  eapply in_domain_in_g in ABS1 as (f1 &t1 &ABS1).
  eapply in_domain_in_g in ABS2 as (f2 &t2 &ABS2).
  
  erewrite in_map_iff in ABS1; destruct ABS1 as ([[[x1 x2] f'] t'] &EQ &ABS1).
  rewrite Heqf in EQ; repeat simpl in EQ.
  assert (x1 = a1 /\ x2 = a2).
  case_eq ( In2 (x1, x2) (secLabs p)); intros; rewrite H0 in *; inv EQ...
  assert (INCL: incl (illEProj g (secLabs p)) (illECast g))...
  unfold incl in INCL; specialize INCL with (a1, x2 + M, f2, t2); intuition. eapply in_g_in_domain in H1; erewrite illEC_eq_domain in *.
  eapply in_preserves_max in H1. assert (x2 = 0) by lia.
  eapply in2_implies_in in H0; unfold sl_pos, pos in POS;
    specialize POS with a1 x2; intuition.
  destruct H0; subst x1 x2.

  case_eq (In2 (a1, a2) (secLabs p)); intros ISHID; rewrite ISHID in *.
  + inv EQ; assert (M = 0) by lia;
    eapply in_g_in_domain,in_preserves_max in ABS1;
    assert (a2 = 0) by lia;
    unfold sl_pos,pos in POS; specialize POS with a1 a2;
      eapply in2_implies_in in ISHID; intuition.
  + eapply illEProj_inv in ABS2 as (IN2 &(t'' &ABS2 &_));
      eapply in_hid_proj,in_g_in_domain in ABS2; 
      erewrite in2_nIn_iff in *; contradiction. 
Qed.


#[global] Hint Resolve in_hid_proj illEProj_app.

Lemma isMap_illEProj: forall g l,
    isMap g ->
    isMap (illEProj g l).
Proof with eauto.
  introv pf.
  induction g.
  simpl...
  eapply isMap_cons in pf as pf2.
  try destruct a as [[[b1 b2]f]t];
    simpl; destruct f, t; try destruct m; try eapply IHg; try assumption; simpl;
      case_eq (In2 (b1, b2) l); intros PEQ;
        try rewrite PEQ in *;
        try eapply IHg; try assumption;
          econstructor;
          destruct H as (IN1 &IN2);
          inverts IN1 as IN1; inverts IN2 as IN2; try inv IN1; try inv IN2; try tauto;
            try eapply illEProj_inv in IN2 as K;
            intuition;
            try destruct H0 as (s &ABS &ABS2);
            try simpl in ABS2; try inv ABS2; try destruct s; try destruct m; simpl; try tauto;
              try eapply illEProj_inv in IN1 as W;
              intuition;
               try destruct H1 as (s &ABS &ABS2);
               try simpl in ABS2; try inv ABS2.

  all: simpl in *.
  try destruct s; try destruct m; simpl; try tauto.
  eapply H... 
  assert (Chan lin p t = Chan lin p0 s).
  eapply pf with (x := (b1, b2)) (f1 := hid) (f2 := hid).
  intuition. inv H0...
  assert (hid = hid /\ Chan lin p t = Chan un p0 s).
  eapply pf  with (x := (b1, b2)); intuition.
  intuition; try discriminate.
    assert (hid = hid /\ Chan lin p t = Top).
  eapply pf  with (x := (b1, b2)); intuition.
  intuition; try discriminate.
  destruct s; try destruct m; simpl in *.
   assert (Chan lin p t = Chan lin p0 s).
  eapply pf with (x := (b1, b2)) (f1 := hid) (f2 := hid).
  intuition. inv H1...
  assert (hid = hid /\ Chan lin p t = Chan un p0 s).
  eapply pf  with (x := (b1, b2)); intuition.
  intuition; try discriminate.
      assert (hid = hid /\ Chan lin p t = Top).
  eapply pf  with (x := (b1, b2)); intuition.
  intuition; try discriminate.
  eapply H...
  destruct s; try destruct m; simpl in *; try tauto;
    try eapply H...
  eapply H...
  assert (hid = hid /\ Chan un p t = Chan lin p0 s).
  eapply pf  with (x := (b1, b2)); intuition.
  intuition; try discriminate.
  assert (hid = hid /\ Chan un p t = Chan un p0 s).
  eapply pf  with (x := (b1, b2)); intuition.
  intuition.
  assert (hid = hid /\ Chan un p t = Top).
  eapply pf  with (x := (b1, b2)); intuition.
  intuition; try discriminate.
  destruct s; try destruct m; simpl in *; try tauto.
  assert (hid = hid /\ Chan un p t = Chan lin p0 s).
  eapply pf  with (x := (b1, b2)); intuition.
  intuition; try discriminate.
  assert (hid = hid /\ Chan un p t = Chan un p0 s).
  eapply pf  with (x := (b1, b2)); intuition.
  intuition.
  assert (hid = hid /\ Chan un p t = Top).
  eapply pf  with (x := (b1, b2)); intuition.
  intuition; try discriminate.
  eapply H...
    destruct s; try destruct m; simpl in *; try tauto.
  eapply H...
  assert (hid = hid /\ Top = Chan lin p s).
  eapply pf  with (x := (b1, b2)); intuition.
  intuition; try discriminate.
  assert (hid = hid /\ Top = Chan un p s).
  eapply pf  with (x := (b1, b2)); intuition.
  intuition; try discriminate.
    destruct s; try destruct m; simpl in *; try tauto.
   assert (hid = hid /\ Top = Chan lin p s).
  eapply pf  with (x := (b1, b2)); intuition.
  intuition; try discriminate.
     assert (hid = hid /\ Top = Chan un p s).
  eapply pf  with (x := (b1, b2)); intuition.
  intuition; try discriminate.
  eapply H...
Qed.

Lemma no_dup_ne_ic0 : forall g l M (nd_pfl: NoDup l) (nd_pf : NoDup (domain g)),
    pos l ->
    max (domain g) <= M ->
    incl l (domain (hid_proj g)) ->
    NoDup (domain ((newEntries g (map (fun x : name * name => (fst x, snd x + M)) l) M) ++ illECast g)).
Proof with eauto using in_eq.
  introv nd_pfl nd_pf POS MAX INCL.
  induction l; simpl;
    try rewrite illEC_eq_domain; try assumption.
  assert (POS2 := POS);
  eapply pos_cons in POS;
  eapply incl_cons_inv in INCL as (IN &INCL);
  assert (K := nd_pfl); eapply NoDup_cons_iff in K as [NIN ND];
    intuition; simpl; destruct a as [a1 a2].
  case_eq (InB (a1, a2 + M) g); intros; case_eq b; intros; subst.
  - assert (False).
    eapply inB_implies_In_2  in H0.
    eapply in_g_in_domain, in_preserves_max in H0.
    assert (a2 = 0) by lia.
    assert (In (a1, a2) ((a1, a2) :: l)). eapply in_eq.
    unfold pos in POS2; specialize POS2 with a1 a2; intuition.
    contradiction.
  - assert (EQ: a2 + M - M = a2) by lia.
    simpl; rewrite H0, EQ; clear EQ; destruct (InB (a1, a2) g );
      simpl; econstructor; try intros ABS.
    rewrite domain_distr in ABS; eapply in_app_iff in ABS as [ABS1 | ABS2].
    + eapply not_in_newEntries with (a := (a1, a2 + M)); try intros ABS; try eapply in_map_iff in ABS ...
      destruct ABS as ([x1 x2] &ABS); simpl in ABS; intuition.
      inversion H1; assert (x2 = a2 ) by lia;
      subst; intuition.
    + rewrite illEC_eq_domain in *. eapply in_domain_in_g in ABS2 as (ff &tt &ABS2); eapply in_implies_InB in ABS2; try rewrite ABS2 in *; try discriminate...
    + assumption.
Qed.

Lemma no_dup_ne_ic : forall g p nd_pf pf,
    sl_pos p ->
    typeCheck g pf p->
    NoDup (domain ((newEntries
                      g
                      (secLabs (dep_relabel p (domain g) nd_pf))
                      (max (domain g)))
                     ++
                     illECast g)).
Proof with eauto using no_dup_ne_ic0, typeCheck_no_dup.
  introv SLPOS TC; erewrite identif_seclabs_of_dep_relabel.
  eapply no_dup_ne_ic0...
  eapply typeCheck_no_dup...
  unfold incl; intros; eapply typeCheck_hid with (g := g)in H as (tt &H)...
Qed.

  #[global] Hint Resolve isMap_not_in incl_cons inB_implies_In_2.




  #[global] Hint Resolve in_removeEntry_cons_iff_2.

 

#[global] Hint Resolve incl_incl fn_disjoint_sl bv_disjoint_sl
     isMap_illEProj cons_illEProj in2_implies_in no_dup_ne_ic
     incl_hid_proj.


Lemma map_iff_newEntries : forall p g nd_pf f pfg (pf : 
                                                 incl (secLabs p) (domain (hid_proj g))),
    sl_pos p ->
    typeCheck g pfg p->
    f =
    (fun x : name * name * flag * piType =>
       let (y, t) := x in
       let (y0, f) := y in let (a1, a2) := y0 in if In2 (a1, a2) (secLabs p) then (a1, a2 + max (domain g), f, t) else cast x) ->
    sl_pos p ->
    forall x : name * name * flag * piType,
      In x (map f g ++ illEProj g (secLabs p)) <-> In x (newEntries g (secLabs (dep_relabel p (domain g) nd_pf)) (max (domain g)) ++ illECast g).
Proof with eauto. 
  introv pf SLPOS TC; intuition auto. 
  - eapply in_app_iff in H1; destruct H1 as [INM | INP].
    + rewrite in_map_iff in INM; destruct INM as [z [EQ INM]]; destruct z as [[[a1 a2] f1] t]; subst f; case_eq (In2 (a1, a2) (secLabs p)); intros; rewrite H in EQ; inversion EQ. eapply in_app_iff; left; erewrite identif_seclabs_of_dep_relabel; eapply in_newEntries.
      eauto. eauto.  subst; intuition auto; eauto. subst; eauto.
      subst; rewrite <-EQ; eapply in_app_iff; right; unfold illECast; eapply in_map...
    + eapply incl_illEP_illEC in INP; erewrite in_app_iff; right...
  -  assert (ND : NoDup (domain  (newEntries g (secLabs (dep_relabel p (domain g) nd_pf)) (max (domain g)) ++
                                             illECast g))).
   eapply no_dup_ne_ic...  
     case_eq (In2 (a, b1) (secLabs p)). intros SL.
     assert (INC: In (a, b1)  (domain (illECast g))).
     erewrite illEC_eq_domain; erewrite in2_In_iff in SL; eapply hid_proj_incl, pf...
     assert (INC2 : In (a, b1, b0, b) (illECast g)).
     eapply in_app_iff in H1; destruct H1 as [ABS | OK].
     eapply in_g_in_domain in ABS. 
     erewrite domain_distr in ND; eapply no_dup_disjoint in ND.
     eapply disjoint_absurd...
     assumption.

     eapply in_app_iff; right.
     eapply in2_implies_in in SL.
     assert (IN3: In  (a, b1) (domain (hid_proj g)))...
     assert (FYP: flagOf g (a,b1) hid)...
     unfold illECast in INC2.
     eapply in_map_iff in INC2;destruct INC2 as (x &EQ &INC2); eapply in_split in INC2 as (l1 &l2 &IN2); rewrite<-EQ,IN2.
     assert (EQ2: illEProj (l1 ++ x :: l2) (secLabs p)=
                  illEProj l1 (secLabs p)++ illEProj(x::nil) (secLabs p)++illEProj l2 (secLabs p))...
     rewrite illEProj_app,cons_app,illEProj_app... 
     rewrite EQ2,in_app_iff; right;rewrite in_app_iff; left.
     inversion FYP; subst; destruct x as [[a' f'] t'].
     assert (a' = (a, b1)).
     simpl in EQ;destruct a'; inversion EQ...
     subst.
     assert ( hid = f').
     assert (ND2 := nd_pf);
       erewrite domain_distr in ND2; simpl in ND2.
     eapply NoDup_remove_2 in ND2.
     eapply in_app_iff in H2 as [ABS | IN2].
     eapply in_g_in_domain in ABS; intuition.
     inversion IN2. inversion H;subst...
      eapply in_g_in_domain in H; intuition.
      subst f';simpl; eapply in2_In_iff in SL; rewrite SL;
        repeat simpl...
     
       
   

     intros. 
     eapply in_app_iff in H1; destruct H1 as [INN | INC].
     erewrite identif_seclabs_of_dep_relabel in INN.
     assert (LEM:
               incl (secLabs p) (domain g) ->  
               In (a, b1, b0, b)
                  (newEntries g
                              (map (fun x : name * name => (fst x, snd x + max (domain g))) (secLabs p)) (max (domain g))) ->
               In (a, b1 - max (domain g)) (secLabs p) /\
               In (a, b1 - max (domain g), b0, b) g).
     eapply inverse_newEntries...
     assert (incl (secLabs p) (domain g)). eapply incl_tran with (m := domain (hid_proj g)), hid_proj_incl... intuition.
     unfold incl in pf; specialize pf with (a, b1 - max (domain g)); eapply in_domain_in_g in pf. destruct pf as [f1 [t1 pf]].
     
     assert (ING: In (a, b1 - max (domain g), f1, t1) g).
     eapply incl_hid_proj...
     eapply in_app_iff; left; subst; eapply in_map_iff. 
     exists (a, b1 - max (domain g), f1, t1).
     assert (K1 := H3); erewrite <-in2_In_iff in K1; rewrite K1...
     rewrite Nat.sub_add. intuition auto.
     assert (EQ: f1 = b0 /\ t1 = b). eapply in_isMap... intuition auto; subst...
     eapply newEntries_gte_max...
     eauto.
     
     unfold illECast in INC. erewrite in_app_iff; left; subst f; erewrite in_map_iff in *; destruct INC as [INC IN]; destruct INC as [[[c1 c2] f2] t2]; exists (c1, c2, f2, t2); intuition auto; inversion H; subst; rewrite H2...
     Qed.

  
Lemma typeCheck_dep_relabel2: forall p g pf nd_pf pf1,
    sl_pos p ->  
    typeCheck g pf p ->
    typeCheck
      ((newEntries
          g
          (secLabs (dep_relabel p (domain g) nd_pf))
          (max (domain g)))
         ++
         illECast g)
      pf1 
      (dep_relabel p (domain g) nd_pf).
Proof with eauto using NoDup_illEProj,no_dup_ne_ic.
  intros.
 assert (NDNE: NoDup (domain ((newEntries
          g
          (secLabs (dep_relabel p (domain g) nd_pf))
          (max (domain g)))
         ++
         illECast g))).
 eapply no_dup_ne_ic...
  specialize typeCheck_dep_relabel1 with
      (p := p) (g := g) (pf := pf) (nd_pf := nd_pf)
      (l := secLabs p)
    as TCMAP.
  remember (fun x : name * name * flag * piType =>
              let (y, t) := x in
              let (y0, f) := y in
              let (a1, a2) := y0 in
              if In2 (a1, a2) (secLabs p)
              then (a1, a2 + max (domain g), f, t)
              else cast x) as f.
  assert (nd_pf2 : NoDup (domain  (map f g))).
  subst f; eapply no_dup_shift...
  apply no_dup_isMap in nd_pf2 as pf2...
  specialize TCMAP with pf2.
  assert (nd_pf3 : NoDup (domain ((map f g) ++ illEProj g (secLabs p)))).
  rewrite domain_distr,no_dup_iff; intuition.
  eapply NoDup_illEProj...
  eapply disjoint_map_illEProj with (M := max (domain g))...
  apply no_dup_isMap in nd_pf3 as pf3.
  assert (WEAK: typeCheck ((map f g) ++ illEProj  g (secLabs p))
                          pf3 (dep_relabel p (domain g) nd_pf)).
  eapply tc_premises_4.typeCheck_weak2.
  rewrite domain_distr in nd_pf3...
  eapply TCMAP...
  eauto.
  erewrite bv_dep_relabel.
  eapply disjoint_incl with (l2 := domain g)...
  eapply bv_disjoint_g...
  assert (EQ: (domain g) =
              (domain (illECast g))).
  erewrite <-illEC_eq_domain...
  rewrite EQ; unfold incl; intuition.
  eapply in_domain_in_g in H1 as (ff &tt &IN2);
    eapply in_g_in_domain,incl_illEP_illEC...

  eapply typeCheck_impl with (pf1 := pf3).
  all:eauto.
  
  eapply map_iff_newEntries...
  unfold incl; intros.
  assert (EX: exists  t, In (a, hid, t) g).
  eapply typeCheck_hid...
  destruct EX as [t EX].
  eapply in_hid_proj, in_g_in_domain in EX...
  Unshelve. 
  eauto.
Qed.


