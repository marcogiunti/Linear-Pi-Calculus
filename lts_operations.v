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
        split_not_exists
        split_operations
        split_operations_2
        type_checking_0
        type_system_rules
        split_operations_4
        disjoint_newEntries.

Require Import CpdtTactics LibTactics.
Import ListNotations.


Lemma lts_lin_input_action: forall g p a1 a2 b1 b2 g1 p' nd_pf pol t s r,
    lts g p (aIn a1 a2 b1 b2) g1 p' nd_pf ->
    typeOf g (a1, a2) (Chan lin pol t) ->
    typeOf g (b1, b2) s ->
    type_plus s t r ->
    g1 = ((a1, a2), vis, Chan lin empty t)
           :: ((b1, b2), vis, r)
           :: removeEntry (a1, a2) (removeEntry (b1, b2) g).
Proof with eauto.
  intros g p a1 a2 b1 b2 g1 p' nd_pf pol t s r
  LTS TYPa TYPb TP. 
  generalize dependent s.
  generalize dependent t.
  generalize dependent r.
  generalize dependent pol.
  dependent induction LTS.
  - intros.
    specialize IHLTS with a1 a2 b1 b2 pol r t s...
  - intros... 
    inversion TYPa. subst. 
    assert (vis = f0 /\  Chan lin inp t =  Chan lin pol t0).
    apply in_isMap with (x := (a1, a2)) (g := g)...
    intuition; inversion H6; subst...
    inversion TYPb; subst.
    assert (f = f0 /\  t1 = s).
    apply in_isMap with (x := (b1, b2)) (g := g)...
    intuition; inversion H6; subst...
    assert (t2 = r)... subst...
  - intros. 
    inversion TYPa. subst.
    assert (vis = f0 /\ Chan un pol t = Chan lin pol0 t0).
    apply in_isMap with (x := (a1, a2)) (g := g)...
    intuition; inversion H6; subst...
    inversion H7... inversion H7...
  - intros. 
     inversion TYPa. subst.
    assert (vis = f0 /\ Chan un pol t = Chan lin pol0 t0).
    apply in_isMap with (x := (a1, a2)) (g := g)...
    intuition; inversion H6; subst...
    inversion H7... inversion H7...
  - intros.
     destruct H as (DIFF1 &DIFF2).
    assert (IH :
               h' ++ (b0, b3, vis, t') :: h'' =
          (a1, a2, vis, Chan lin empty t0)
          :: (b1, b2, vis, r)
          :: removeEntry (a1, a2) (removeEntry (b1, b2) (h1 ++ (b0, b3, vis, t) :: h2))).
    eapply IHLTS...
    inversion TYPa; subst;
       try eapply in_app_iff in H as [HD|TL];
       try econstructor;
       try eapply in_app_iff...
     inversion TL as [EQ | TL2];
       try inversion EQ; subst; try contradiction.
     repeat right...
      inversion TYPb; subst;
       try eapply in_app_iff in H as [HD|TL];
       try econstructor;
       try eapply in_app_iff...
     inversion TL as [EQ | TL2];
       try inversion EQ; subst; try contradiction.
     repeat right...

     eapply typeEnv_eq_change_flag_removeEntry_app...
Qed. 
    
#[global] Hint Resolve lts_lin_input_action.


Lemma lts_inp:
  forall g p a1 a2 b1 b2 g' p' nd_pf ta tb m q t r, 
    lts g p (aIn a1 a2 b1 b2) g' p' nd_pf ->
    typeOf g (a1, a2) ta ->
    typeOf g (b1, b2) tb ->
    ta = Chan m q t ->
    type_plus tb t r ->
    ((m = lin ->
      g' = (((a1, a2), vis, Chan lin empty t)
              :: ((b1, b2), vis, r)
              :: (removeEntry (a1, a2) (removeEntry (b1, b2) g))))
     /\
       (m = un ->
        sl_pos p ->
    max (secLabs p) <= max (domain g) ->
      exists ne,
          g' = ne ++ (((b1, b2), vis, r) :: removeEntry (b1, b2) g))).
Proof with eauto.
 intros. 
 split. 
 intros. subst.
  specialize lts_lin_input_action with
     g p a1 a2 b1 b2 g' p' nd_pf q t tb r as LININP; intuition.
  intros. subst.
  specialize lts_un_input_action with
    g p a1 a2 b1 b2 g' p' nd_pf q t tb r as UNINP; eapply UNINP in H as (k &IH1 &IH2)...
Qed.
 
Lemma lts_un_output_action: forall g p a1 a2 b1 b2 g1 p' nd_pf pol t s r,
    lts g p (aOut a1 a2 b1 b2) g1 p' nd_pf ->
    typeOf g (a1, a2) (Chan un pol t) ->
    typeOf g (b1, b2) s ->
    type_remove s t r ->
    g1 = ((b1, b2), vis, r) :: removeEntry (b1, b2) g.
Proof with eauto using typeEnv_eq_change_flag_removeEntry.
  intros g p a1 a2 b1 b2 g1 p' nd_pf pol t s r
         LTS TYPa TYPb TR.
  generalize dependent s.
  generalize dependent t.
  generalize dependent r.
  generalize dependent pol.
  dependent induction LTS.
  - intros.
    specialize IHLTS with a1 a2 b1 b2 pol r t s...
  - intros.
    inversion TYPa. subst. 
    assert (vis = f /\  Chan lin out t =  Chan un pol t0).
    apply in_isMap with (x := (a1, a2)) (g := g)...
    intuition. inversion H5; subst...
  - intros.
    inversion TYPb; subst.
    assert (vis = f /\  t1 = s).
    apply in_isMap with (x := (b1, b2)) (g := g)...
    intuition; inversion H6; subst...
    inversion TYPa. subst. 
    assert (vis = f /\  Chan un out t =  Chan un pol0 t0).
    apply in_isMap with (x := (a1, a2)) (g := g)...
    intuition. inversion H7; subst...
    assert (t2 = r)... subst...
     inversion TYPa. subst. 
    assert (vis = f /\  Chan un io t =  Chan un pol0 t0).
    apply in_isMap with (x := (a1, a2)) (g := g)...
    intuition. inversion H7; subst...
    assert (t2 = r)... subst...
  - intros.
    inversion TYPb; subst.
      assert (hid = f /\  t = s).
    apply in_isMap with (x := (b1, b2)) (g := g)...
    intuition. subst.
    specialize IHLTS with
        (a1 := a1) (a2 := a2) (b1 :=b1) (b2 := b2)
        (pol := pol) (t := t0) (r := r) (s := s).
    assert (typeOf ((b1, b2, vis, s) :: removeEntry (b1, b2) g) (a1, a2) (Chan un pol t0)).
    apply typeOf_removeEntry...
    assert ( typeOf ((b1, b2, vis, s) :: removeEntry (b1, b2) g) (b1, b2) s)...
    intuition.
    unfold removeEntry in H4.
    fold removeEntry in H4...
    assert (pair_eq (b1, b2) (b1, b2) = true)...
    rewrite H3 in H4...
  - intros.
    destruct H as [DIFF1 DIFF2].
    assert (IH:  aOut a1 a2 b1 b2 = aOut a1 a2 b1 b2)...
    eapply IHLTS in IH; try eassumption.
    erewrite typeEnv_eq_change_flag_removeEntry with (h := nil),app_nil_l; try simpl...
    inverts TYPa as INa;
      eapply in_app_iff in INa as [INa | CONT]; try econstructor;
      try eapply in_app_iff;
      try inv CONT as [ABS | CONT2];
      try inv ABS;
      try contradiction...
    repeat right...
    inverts TYPb as INa;
      eapply in_app_iff in INa as [INa | CONT]; try econstructor;
      try eapply in_app_iff;
      try inv CONT as [ABS | CONT2];
      try inv ABS;
      try contradiction...
    repeat right...
Qed.
    
    Lemma lts_lin_output_action: forall g p a1 a2 b1 b2 g1 p' nd_pf pol t s r,
    lts g p (aOut a1 a2 b1 b2) g1 p' nd_pf ->
    typeOf g (a1, a2) (Chan lin pol t) ->
    typeOf g (b1, b2) s ->
    type_remove s t r ->
    g1 = ((a1, a2), vis, Chan lin empty t)
           :: ((b1, b2), vis, r)
           :: removeEntry (a1, a2) (removeEntry (b1, b2) g).
Proof with eauto.
intros g p a1 a2 b1 b2 g1 p' nd_pf pol t s r
         LTS TYPa TYPb TR.
  generalize dependent s.
  generalize dependent t.
  generalize dependent r.
  generalize dependent pol.
  dependent induction LTS.
  - intros.
    specialize IHLTS with a1 a2 b1 b2 pol r t s...
  - intros.
    inversion TYPa. subst. 
    assert (vis = f /\  Chan lin out t =  Chan lin pol t0).
    apply in_isMap with (x := (a1, a2)) (g := g)...
    intuition. inversion H5; subst...
    inversion TYPb; subst.
    assert (vis = f /\  t1 = s).
    apply in_isMap with (x := (b1, b2)) (g := g)...
    intuition. subst...
    assert (t2 = r)... subst...
  - intros.
     inversion TYPa. subst. 
    assert (vis = f /\  Chan un pol t =  Chan lin pol0 t0).
    apply in_isMap with (x := (a1, a2)) (g := g)...
    intuition. inversion H6... inversion H6...
  - intros.
    inversion TYPb; subst.
      assert (hid = f /\  t = s).
    apply in_isMap with (x := (b1, b2)) (g := g)...
    intuition. subst.
    specialize IHLTS with
        (a1 := a1) (a2 := a2) (b1 :=b1) (b2 := b2)
        (pol := pol) (t := t0) (r := r) (s := s).
    assert (typeOf ((b1, b2, vis, s) :: removeEntry (b1, b2) g) (a1, a2) (Chan lin pol t0)).
    apply typeOf_removeEntry...
    assert ( typeOf ((b1, b2, vis, s) :: removeEntry (b1, b2) g) (b1, b2) s)...
    intuition.
    unfold removeEntry in H4.
    fold removeEntry in H4...
    assert (pair_eq (b1, b2) (b1, b2) = true)...
    rewrite H3 in H4...
    - intros.
    destruct H as [DIFF1 DIFF2].
    assert (IH:  aOut a1 a2 b1 b2 = aOut a1 a2 b1 b2)...
    eapply IHLTS in IH; try eassumption.
    erewrite typeEnv_eq_change_flag_removeEntry_app... 
    inverts TYPa as INa;
      eapply in_app_iff in INa as [INa | CONT]; try econstructor;
      try eapply in_app_iff;
      try inv CONT as [ABS | CONT2];
      try inv ABS;
      try contradiction...
    repeat right...
    inverts TYPb as INa;
      eapply in_app_iff in INa as [INa | CONT]; try econstructor;
      try eapply in_app_iff;
      try inv CONT as [ABS | CONT2];
      try inv ABS;
      try contradiction...
    repeat right...
Qed.

Lemma lts_out:
  forall g p a1 a2 b1 b2 g' p' nd_pf ta tb m q t s,
    lts g p (aOut a1 a2 b1 b2) g' p' nd_pf ->
    typeOf g (a1, a2) ta ->
    ta = Chan m q t ->
    typeOf g (b1, b2) tb ->
    type_remove tb t s ->
    ((m = lin  ->
      g' = (((a1, a2), vis, Chan lin empty t)
              :: ((b1, b2), vis, s)
              :: (removeEntry (a1, a2)
                              (removeEntry (b1, b2) g)))) /\
     (m = un ->
      g' = (((b1, b2), vis, s) :: removeEntry (b1, b2) g))).
Proof.
intros. 
 split. 
 intros. subst.
 specialize lts_lin_output_action with
     g p a1 a2 b1 b2 g' p' nd_pf q t tb s as LININP; intuition.
 intros. subst.
 specialize lts_un_output_action with
     g p a1 a2 b1 b2 g' p' nd_pf q t tb s as UNINP; intuition.
Qed.   


(*Lemma lts_tau:
  forall g p a1 a2 g' p' nd_pf ta m q t,
    lts g p (aTau a1 a2) g' p' nd_pf ->
    typeOf g (a1, a2) ta ->
    ta = Chan m q t ->
    ((m = lin  ->
      g' = (((a1, a2), vis, Chan lin empty t)
              :: (removeEntry (a1, a2) g))) /\
     (m = un ->
      g' = g \/
      (exists ne,
          g' = ne ++ g /\
          isMap g'))).
Proof.
*)

Lemma typeCheck_lts_in:
  forall g1 g pf1 p a1 a2 b1 b2 g' p' nd_pf,
    typeCheck g1 pf1 p ->
    lts g p (aIn a1 a2 b1 b2) g' p' nd_pf ->
    exists m t,
      typeOf g1 (a1, a2) (Chan m inp t) \/
      typeOf g1 (a1, a2) (Chan m io t).
Proof with eauto.
  intros g1 g pf1 p a1 a2 b1 b2 g' p' nd_pf TC LTS.
  generalize dependent g.
  generalize dependent g'.
  generalize dependent p'.
  dependent induction TC.
  - intros. inversion LTS.
  - intros.  destruct n. inverts LTS as LTSIN; subst; eapply IHTC in LTSIN as (mm&tt&[LTSIN|LTSIN]); try exists mm tt...
try inverts LTSIN as IN; try inversion IN as [ABS|IN2];
try inv ABS;try econstructor...
right.

try inverts LTSIN as IN; try inversion IN as [ABS|IN2];
try inv ABS;try econstructor...
 - intros. inversion LTS. subst.
   specialize IHTC1 with p3 g' g0 nd_pf.
   intuition.
   destruct H0 as [m [t [TYP | TYP]]].
   inversion TYP; subst.
   apply tsub_in with g1 g2 g pf1 pf2 pf a1 a2 f m t in H0...
   inversion TYP; subst.
 apply tsub_io with g1 g2 g pf1 pf2 pf a1 a2 f m t in H0...
 - intros. inversion LTS.
 - intros. inversion LTS.
 - intros. clear IHTC. 
   destruct u. simpl in LTS. 
   inversion H. inversion H3. subst...
   inversion LTS; subst.
   exists lin. exists t. left... 
   exists lin. exists t. left...
   subst.
   inversion LTS; subst.
   exists lin. exists t...
   exists lin. exists t...
 - intros. clear IHTC.
   assert (u = (a1, a2)).
   destruct u. simpl in LTS.   
   inversion LTS. all:eauto.
   subst. 
   exists un t. intuition.
   subst... subst. apply T_Entry in H0. intuition.
 - intros. clear IHTC.
   assert (u = (a1, a2)).
   destruct u. simpl in LTS.   
   inversion LTS. all:eauto.
   subst. 
   exists un t. intuition.
   subst... subst. apply T_Entry in H0. intuition.
Qed.


Lemma typeCheck_lts_out:
  forall g1 g pf1 p a1 a2 b1 b2 g' p' nd_pf,
    typeCheck g1 pf1 p ->
    lts g p (aOut a1 a2 b1 b2) g' p' nd_pf ->
    exists m t,
      typeOf g1 (a1, a2) (Chan m out t) \/
      typeOf g1 (a1, a2) (Chan m io t).
Proof with eauto.
  intros g1 g pf1 p a1 a2 b1 b2 g' p' nd_pf TC LTS.
  generalize dependent g.
  generalize dependent g'.
  generalize dependent p'.
  dependent induction TC.
 - intros. inversion LTS.
 - intros.  destruct n. inversion LTS; subst.
   specialize IHTC with p' g' ((b1, b2, vis, t0) :: removeEntry (b1, b2) g0) pf2. intuition.
   destruct H0 as [m [t1 [TYP | TYP]]].
   inversion TYP. subst.
   apply in_app_iff with (l := (b1, b2, vis, t) :: nil) in H0 as [HEAD | TAIL].
   inversion HEAD; inversion H0; subst...
   assert ( In (a1, a2, f, Chan m out t1) g).
   apply in_removeEntry with (y := (b1, b2))...
   exists m. exists t1. left...
   inversion TYP; subst. 
   apply in_app_iff with (l := (b1, b2, vis, t) :: nil) in H0 as [HEAD | TAIL].
   inversion HEAD; inversion H0; subst...
   assert ( In (a1, a2, f, Chan m io t1) g).
   apply in_removeEntry with (y := (b1, b2))...

   exists m. exists t1. right...

   inverts LTS as IN LTSIN; subst;
     try eapply IHTC in LTSIN as (mm&tt&[LTSIN|LTSIN]); try exists mm tt...
try inverts LTSIN as IN2; try inversion IN2 as [ABS2|IN3];
try inv ABS2;try econstructor...
right.

try inverts LTSIN as IN2; try inversion IN2 as [ABS2|IN3];
  try inv ABS2;try econstructor...

 try eapply IHTC in IN as (mm&tt&[LTSIN2|LTSIN2]); try exists mm tt...
try inverts LTSIN2 as IN2; try inversion IN2 as [ABS2|IN3];
try inv ABS2;try econstructor...
right.

try inverts LTSIN2 as IN2; try inversion IN2 as [ABS2|IN3];
try inv ABS2;try econstructor...
   
 - intros. inversion LTS. subst.
   specialize IHTC1 with p3 g' g0 nd_pf.
   intuition.
   destruct H0 as [m [t [TYP | TYP]]].
   inversion TYP; subst.
   apply tsub_out with g1 g2 g pf1 pf2 pf a1 a2 f m t in H0...
   inversion TYP; subst.
 apply tsub_io with g1 g2 g pf1 pf2 pf a1 a2 f m t in H0...
 - intros. clear IHTC. 
   destruct u. unfold fst at 1 in LTS. unfold snd at 1 in LTS.
   inversion H; inversion H3. subst...
   inversion LTS; subst.
   exists lin. exists t. left...
   exists lin. exists t. left...
   subst.
   inversion LTS; subst.
   exists lin. exists t...
   exists lin. exists t...
 - intros. clear IHTC.
   destruct u, v; simpl in LTS. inversion LTS. subst.
   exists un. exists t.
   intuition. subst... subst. left...
   exists un. exists t. subst.
   destruct H as [IO | OUT].
   subst. right...
   subst. left...
 - intros. inversion LTS. 
 - intros. inversion LTS.
 - intros. inversion LTS.
Qed.

Lemma typeCheck_lts_out_payload:
  forall g1 g pf1 p a1 a2 b1 b2 g' p' nd_pf,
    typeCheck g1 pf1 p ->
    lts g p (aOut a1 a2 b1 b2) g' p' nd_pf ->
    ( flagOf g1 (b1, b2) vis \/
      flagOf g1 (b1, b2) hid).
Proof with eauto.
  intros  g1 g pf1 p a1 a2 b1 b2 g' p' nd_pf TC LTS.
  generalize dependent g.
  generalize dependent g'.
  generalize dependent p'.
  dependent induction TC.
  - intros. inversion LTS.
  - intros.  destruct n. inversion LTS; subst.
    right...
    inverts LTS as LTSIN; subst...
    try eapply IHTC in LTSIN as FYP; destruct  FYP as [FYP1 | FYP2].
try inverts FYP1 as IN2; try inversion IN2 as [ABS2|IN3];
try inv ABS2;try econstructor...
unfold notHidden in *; intuition.
right.
try inverts FYP2 as IN2; try inversion IN2 as [ABS2|IN3];
try inv ABS2;try econstructor...

  -  intros. inversion LTS. subst.
     specialize IHTC1 with p3 g' g0 nd_pf.
     intuition.
     left.
     specialize flag_of_split_l with g1 g2 g pf1 pf2 pf (b1, b2) as FSL. intuition.
     right.
     specialize flag_of_split_l with g1 g2 g pf1 pf2 pf (b1, b2) as FSL. intuition.   
  -  intros. clear IHTC. 
     destruct u. destruct v. unfold fst at 1 in LTS. unfold snd at 1 in LTS.
     inversion H; inversion H3. subst.
     inversion LTS; subst.
     left...
     left...
     inversion LTS; subst.
     left...
     left...
  - intros. clear IHTC. 
     destruct u. destruct v. unfold fst at 1 in LTS. unfold snd at 1 in LTS.
     inversion H; inversion H3. subst.
     inversion LTS; subst.
     left...
     left...
     inversion LTS; subst.
     left...
     left...
  - intros. inversion LTS.
  - intros. inversion LTS. 
  - intros. inversion LTS.
Qed.
