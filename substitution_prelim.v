Require Import
        Bool List Lia PeanoNat Program.Equality
        ListAddOns Max RemoveEntry Domain
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
        (*split_existential_2 *)
        type_checking_1
        lts_no_dup 
        proposition27
        disjoint_newEntries
	tc_prelim
        split_cons_remove
        tc_premises2
        type_system_rules.

Require Import CpdtTactics LibTactics.

Require Import Coq.Logic.Classical_Prop.

Import ListNotations.

(********* 2DO: CHECK ALL DUPLICATED LEMMAS ********)


#[global] Hint Resolve   split_comm.
#[global] Hint Constructors cons.
#[global] Hint Constructors type_sub.
#[global] Hint Constructors type_plus.

    
 
  
  Lemma in_vis_ill_proj: forall a1 a2 f t g,
      In (a1, a2, f, t) g ->
      f <> hid ->
      In (a1, a2, f, t) (vis_proj g ++ ill_proj g).
  Proof with eauto.
    introv IN DIFF; eapply in_split in IN as (l1 &l2 &IN); subst;
      erewrite  proj_distr...
    erewrite  proj_distr...
    destruct f; try contradiction.
    repeat (eapply in_app_iff; right); econstructor...
    eapply in_app_iff; left; eapply in_app_iff; right; econstructor...
  Qed.
             
Lemma no_dup_vis_ill_proj: forall b1 b2 t g,
    NoDup (domain g) ->
    NoDup (domain
       ((vis_proj
          ((b1, b2, vis, t)
           :: removeEntry (b1, b2) g)) ++
        ill_proj
         (removeEntry (b1, b2)  g))).
Proof with eauto using not_disjoint,vis_proj_in,ill_proj_in, proj_in.
  introv nd_pf. rewrite domain_distr,no_dup_iff; intuition.
  - eapply no_dup_vis_proj,no_dup_cons_removeEntry...
  - apply Peirce; intros ABS.
    assert (ABS2: exists x,
               In x (domain (vis_proj ((b1, b2, vis, t) :: removeEntry (b1, b2) g))) /\
               In x  (domain (ill_proj (removeEntry (b1, b2) g))))...
    destruct ABS2 as ([a1 a2] &ABS1 &ABS2).
      eapply in_domain_in_g in ABS1 as (ff1 &tt1 &ABS1);
      eapply in_domain_in_g in ABS2 as (ff2 &tt2 &ABS2).
      assert (ff1 = vis)...
      assert (ff2 = ill)...
      subst.
      eapply proj_in in ABS1;
            eapply proj_in in ABS2...
      inv ABS1; try inv H.
      assert (~ In (a1, a2, ill, tt2) (removeEntry (a1, a2) g)).
      eapply no_dup_not_in_removeEntry...
      contradiction.
      assert (ill = vis).
      eapply flag_of_map with (x := (a1, a2)) (g := removeEntry (b1, b2) g)...
      discriminate.
Qed.

Lemma in_vis_proj: forall a1 a2 t g,
    In (a1, a2, vis, t) g->
    In (a1, a2, vis, t) (vis_proj g).
Proof with eauto.
  intros. 
  eapply in_split in H as (l1 &l2 &IN); subst.
  erewrite proj_distr. erewrite in_app_iff; right;simpl...
  left...
Qed.


Lemma in_ill_proj: forall a1 a2 t g,
    In (a1, a2, ill, t) g->
    In (a1, a2, ill, t) (ill_proj g).
Proof with eauto.
  intros. 
  eapply in_split in H as (l1 &l2 &IN); subst.
  erewrite proj_distr,in_app_iff; right;simpl...
Qed.


#[global] Hint Constructors cons.



Lemma gcons_removeEntry: forall a1 a2 g pf pf1,
    cons g pf ->
    cons (removeEntry (a1, a2) g) pf1.
Proof with eauto using isMap_removeEntry.
  introv CONS;
  dependent induction g;
    try destruct a as [[[b1 b2] ff1] tt1].
  eauto.
  assert (CONS2 :=CONS).
  assert (pf2 : isMap g). eapply isMap_cons...
  eapply gcons_cons with (pf := pf2) in CONS2 as K;
      eapply IHg in K as IH;
      gen pf1; simpl;
        case_eq (pair_eq (b1, b2) (a1, a2));
        try intros PEQ; intros.
    eauto.
    assert (EQ: pair_eq (b1, b2) (b1, b2) = true).
    eapply pairEq_eq...
    assert (pf3: isMap (removeEntry (b1, b2) ((b1, b2, ff1, tt1) :: removeEntry (a1, a2) g))).
   simpl; rewrite EQ...
    destruct tt1; try destruct m.
    + destruct p.
      * eapply Co_lin with (n := (b1, b2)) (pf' := pf3). simpl... 
        gen pf3; simpl; rewrite EQ; intros...
      * assert (inp = empty).
        eapply cons_lin with (a1 := b1) (a2 := b2) (g := (b1, b2, ff1, Chan lin inp tt1) :: g)... discriminate.
      * assert (out = empty).
        eapply cons_lin with (a1 := b1) (a2 := b2) (g := (b1, b2, ff1, Chan lin out tt1) :: g)... discriminate.
      * assert (io = empty).
        eapply cons_lin with (a1 := b1) (a2 := b2) (g := (b1, b2, ff1, Chan lin io tt1) :: g)... discriminate.
    + eapply Co_un with (n := (b1, b2)) (pf' := pf3). simpl... 
        gen pf3; simpl; rewrite EQ; intros...
    +  eapply Co_top with (n := (b1, b2)) (pf' := pf3). simpl... 
       gen pf3; simpl; rewrite EQ; intros...
       Unshelve.
       assert (pf' := pf); eapply isMap_cons in pf'...
Qed.

        
Lemma vis_proj_removeEntry: forall g b1 b2 (nd_pf : NoDup (domain g)),
    vis_proj (removeEntry (b1, b2) g) =
    removeEntry (b1, b2) (vis_proj g).
Proof with eauto using  proj_in.
  intros; dependent induction g;
    try destruct a as [[[a1 a2] ff] tt]...
  case_eq (pair_eq (a1, a2) (b1, b2)); introv EQ; simpl;
    try rewrite EQ; destruct ff...
  - try erewrite removeEntry_idempot; try intros ABS...
    assert (In (b1,b2) (domain g)).
    eapply in_domain_in_g in ABS as (f &t &ABS)...
    rewrite <-pairEq_eq in EQ; inv EQ; eapply NoDup_cons_iff in nd_pf; intuition.
  - try erewrite removeEntry_idempot; try intros ABS...
    assert (In (b1,b2) (domain g)).
    eapply in_domain_in_g in ABS as (f &t &ABS)...
    rewrite <-pairEq_eq in EQ; inv EQ; eapply NoDup_cons_iff in nd_pf; intuition.
  - simpl; try rewrite EQ...
  - simpl; try rewrite EQ,IHg...
Qed.

Lemma ill_proj_removeEntry: forall g b1 b2 (nd_pf : NoDup (domain g)),
    ill_proj (removeEntry (b1, b2) g) =
    removeEntry (b1, b2) (ill_proj g).
Proof with eauto using  proj_in.
  intros; dependent induction g;
    try destruct a as [[[a1 a2] ff] tt]...
  case_eq (pair_eq (a1, a2) (b1, b2)); introv EQ; simpl;
    try rewrite EQ; destruct ff...
  - try erewrite removeEntry_idempot; try intros ABS...
    assert (In (b1,b2) (domain g)).
    eapply in_domain_in_g in ABS as (f &t &ABS)...
    rewrite <-pairEq_eq in EQ; inv EQ; eapply NoDup_cons_iff in nd_pf; intuition.
  - simpl; try rewrite EQ...
  - try erewrite removeEntry_idempot; try intros ABS...
    assert (In (b1,b2) (domain g)).
    eapply in_domain_in_g in ABS as (f &t &ABS)...
    rewrite <-pairEq_eq in EQ; inv EQ; eapply NoDup_cons_iff in nd_pf; intuition.
 
  - simpl; try rewrite EQ,IHg...
Qed.

Ltac arewrite tac := erewrite tac; try assumption.
  
Lemma gcons_vis_proj_add :
  forall b1 b2 p g1 f s pf1 pf2,
    NoDup (domain g1) ->
    cons (vis_proj g1) pf1 ->
    cons (vis_proj ((b1, b2, f, Chan un p s) :: removeEntry (b1, b2) g1)) pf2.
Proof with eauto.
  intros. 
  revert dependent pf2;destruct f; simpl.
  arewrite vis_proj_removeEntry;
  intros; eapply gcons_removeEntry...
  arewrite vis_proj_removeEntry;
  intros; eapply gcons_removeEntry...
  intros.
  assert (pf' : isMap (removeEntry (b1, b2) ((b1, b2, vis, Chan un p s) :: vis_proj (removeEntry (b1, b2) g1)))).
  eapply isMap_cons in pf2.
  simpl; erewrite pairEq_eq_true...
  eapply Co_un with (pf' := pf').
  try econstructor...
  revert dependent pf';simpl. erewrite pairEq_eq_true.
  arewrite vis_proj_removeEntry;
  intros; eapply gcons_removeEntry...
Qed.


Lemma gcons_vis_proj_addT :
  forall b1 b2 g1 f pf1 pf2,
    NoDup (domain g1) ->
    cons (vis_proj g1) pf1 ->
    cons (vis_proj ((b1, b2, f, Top) :: removeEntry (b1, b2) g1)) pf2.
Proof with eauto.
  intros. 
  revert dependent pf2;destruct f; simpl.
  arewrite vis_proj_removeEntry;
  intros; eapply gcons_removeEntry...
  arewrite vis_proj_removeEntry;
  intros; eapply gcons_removeEntry...
  intros.
  assert (pf' : isMap (removeEntry (b1, b2) ((b1, b2, vis, Top) :: vis_proj (removeEntry (b1, b2) g1)))).
  eapply isMap_cons in pf2.
  simpl; erewrite pairEq_eq_true...
  eapply Co_top with (pf' := pf').
  try econstructor...
  revert dependent pf';simpl. erewrite pairEq_eq_true.
  arewrite vis_proj_removeEntry;
    intros; eapply gcons_removeEntry...
Qed.

Lemma gcons_vis_proj_addL :
  forall b1 b2 g1 f s pf1 pf2,
    NoDup (domain g1) ->
    cons (vis_proj g1) pf1 ->
    cons (vis_proj ((b1, b2, f, Chan lin empty s) :: removeEntry (b1, b2) g1)) pf2.
Proof with eauto.
   intros. 
  revert dependent pf2;destruct f; simpl.
  arewrite vis_proj_removeEntry;
  intros; eapply gcons_removeEntry...
  arewrite vis_proj_removeEntry;
  intros; eapply gcons_removeEntry...
  intros.
  assert (pf' : isMap (removeEntry (b1, b2) ((b1, b2, vis, Chan lin empty s) :: vis_proj (removeEntry (b1, b2) g1)))).
  eapply isMap_cons in pf2.
  simpl; erewrite pairEq_eq_true...
  eapply Co_lin with (pf' := pf').
  try econstructor...
  revert dependent pf';simpl. erewrite pairEq_eq_true.
  arewrite vis_proj_removeEntry;
    intros; eapply gcons_removeEntry...
Qed. 

Lemma gcons_ill_proj_add :
  forall b1 b2 p g1 f s pf1 pf2,
    NoDup (domain g1) ->
    cons (ill_proj g1) pf1 ->
    cons (ill_proj ((b1, b2, f, Chan un p s) :: removeEntry (b1, b2) g1)) pf2.
Proof with eauto.
intros. 
  revert dependent pf2;destruct f; simpl.
  arewrite ill_proj_removeEntry;
    intros; eapply gcons_removeEntry...
   intros.
  assert (pf' : isMap (removeEntry (b1, b2) ((b1, b2, ill, Chan un p s) :: ill_proj (removeEntry (b1, b2) g1)))).
  eapply isMap_cons in pf2.
  simpl; erewrite pairEq_eq_true...
  eapply Co_un with (pf' := pf').
  try econstructor...
  revert dependent pf';simpl. erewrite pairEq_eq_true.
  arewrite ill_proj_removeEntry;
  intros; eapply gcons_removeEntry...
  arewrite ill_proj_removeEntry.
  intros; eapply gcons_removeEntry...
Qed. 

Lemma gcons_ill_proj_addT :
  forall b1 b2 g1 f pf1 pf2,
    NoDup (domain g1) ->
    cons (ill_proj g1) pf1 ->
    cons (ill_proj ((b1, b2, f, Top) :: removeEntry (b1, b2) g1)) pf2.
Proof with eauto.
 intros. 
  revert dependent pf2;destruct f; simpl.
  arewrite ill_proj_removeEntry;
    intros; eapply gcons_removeEntry...
  intros.
  assert (pf' : isMap (removeEntry (b1, b2) ((b1, b2, ill, Top) :: ill_proj (removeEntry (b1, b2) g1)))).
  eapply isMap_cons in pf2.
  simpl; erewrite pairEq_eq_true...
  eapply Co_top with (pf' := pf').
  try econstructor...
  revert dependent pf';simpl. erewrite pairEq_eq_true.
  arewrite ill_proj_removeEntry;
    intros; eapply gcons_removeEntry...
  arewrite ill_proj_removeEntry;
    intros; eapply gcons_removeEntry...
  Qed.
  

Lemma gcons_ill_proj_addL :
  forall b1 b2 g1 f s pf1 pf2,
    NoDup (domain g1) ->
    cons (ill_proj g1) pf1 ->
    cons (ill_proj ((b1, b2, f, Chan lin empty s) :: removeEntry (b1, b2) g1)) pf2.
Proof with eauto.
    intros. 
  revert dependent pf2;destruct f; simpl.
  arewrite ill_proj_removeEntry;
  intros; eapply gcons_removeEntry...
  intros.
  assert (pf' : isMap (removeEntry (b1, b2) ((b1, b2, ill, Chan lin empty s) :: ill_proj (removeEntry (b1, b2) g1)))).
  eapply isMap_cons in pf2.
  simpl; erewrite pairEq_eq_true...
  eapply Co_lin with (pf' := pf').
  try econstructor...
  revert dependent pf';simpl. erewrite pairEq_eq_true.
  arewrite ill_proj_removeEntry;
    intros; eapply gcons_removeEntry...
  arewrite ill_proj_removeEntry;
    intros; eapply gcons_removeEntry...
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
  try match goal with
  | [ TR : type_remove (Chan un ?p _) _ _ |-
    exists _, type_remove ?t1 _ _] =>
    exists t1;
      try eapply type_remove_un in TR;
      try eapply type_remove_entry;
      unfold type_remove;
      intuition; subst;
    try destruct p1; simpl; econstructor
  | _ => easy
  end.
Qed.
  

Lemma pol_cup_type_sub:
  forall (p q p' : pol) (t : piType),
    pol_cup p q = p' -> type_sub (Chan un p t) (Chan un p' t).
Proof with eauto.
  intros; destruct p, q, p'; try inversion H...
Qed.

#[global] Hint Resolve pol_cup_type_sub.

Lemma type_plus_type_sub:
  forall s1 s s2,  type_plus s1 s s2 ->
                   type_sub s1 s2.
Proof with eauto.
  intros t1 t2 t TP. dependent induction TP...
Qed.

  Lemma plus_sub_exists_2:
  forall t s r1 r : piType,
    type_plus t s r1 ->
    type_sub r1 r ->
    exists s1 : piType, type_plus t s1 r.
  Proof with eauto.
    introv TP TS;
      destruct t, r1, r;
      try destruct m; inversion TP;
        inversion TS;
        inversion TP;
        try inversion H15;
        subst;
        try discriminate...
    - assert (p = empty).
      destruct p, p3; inversion H7; subst; try discriminate...
      exists (Chan un p1 r); subst;econstructor...
    - assert (EQ: p = empty \/ p = inp).
      destruct p, p3; inversion H7; subst; try discriminate...
      destruct EQ; subst...
      exists (Chan un io r); econstructor...
      exists (Chan un out r); econstructor...
    - assert (EQ: p = empty \/ p = out).
      destruct p, p3; inversion H7; subst; try discriminate...
      destruct EQ; subst...
      exists (Chan un io r); econstructor...
      exists (Chan un inp r); econstructor...
  Qed.
    


#[global] Hint Resolve   split_comm.
#[global] Hint Constructors cons.
#[global] Hint Constructors type_sub.
#[global] Hint Constructors type_plus.


Lemma type_plus_distr2: forall   t r1 s1 s2 s,
    type_plus t r1 s1 ->
    type_plus s1 s2 s ->
    exists r2, type_plus r1 s2 r2.
Proof with eauto.
  intros t r1 s1 s2 s TP1 TP2. 
  destruct s1. destruct m, p; inversion TP2;inversion H3;subst;inversion TP1; try inversion H2; subst...
  inversion TP1; inversion TP2; subst...
Qed.

