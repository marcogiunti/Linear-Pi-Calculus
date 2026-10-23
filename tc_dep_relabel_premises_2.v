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
        split_cons_remove.

Require Import CpdtTactics LibTactics.


Import ListNotations.



#[global] Hint Resolve typeCheck_rewrite_pf in2_false_illECast
     pos_cons pos_remove in_iff_swap
     map_is_map var_not_in_map max_map
     in_g_in_domain.

Lemma app_cons {A}: forall a (l : list A),
    [a] ++ l = a :: l.
Proof. eauto. Qed.


  
(* Lemma disjoint_remove_inv : forall n n0 l1 l2,
    disjoint l1 l2 ->
    disjoint l1 (List.remove nat_pair_eq_dec (n, n0) l2).
Proof with eauto.
  introv DIS; induction l1; try econstructor;
    inv DIS; try intros ABS;
      try eapply in_remove in ABS; intuition...
Qed.

Lemma disjoint_remove_swap: forall n n0 l1 l2,
    disjoint (List.remove nat_pair_eq_dec (n, n0) l1) l2 ->
    disjoint l1 (List.remove nat_pair_eq_dec (n, n0) l2).
Proof with eauto.
  introv DIS; induction l1; try econstructor;
    case_eq (nat_pair_eq_dec (n, n0) a); intros; subst; simpl in DIS;
      try rewrite H in *;
      try eapply in_remove in H0;
      try eapply disjoint_l_cons in DIS;
      intuition.
  Qed. *)
  
#[global] Hint Resolve split_comm.

#[global] Hint Resolve gcons_cons.

Lemma cons_vis_proj_map:
  forall l M f g (nd_pf : NoDup (domain g)) pf1 pf2,
    pos l ->
      max (domain g) <= M ->
    f = (fun x : name * name * flag * piType =>
           let (y, t0) := x in
           let (y0, f) := y in
           let (a1, a2) := y0 in
           if In2 (a1, a2) l
           then (a1, a2 + M, f, t0)
           else cast x) ->
    cons (vis_proj g) pf1 ->
    cons (vis_proj (map f g)) pf2.
Proof with eauto using cons2_rewrite_pf.
  intros.
  revert dependent l. revert dependent f. revert dependent M.
  induction g. simpl...

  assert (nd_pf3 : NoDup (domain (vis_proj g))).
  eapply no_dup_vis_proj...
  eapply no_dup_isMap in nd_pf3 as pf3.

  assert (cons (vis_proj g) pf3).
  destruct a as [[[a1 a2] ff] tt];  destruct ff; simpl in H2...
  
  destruct a as [[[a1 a2] ff] tt];
    intros M MAX; simpl; intros.
  
  assert (MAX2:  max (domain g) <= M).
  assert (max (domain g) <= max ((a1, a2) :: domain g)). eauto.
  unfold domain in MAX; fold domain in MAX; lia.

  assert (nd_pfg : NoDup (domain g)).
  inversion nd_pf...

  (*assert (nd_pf1 : NoDup (domain (map f g))).
  Check no_dup_shift.
  eapply no_dup_shift; unfold domain in H0; fold domain in H0...
  eapply no_dup_vis_proj, no_dup_isMap in nd_pf1 as pf'.*)

  assert (EQ2 : forall a1 a2 g f t,
             removeEntry (a1, a2)
                         ((a1, a2, f, t)
                            :: g) = g).
  intros; simpl; try erewrite pairEq_eq_true...
  assert (PF := pf2).
  eapply isMap_removeEntry in PF as pf''.
  
  destruct ff; revert dependent pf2; subst f;
    case_eq (In2 (a1, a2) l); intros EQ; intros; repeat simpl; unfold castF; simpl.
  - eapply IHg with (M := M)...
  - destruct tt; try destruct m; simpl; subst...
  - destruct tt; try destruct m; simpl; subst...
  - destruct tt; try destruct m; simpl in *; subst...
  - remember (fun x : name * name * flag * piType =>
              let (y, t0) := x in
              let (y0, f) := y in
              let (a0, a3) := y0 in if In2 (a0, a3) l then (a0, a3 + M, f, t0) else cast x) as f.
    destruct tt; try destruct m; simpl.
     + assert (p = empty).
     simpl in H2; eapply cons_lin in H2...
     subst.
(*     erewrite <-EQ2 with (f := vis) (t := Chan lin empty tt) in pf'.*)
       eapply Co_lin with  (pf' := pf'').
      eauto.
      revert dependent pf''; simpl; erewrite pairEq_eq_true; intros; 
        eapply IHg with (M := M)...
     + 
      eapply Co_un with  (pf' := pf''). 
      eauto.
      revert dependent pf''; simpl; erewrite pairEq_eq_true; intros; 
        eapply IHg with (M := M)...
    + eapply Co_top with  (pf' := pf''). 
      eauto.
      revert dependent pf''; simpl; erewrite pairEq_eq_true; intros; 
        eapply IHg with (M := M)...
  - remember (fun x : name * name * flag * piType =>
              let (y, t0) := x in
              let (y0, f) := y in
              let (a0, a3) := y0 in if In2 (a0, a3) l then (a0, a3 + M, f, t0) else cast x) as f.
    assert (pf''' : isMap (removeEntry (a1, a2) ((a1, a2, vis, tt) :: vis_proj (map f g)))).
    eapply isMap_removeEntry...
    destruct tt; try destruct m; simpl.
     +  simpl in H2.
        assert (p = empty).
        eapply cons_lin in H2...
        subst.
        (*    erewrite <-EQ2 with (f := vis) (t := Chan lin empty tt) in pf'.*)
        eapply Co_lin with  (pf' := pf''').
        simpl...
        
        revert dependent pf'''; simpl; erewrite pairEq_eq_true; intros; 
        eapply IHg with (M := M)...
          
     +
       (*erewrite <-EQ2 with (f := vis) (t := Chan un p tt) in pf'.*)
      eapply Co_un with  (pf' := pf'''). 
      eauto.
      revert dependent pf'''; simpl; erewrite pairEq_eq_true; intros; 
        eapply IHg with (M := M)...
    + eapply Co_top with  (pf' := pf'''). 
      eauto.
      revert dependent pf'''; simpl; erewrite pairEq_eq_true; intros; 
        eapply IHg with (M := M)...
    Unshelve.
    all:eauto.
Qed.



#[global] Hint Resolve gcons_cons.

Lemma cons_ill_proj_map:
  forall l M f g (nd_pf : NoDup (domain g)) pf1 pf2,
      pos l ->
      max (domain g) <= M ->
    f = (fun x : name * name * flag * piType =>
           let (y, t0) := x in
           let (y0, f) := y in
           let (a1, a2) := y0 in
           if In2 (a1, a2) l
           then (a1, a2 + M, f, t0)
           else cast x) ->
    cons (ill_proj g) pf1 ->
    cons (ill_proj (map f g)) pf2.
Proof with eauto.
  intros.
  revert dependent l. revert dependent f. revert dependent M.
  induction g. simpl...

  assert (nd_pf3 : NoDup (domain (ill_proj g))).
  eapply no_dup_ill_proj...
  eapply no_dup_isMap in nd_pf3 as pf3.


  assert (cons (ill_proj g) pf3).
  destruct a as [[[a1 a2] ff] tt];  destruct ff; simpl in H2...
  destruct a as [[[a1 a2] ff] tt];
    intros M MAX; simpl; intros.
  
  assert (MAX2:  max (domain g) <= M).
  assert (max (domain g) <= max ((a1, a2) :: domain g)). eauto.
  unfold domain in MAX; fold domain in MAX; lia.

(*  assert (nd_pf1 : NoDup (domain (map (fun x : name * name * flag * piType =>
                                         let (y, t0) := x in let (y0, f) := y in let (a0, a3) := y0 in if In2 (a0, a3) l then (a0, a3 + M, f, t0) else cast x) g))).
  eapply no_dup_shift; unfold domain in H0; fold domain in H0...
  eapply no_dup_ill_proj, no_dup_isMap in nd_pf1 as pf'.
*)
  assert (EQ2 : forall a1 a2 g f t,
             removeEntry (a1, a2)
                         ((a1, a2, f, t)
                            :: g) = g).
  intros; simpl; try erewrite pairEq_eq_true...

   assert (PF := pf2).
  eapply isMap_removeEntry in PF as pf''.
  
  destruct ff; revert dependent pf2; subst f;
    case_eq (In2 (a1, a2) l); intros EQ; intros; repeat simpl; unfold castF; simpl.
  - eapply IHg with (M := M)...
  - remember ((fun x : name * name * flag * piType =>
              let (y, t0) := x in
              let (y0, f) := y in
              let (a0, a3) := y0 in if In2 (a0, a3) l then (a0, a3 + M, f, t0) else cast x)) as f.
      
      
    destruct tt; try destruct m; simpl.
    + assert (pf''' :
               isMap (removeEntry (a1, a2)
                        ((a1, a2, ill, Chan lin empty tt) :: ill_proj (map f g)))).
      simpl in *; rewrite EQ in *...
      eapply Co_lin with  (pf' := pf''').
      eauto.
      revert dependent pf'''; simpl; erewrite pairEq_eq_true; intros; 
        eapply IHg with (M := M)...
          
    + assert (pf''' :
               isMap (removeEntry (a1, a2)
                        ((a1, a2, ill, Chan un p tt) :: ill_proj (map f g)))).
      simpl in *; rewrite EQ in *; try rewrite pairEq_eq_true in *...
      eapply Co_un with  (pf' := pf'''). 
      eauto.
      revert dependent pf'''; simpl; erewrite pairEq_eq_true; intros; 
        eapply IHg with (M := M)...
    + 
      assert (pf''' :
               isMap (removeEntry (a1, a2)
                        ((a1, a2, ill, Top) :: ill_proj (map f g)))).
      simpl in *; rewrite EQ in *; try rewrite pairEq_eq_true in *...
      eapply Co_top with  (pf' := pf'''). 
      eauto.
      revert dependent pf'''; simpl; erewrite pairEq_eq_true; intros; 
        eapply IHg with (M := M)...
  -
    remember ((fun x : name * name * flag * piType =>
                 let (y, t0) := x in
                 let (y0, f) := y in
                 let (a0, a3) := y0 in if In2 (a0, a3) l then (a0, a3 + M, f, t0) else cast x)) as f.
      
    destruct tt; try destruct m; simpl.
     +  simpl in H2.
        assert (p = empty).
        eapply cons_lin in H2...
        subst p.
        assert (pf''': isMap (removeEntry (a1, a2 +M)
                                ((a1, a2 + M, ill, Chan lin empty tt) :: ill_proj (map f g)))).
        eapply isMap_removeEntry...
        
        eapply Co_lin with  (pf' := pf''').
      eauto.
      revert dependent pf'''; simpl; erewrite pairEq_eq_true; intros; 
        eapply IHg with (M := M)...
          
    +  assert (pf''': isMap (removeEntry (a1, a2 +M)
                               ((a1, a2 + M, ill, Chan un p tt) :: ill_proj (map f g)))).
        eapply isMap_removeEntry...
      eapply Co_un with  (pf' := pf'''). 
      eauto.
      revert dependent pf'''; simpl; erewrite pairEq_eq_true; intros; 
        eapply IHg with (M := M)...
    + assert (pf''': isMap (removeEntry (a1, a2 +M)
                                ((a1, a2 + M, ill, Top) :: ill_proj (map f g)))).
        eapply isMap_removeEntry...
      eapply Co_top with  (pf' := pf'''). 
      eauto.
      revert dependent pf'''; simpl; erewrite pairEq_eq_true; intros; 
        eapply IHg with (M := M)...
  -   remember ((fun x : name * name * flag * piType =>
                 let (y, t0) := x in
                 let (y0, f) := y in
                 let (a0, a3) := y0 in if In2 (a0, a3) l then (a0, a3 + M, f, t0) else cast x)) as f.

      destruct tt; try destruct m; simpl.
      + 
assert (pf''' :
               isMap (removeEntry (a1, a2)
                        ((a1, a2, ill, Chan lin empty tt) :: ill_proj (map f g)))).
      simpl in *; rewrite EQ in *...
        eapply Co_lin with (pf' := pf''').
        eauto.
        revert dependent pf'''; simpl; erewrite pairEq_eq_true; intros; 
          eapply IHg with (M := M)...
      +

        assert (pf''' :
               isMap (removeEntry (a1, a2)
                        ((a1, a2, ill, Chan  un p tt) :: ill_proj (map f g)))).
        simpl in *; rewrite EQ in *...
        eapply Co_un with  (pf' := pf'''). 
      eauto.
      revert dependent pf'''; simpl; erewrite pairEq_eq_true; intros; 
        eapply IHg with (M := M)...
      + assert (pf''' :
               isMap (removeEntry (a1, a2)
                        ((a1, a2, ill, Top) :: ill_proj (map f g)))).
      simpl in *; rewrite EQ in *...

        eapply Co_top with  (pf' := pf'''). 
      eauto.
      revert dependent pf'''; simpl; erewrite pairEq_eq_true; intros; 
        eapply IHg with (M := M)...
  - subst...
  - subst...
    Unshelve.
    all:eauto.
Qed.

Lemma shift_removeEntry_2: forall u g l M f,
    ~In u l ->
    pos l ->
    snd u <= M ->
    f =  (fun x : name * name * flag * piType =>
         let (y, t0) := x in
         let (y0, f0) := y in
         let (a1, a2) := y0 in
         if In2 (a1, a2) l
         then (a1, a2 + M, f0, t0)
         else cast x) -> 
    map f  (removeEntry u g) =
    removeEntry u (map f g).
Proof with eauto.
  intros  u g l M f NIN POS LE Heqf.
 dependent induction g; simpl; try destruct a as [[[a1 a2] ff] tt];try case_eq(pair_eq (a1, a2) u);intros...
  - rewrite <-pairEq_eq in H; inversion H; subst u;
     rewrite <-in2_nIn_iff in NIN; rewrite Heqf,NIN,<-Heqf.
   case_eq (cast (a1, a2, ff, tt)); intros ((b1 & b2) & ff1)  tt1  EQ; simpl in EQ; inversion EQ; subst b1 b2.
   assert (pair_eq (a1, a2) (a1, a2) = true). eapply pairEq_eq... rewrite H...
  - simpl; case_eq (f (a1, a2, ff, tt)); intros ((b1 & b2) & ff1)  tt1  EQ; rewrite Heqf in EQ.
    case_eq (In2 (a1, a2) l); intros EQ2; rewrite EQ2 in *; inversion EQ; subst b1 b2 ff1 tt1.
    + erewrite IHg...
      case_eq (pair_eq (a1, a2 + M) u); intros ABS...
      destruct u as [u1 u2]; rewrite <-pairEq_eq in ABS;
        inversion ABS; simpl in LE.
      assert (a2 = 0) by lia.
      assert (a2 > 0).
      rewrite in2_In_iff in *; unfold pos in *;
        specialize POS with a1 a2; eapply POS...
      lia.
    + case_eq (pair_eq (a1, a2) u);
        intros ABS; try rewrite <-pairEq_eq in ABS;
        inversion ABS; try subst u; assert (EQ4: pair_eq (a1, a2) (a1, a2) = true); try eapply pairEq_eq; eauto; try rewrite EQ4 in *; erewrite IHg;try discriminate...
      Unshelve.  all : eauto.
Qed.


Lemma shift_removeEntry_3: forall u1 u2 g l M f,
    In (u1, u2) l ->
    pos l ->
    M > 0 ->
    (forall x1 x2, In (x1, x2) (domain g) -> x2 <= M) -> 
    f =  (fun x : name * name * flag * piType =>
         let (y, t0) := x in
         let (y0, f0) := y in
         let (a1, a2) := y0 in
         if In2 (a1, a2) l
         then (a1, a2 + M, f0, t0)
         else cast x) -> 
    map f  (removeEntry (u1, u2) g) =
    removeEntry (u1, u2 + M) (map f g).
Proof with eauto.
   intros  u1 u2 g l M f IN POS MPOS MAX Heqf.
 dependent induction g; simpl; try destruct a as [[[a1 a2] ff] tt];try case_eq(pair_eq (a1, a2) (u1, u2));intros...
  - rewrite <-pairEq_eq in H; inversion H; subst u1 u2;
     rewrite <-in2_In_iff in IN; rewrite Heqf,IN,<-Heqf.
   case_eq (cast (a1, a2, ff, tt)); intros ((b1 & b2) & ff1)  tt1  EQ; simpl in EQ; inversion EQ; subst b1 b2.
   assert (EQ2: pair_eq (a1, a2 + M) (a1, a2 + M) = true). eapply pairEq_eq... rewrite EQ2...
  - simpl; case_eq (f (a1, a2, ff, tt)); intros ((b1 & b2) & ff1)  tt1  EQ; rewrite Heqf in EQ.
    case_eq (In2 (a1, a2) l); intros EQ2; rewrite EQ2 in *; inversion EQ; subst b1 b2 ff1 tt1.
    + erewrite IHg...
      case_eq (pair_eq (a1, a2 + M) (u1, u2 + M)); intros ABS; try rewrite <-pairEq_eq in ABS; inversion ABS.
      assert (a2 = u2) by lia.
      subst u1 u2.
      assert (EQ3: pair_eq (a1, a2) (a1, a2) = true). eapply pairEq_eq... rewrite EQ3 in *; discriminate.
      tauto. intros; eapply MAX;simpl...
    + case_eq (pair_eq (a1, a2) (u1, u2 + M)); intros ABS; try rewrite <-pairEq_eq in ABS; inversion ABS; try 
                                                                                                            erewrite IHg...
      assert (u2 >0).
      unfold pos in POS; specialize POS with u1 u2; eapply POS...
      assert (a2 <= M ). specialize MAX with a1 a2; simpl in MAX. eapply MAX...
      lia.
      all:intros; specialize MAX with x1 x2;
        eapply MAX;simpl;
          try erewrite in_app_iff;right...
Qed.


Lemma max_pos: forall u l1 l2,
    In u l1 -> pos l1 -> In u l2 ->
    max l2 > 0.
Proof with eauto.
  intros [u1 u2] l1 l2 IN1 POS IN2; unfold pos in *;
    specialize POS with u1 u2;
    assert (u2 > 0); intuition; clear IN1.
  dependent induction l2; inversion IN2;subst;simpl;
    case_eq (u2 <? max l2); intros;
      try rewrite Nat.ltb_lt in *;   
      try destruct a as [a1 a2];
      try case_eq (a2 <? max l2);
      intros;
      try rewrite Nat.ltb_nlt in *;
      try eapply  IHl2 in H1; intuition;
      try lia...
Qed.  




Lemma split_map: forall g1 g2 g pf1 pf2 pf l M pf' pf'' pf''' (nd_pf : NoDup (domain g)),
    pos l ->
    tEnv_split g1 g2 g pf1 pf2 pf ->
    max (domain g) <= M ->
    tEnv_split
    (map
       (fun x : name * name * flag * piType =>
        let (y, t) := x in
        let (y0, f) := y in
        let (a1, a2) := y0 in
        if In2 (a1, a2) l then (a1, a2 + M, f, t) else cast x) g1)
    (map
       (fun x : name * name * flag * piType =>
        let (y, t) := x in
        let (y0, f) := y in
        let (a1, a2) := y0 in
        if In2 (a1, a2) l then (a1, a2 + M, f, t) else cast x) g2)
    (map
       (fun x : name * name * flag * piType =>
        let (y, t) := x in
        let (y0, f) := y in
        let (a1, a2) := y0 in
        if In2 (a1, a2) l then (a1, a2 + M, f, t) else cast x) g) 
    pf' pf'' pf'''.
Proof with eauto.
  intros g1 g2 g pf1 pf2 pf l M pf' pf'' pf''' nd_pf POS TS MAX.
  revert dependent pf'. (*erewrite split_max with (g := g)...*) intros.
  revert dependent pf''. (*erewrite split_max with (g := g) (g1 := g2); try eapply split_comm... *) intros.
  dependent induction TS;subst;simpl.
  econstructor...
  -  Case SpLin.
     assert (TS2 :  tEnv_split g1 g2 g3 pf1 pf2 pf3).
     eapply SpLin...

     assert (ND1: NoDup (domain g1)).
     eapply no_dup_split_no_dup_l...
     assert (MAX1: max (domain g1) <= M).
     erewrite split_max...
     assert (ND2: NoDup (domain g2)).
     eapply no_dup_split_no_dup_r with (g := g3)...
     assert (MAX2: max (domain g2) <= M).
     erewrite split_max  with (g := g3);
       try eapply split_comm...
     destruct n as [n1 n2].
     assert (MAX': max (domain (removeEntry (n1,n2) g1)) <= M).
     transitivity (max (domain g1)); try eapply max_removeEntry...
      assert (MAX'': max (domain (removeEntry (n1,n2) g2)) <= M).
      transitivity (max (domain g2)); try eapply max_removeEntry...
       assert (MAX''': max (domain (removeEntry (n1,n2) g3)) <= M).
     transitivity (max (domain g3)); try eapply max_removeEntry... 

     case_eq (In2 (n1, n2) l); intros IN2.
    +  assert (IN2':  In (n1, n2) l).
       eapply in2_implies_in...
       assert (MPOS: M > 0).
       assert (max (domain g3) > 0).
       inversion H5; eapply max_pos with (u := (n1, n2)) (l1 := l),in_g_in_domain...
       lia.

    eapply no_dup_removeEntry_no_dup with (a := (n1, n2)) in nd_pf as nd_pff.
    assert (nd_pf1 : NoDup (domain (removeEntry (n1, n2) g1))).
    eapply no_dup_split_no_dup_l...
    assert (nd_pf2 : NoDup (domain (removeEntry (n1, n2) g2))).
    eapply no_dup_split_no_dup_r with (g := removeEntry (n1, n2) g3)...
    eapply  no_dup_shift with (l := l) (n := M) in nd_pff as nd_pf'''; try eapply no_dup_isMap in nd_pf''' as pff'''.
    eapply  no_dup_shift with (l := l) (n := M) in nd_pf1 as nd_pf'; try eapply no_dup_isMap in nd_pf' as pff'.
       eapply  no_dup_shift with (l := l) (n := M) in nd_pf2 as nd_pf''; try eapply no_dup_isMap in nd_pf'' as pff''.
    assert (nd_pfk1: NoDup (domain (removeEntry (n1, n2 + M)
      (map
         (fun x : name * name * flag * piType =>
          let (y, t0) := x in
          let (y0, f0) := y in
          let (a1, a2) := y0 in if In2 (a1, a2) l then (a1, a2 + M, f0, t0) else cast x) g1)))).
    eapply no_dup_removeEntry_no_dup,no_dup_shift...
    eapply no_dup_isMap in nd_pfk1 as pfk1.
     assert (nd_pfk2: NoDup (domain (removeEntry (n1, n2 + M)
      (map
         (fun x : name * name * flag * piType =>
          let (y, t0) := x in
          let (y0, f0) := y in
          let (a1, a2) := y0 in if In2 (a1, a2) l then (a1, a2 + M, f0, t0) else cast x) g2)))).
    eapply no_dup_removeEntry_no_dup,no_dup_shift...
    eapply no_dup_isMap in nd_pfk2 as pfk2.

     assert (nd_pfk3: NoDup (domain (removeEntry (n1, n2 + M)
      (map
         (fun x : name * name * flag * piType =>
          let (y, t0) := x in
          let (y0, f0) := y in
          let (a1, a2) := y0 in if In2 (a1, a2) l then (a1, a2 + M, f0, t0) else cast x) g3)))).
    eapply no_dup_removeEntry_no_dup,no_dup_shift...
    eapply no_dup_isMap in nd_pfk3 as pfk3.
    
    eapply SpLin with
        (n := (n1, n2 + M)) (pf' := pfk1) (pf'' := pfk2)
    (pf''' := pfk3);
      try erewrite  in_map_iff.
    eauto.
    eauto.
    try exists (n1, n2, f, Chan lin p t);
                 simpl; try rewrite IN2...
    try exists (n1, n2, g, Chan lin q t);simpl; try erewrite IN2...
    assert (IH : max (domain (removeEntry (n1, n2) g3)) <= M). eauto.
  
    eapply IHTS  with (pf' := pff') (pf'' := pff'') (pf''' := pff''')in IH; move IH at bottom.
    revert dependent pfk1.
    revert dependent pfk2.
    revert dependent pfk3.
    erewrite <-shift_removeEntry_3 with (M := M),
       <-shift_removeEntry_3 with (M := M),<-shift_removeEntry_3 with (M := M); intros.
    eapply split_cons_remove.split_pf...

    all: eauto.
    assert (LE: x2 <= max (domain g1));
      try eapply min_max...
    lia.
    assert (LE: x2 <= max (domain g2));
      try eapply min_max...
    lia.
     assert (LE: x2 <= max (domain g3));
      try eapply min_max...
     lia.
     inversion H4; subst; econstructor; erewrite in_map_iff;
       exists (n1, n2, f', t0);erewrite IN2...

     inversion H5; subst; econstructor; erewrite in_map_iff;
      exists (n1, n2, f0,  Chan lin p' t);erewrite IN2...

    +  eapply in2_nIn_iff in IN2 as NIN.
     remember (match snd (castF f (Chan lin p t)) with
              | Chan _ p _ => p | _ => empty end ) as P.
     remember (match snd (castF g (Chan lin q t)) with
              | Chan _ p _ => p | _ => empty end ) as Q.
     remember (match snd (castF f' (Chan lin p' t)) with
              | Chan _ p _ => p | _ => empty end ) as P1.
     remember (match f with | hid => ill | _ => f end ) as F.
     remember (match g with | hid => ill | _ => g end ) as G.
     remember (match f' with | hid => ill | _ => f' end ) as F1.
      assert (nd_pfk1: NoDup (domain (removeEntry (n1, n2)
      (map
         (fun x : name * name * flag * piType =>
          let (y, t0) := x in
          let (y0, f0) := y in
          let (a1, a2) := y0 in if In2 (a1, a2) l then (a1, a2 + M, f0, t0) else cast x) g1)))).
    eapply no_dup_removeEntry_no_dup,no_dup_shift...
    eapply no_dup_isMap in nd_pfk1 as pfk1.
     assert (nd_pfk2: NoDup (domain (removeEntry (n1, n2)
      (map
         (fun x : name * name * flag * piType =>
          let (y, t0) := x in
          let (y0, f0) := y in
          let (a1, a2) := y0 in if In2 (a1, a2) l then (a1, a2 + M, f0, t0) else cast x) g2)))).
    eapply no_dup_removeEntry_no_dup,no_dup_shift...
    eapply no_dup_isMap in nd_pfk2 as pfk2.

     assert (nd_pfk3: NoDup (domain (removeEntry (n1, n2)
      (map
         (fun x : name * name * flag * piType =>
          let (y, t0) := x in
          let (y0, f0) := y in
          let (a1, a2) := y0 in if In2 (a1, a2) l then (a1, a2 + M, f0, t0) else cast x) g3)))).
    eapply no_dup_removeEntry_no_dup,no_dup_shift...
    eapply no_dup_isMap in nd_pfk3 as pfk3.
      
    eapply SpLin with (n := (n1, n2)) (f := F) (g := G) (f' := F1) (p := P) (q := Q) (p' := P1) (t := t)
    (pf' := pfk1) (pf'' := pfk2)
    (pf''' := pfk3);
      try rewrite in_map_iff.
    (* flag_plus F G F1 *)
    destruct f,f', g; subst; try inversion H;subst...
    (*  pol_plus P Q P1 *)
    destruct f', p,q,p'; subst; try inversion H;subst...
    exists ((n1, n2, f, Chan lin p t));
         try rewrite IN2;simpl; unfold castF;destruct f;subst; simpl...
         exists ((n1, n2, g, Chan lin q t));
           try rewrite IN2;simpl; unfold castF;destruct g;subst; simpl...   
         eapply IHTS in MAX''' as IH.
         revert dependent pfk1.
         revert dependent pfk2.
         revert dependent pfk3.
         erewrite <-shift_removeEntry_2 with (M := M),
         <-shift_removeEntry_2 with (M := M),<-shift_removeEntry_2 with (M := M);simpl...
         transitivity (max (domain g1));
           try eapply in_preserves_max,in_g_in_domain...
         transitivity (max (domain g1));
           try eapply in_preserves_max,in_g_in_domain...
         transitivity (max (domain g1));
           try eapply in_preserves_max,in_g_in_domain...
         eapply no_dup_removeEntry_no_dup...
         tauto.
        
         (* flagOf
    (map
       (fun x : name * name * flag * piType =>
        let (y, t0) := x in
        let (y0, f0) := y in
        let (a1, a2) := y0 in if In2 (a1, a2) l then (a1, a2 + M, f0, t0) else cast x) g3)
    (n1, n2) F1 *)
         assert (IN3: In (n1, n2, f', Chan lin p' t) g3).
         inversion H4; inversion H5; subst.
         assert (EQ: f' = f1 /\ t0 =  Chan lin p' t).
         eapply in_isMap with (g := g3)...
         destruct EQ; subst...
         destruct f, f'.
         eapply F_Entry with
             (t := Chan lin empty t); eapply in_map_iff;
            exists (n1, n2, hid, Chan lin p' t);
            rewrite IN2; subst F1; subst; simpl...
         eapply F_Entry with
             (t := Chan lin empty t); eapply in_map_iff;
            exists (n1, n2, ill, Chan lin p' t);
            rewrite IN2; subst F1; subst; simpl...
         eapply F_Entry with
             (t := Chan lin p' t); eapply in_map_iff;
            exists (n1, n2, vis, Chan lin p' t);
            rewrite IN2; subst F1; subst; simpl...
          eapply F_Entry with
             (t := Chan lin empty t); eapply in_map_iff;
            exists (n1, n2, hid, Chan lin p' t);
            rewrite IN2; subst F1; subst; simpl...
          eapply F_Entry with
             (t := Chan lin empty t); eapply in_map_iff;
            exists (n1, n2, ill, Chan lin p' t);
            rewrite IN2; subst F1; subst; simpl...
         eapply F_Entry with
             (t := Chan lin p' t); eapply in_map_iff;
            exists (n1, n2, vis, Chan lin p' t);
            rewrite IN2; subst F1; subst; simpl...
          eapply F_Entry with
             (t := Chan lin empty t); eapply in_map_iff;
            exists (n1, n2, hid, Chan lin p' t);
            rewrite IN2; subst F1; subst; simpl...
          eapply F_Entry with
             (t := Chan lin empty t); eapply in_map_iff;
            exists (n1, n2, ill, Chan lin p' t);
            rewrite IN2; subst F1; subst; simpl...
         eapply F_Entry with
             (t := Chan lin p' t); eapply in_map_iff;
            exists (n1, n2, vis, Chan lin p' t);
            rewrite IN2; subst F1; subst; simpl...
         (* typeOf
    (map
       (fun x : name * name * flag * piType =>
        let (y, t0) := x in
        let (y0, f0) := y in
        let (a1, a2) := y0 in if In2 (a1, a2) l then (a1, a2 + M, f0, t0) else cast x) g3)
    (n1, n2) (Chan lin P1 t) *)
          assert (IN3: In (n1, n2, f', Chan lin p' t) g3).
         inversion H4; inversion H5; subst.
         assert (EQ: f' = f1 /\ t0 =  Chan lin p' t).
         eapply in_isMap with (g := g3)...
         destruct EQ; subst...
         eapply T_Entry with (f := fst (castF f' (Chan lin p' t)));
           eapply in_map_iff;
           exists (n1, n2, f', Chan lin p' t);
            rewrite IN2; subst P1; destruct f'; simpl... 
  - Case SpUn. 
     assert (TS2 :  tEnv_split g1 g2 g3 pf1 pf2 pf3).
     eapply SpUn...

     assert (ND1: NoDup (domain g1)).
     eapply no_dup_split_no_dup_l...
     assert (MAX1: max (domain g1) <= M).
     erewrite split_max...
     assert (ND2: NoDup (domain g2)).
     eapply no_dup_split_no_dup_r with (g := g3)...
     assert (MAX2: max (domain g2) <= M).
     erewrite split_max  with (g := g3);
       try eapply split_comm...
     destruct n as [n1 n2].
     assert (MAX': max (domain (removeEntry (n1,n2) g1)) <= M).
     transitivity (max (domain g1)); try eapply max_removeEntry...
      assert (MAX'': max (domain (removeEntry (n1,n2) g2)) <= M).
      transitivity (max (domain g2)); try eapply max_removeEntry...
       assert (MAX''': max (domain (removeEntry (n1,n2) g3)) <= M).
       transitivity (max (domain g3)); try eapply max_removeEntry...

         eapply no_dup_removeEntry_no_dup with (a := (n1, n2)) in nd_pf as nd_pff.
    assert (nd_pf1 : NoDup (domain (removeEntry (n1, n2) g1))).
    eapply no_dup_split_no_dup_l...
    assert (nd_pf2 : NoDup (domain (removeEntry (n1, n2) g2))).
    eapply no_dup_split_no_dup_r with (g := removeEntry (n1, n2) g3)...
    eapply  no_dup_shift with (l := l) (n := M) in nd_pff as nd_pf'''; try eapply no_dup_isMap in nd_pf''' as pff'''.
    eapply  no_dup_shift with (l := l) (n := M) in nd_pf1 as nd_pf'; try eapply no_dup_isMap in nd_pf' as pff'.
       eapply  no_dup_shift with (l := l) (n := M) in nd_pf2 as nd_pf''; try eapply no_dup_isMap in nd_pf'' as pff''.
    

     case_eq (In2 (n1, n2) l); intros IN2.
    +  assert (IN2':  In (n1, n2) l).
       eapply in2_implies_in...
       assert (MPOS: M > 0).
       assert (max (domain g3) > 0).
       inversion H4; eapply max_pos with (u := (n1, n2)) (l1 := l),in_g_in_domain...
       lia.

       assert (nd_pfk1: NoDup (domain (removeEntry (n1, n2 + M)
      (map
         (fun x : name * name * flag * piType =>
          let (y, t0) := x in
          let (y0, f0) := y in
          let (a1, a2) := y0 in if In2 (a1, a2) l then (a1, a2 + M, f0, t0) else cast x) g1)))).
    eapply no_dup_removeEntry_no_dup,no_dup_shift...
    eapply no_dup_isMap in nd_pfk1 as pfk1.
     assert (nd_pfk2: NoDup (domain (removeEntry (n1, n2 + M)
      (map
         (fun x : name * name * flag * piType =>
          let (y, t0) := x in
          let (y0, f0) := y in
          let (a1, a2) := y0 in if In2 (a1, a2) l then (a1, a2 + M, f0, t0) else cast x) g2)))).
    eapply no_dup_removeEntry_no_dup,no_dup_shift...
    eapply no_dup_isMap in nd_pfk2 as pfk2.

     assert (nd_pfk3: NoDup (domain (removeEntry (n1, n2 + M)
      (map
         (fun x : name * name * flag * piType =>
          let (y, t0) := x in
          let (y0, f0) := y in
          let (a1, a2) := y0 in if In2 (a1, a2) l then (a1, a2 + M, f0, t0) else cast x) g3)))).
    eapply no_dup_removeEntry_no_dup,no_dup_shift...
    eapply no_dup_isMap in nd_pfk3 as pfk3.

  

     eapply SpUn with
        (n := (n1, n2 + M)) (pf' := pfk1) (pf'' := pfk2)
    (pf''' := pfk3);
      try erewrite  in_map_iff.
    eauto.
    try exists (n1, n2, f, Chan un p t);
                 simpl; try rewrite IN2...
    try exists (n1, n2, g, Chan un p t);simpl; try erewrite IN2...
    assert (IH : max (domain (removeEntry (n1, n2) g3)) <= M). eauto.

    eapply IHTS  with (pf' := pff') (pf'' := pff'') (pf''' := pff''')in IH; move IH at bottom.
    revert dependent pfk1.
    revert dependent pfk2.
    revert dependent pfk3.
    erewrite <-shift_removeEntry_3 with (M := M),
       <-shift_removeEntry_3 with (M := M),<-shift_removeEntry_3 with (M := M); intros.
    eapply split_cons_remove.split_pf...

    eauto.
    eauto.
    eauto.
    assert (x2 <= max (domain g1));
      try eapply in_preserves_max;
      try transitivity (max (domain g1))...
    eauto.
    eauto.
    eauto.
    eauto.
     assert (x2 <= max (domain g2));
      try eapply in_preserves_max;
      try transitivity (max (domain g2))...
    eauto.
    eauto.
    eauto.
    eauto.
     assert (x2 <= max (domain g3));
      try eapply in_preserves_max;
      try transitivity (max (domain g3))...
    eauto.
    eauto.
    eauto.
    (* flagOf
    (map
       (fun x : name * name * flag * piType =>
        let (y, t0) := x in let (y0, f0) := y in let (a1, a2) := y0 in if In2 (a1, a2) l then (a1, a2 + M, f0, t0) else cast x) g3)
    (n1, n2 + M) f' *)
    clear Case IHTS; inverts H3; inverts H4.
    assert (EQ: f' = f0 /\ t0 = Chan un p t).
    eapply in_isMap with (g := g3)...
    destruct EQ; subst;
      econstructor; eapply in_map_iff; destruct  f0.
     try exists (n1, n2, hid, Chan un p t); simpl; try rewrite IN2; 
                  unfold cast,castF,flag_eq;simpl; intuition...
      try exists (n1, n2, ill, Chan un p t); simpl; try rewrite IN2; 
                  unfold cast,castF,flag_eq;simpl; intuition...
      try exists (n1, n2, vis, Chan un p t); simpl; try rewrite IN2; 
                  unfold cast,castF,flag_eq;simpl; intuition...
    (* typeOf
    (map
       (fun x : name * name * flag * piType =>
        let (y, t0) := x in let (y0, f0) := y in let (a1, a2) := y0 in if In2 (a1, a2) l then (a1, a2 + M, f0, t0) else cast x) g3)
    (n1, n2 + M) (Chan un p t) *)
     clear Case IHTS; inverts H3; inverts H4.
    assert (EQ: f' = f0 /\ t0 = Chan un p t).
    eapply in_isMap with (g := g3)...
    destruct EQ; subst;
      econstructor; eapply in_map_iff; destruct  f0.
     try exists (n1, n2, hid, Chan un p t); simpl; try rewrite IN2; 
                  unfold cast,castF,flag_eq;simpl; intuition...
      try exists (n1, n2, ill, Chan un p t); simpl; try rewrite IN2; 
                  unfold cast,castF,flag_eq;simpl; intuition...
      try exists (n1, n2, vis, Chan un p t); simpl; try rewrite IN2; 
                   unfold cast,castF,flag_eq;simpl; intuition...
  +   assert (nd_pfk1: NoDup (domain (removeEntry (n1, n2)
      (map
         (fun x : name * name * flag * piType =>
          let (y, t0) := x in
          let (y0, f0) := y in
          let (a1, a2) := y0 in if In2 (a1, a2) l then (a1, a2 + M, f0, t0) else cast x) g1)))).
    eapply no_dup_removeEntry_no_dup,no_dup_shift...
    eapply no_dup_isMap in nd_pfk1 as pfk1.
     assert (nd_pfk2: NoDup (domain (removeEntry (n1, n2)
      (map
         (fun x : name * name * flag * piType =>
          let (y, t0) := x in
          let (y0, f0) := y in
          let (a1, a2) := y0 in if In2 (a1, a2) l then (a1, a2 + M, f0, t0) else cast x) g2)))).
    eapply no_dup_removeEntry_no_dup,no_dup_shift...
    eapply no_dup_isMap in nd_pfk2 as pfk2.

     assert (nd_pfk3: NoDup (domain (removeEntry (n1, n2)
      (map
         (fun x : name * name * flag * piType =>
          let (y, t0) := x in
          let (y0, f0) := y in
          let (a1, a2) := y0 in if In2 (a1, a2) l then (a1, a2 + M, f0, t0) else cast x) g3)))).
    eapply no_dup_removeEntry_no_dup,no_dup_shift...
    eapply no_dup_isMap in nd_pfk3 as pfk3.

    eapply in2_nIn_iff in IN2 as NIN.
     remember (match f with | hid => ill | _ => f end ) as F.
     remember (match g with | hid => ill | _ => g end ) as G.
     remember (match f' with | hid => ill | _ => f' end ) as F1.

    eapply SpUn with
        (n := (n1, n2)) (pf' := pfk1) (pf'' := pfk2)
    (pf''' := pfk3) (f := F) (g := G) (f' := F1);
      try erewrite  in_map_iff.
    destruct f, g, f'; subst; try inversion H...
    try exists (n1, n2, f, Chan un p t);
                 try rewrite IN2; try destruct f; simpl; subst...
    try exists (n1, n2, g, Chan un p t);
                   try rewrite IN2; try destruct g; simpl; subst...
    assert (IH : max (domain (removeEntry (n1, n2) g3)) <= M). eauto.

    eapply IHTS  with (pf' := pff') (pf'' := pff'') (pf''' := pff''')in IH; move IH at bottom.
    revert dependent pfk1.
    revert dependent pfk2.
    revert dependent pfk3.
    erewrite <-shift_removeEntry_2 with (M := M),
       <-shift_removeEntry_2 with (M := M),<-shift_removeEntry_2 with (M := M); intros.
    eapply split_cons_remove.split_pf...

    eauto.
    eauto.
    assert (n2 <= max (domain g1));
      try eapply in_preserves_max;
      try transitivity (max (domain g1))...
    eauto.
    eauto.
    eauto.
     assert (n2 <= max (domain g2));
      try eapply in_preserves_max;
      try transitivity (max (domain g2))...
    eauto.
    eauto.
    eauto.
     assert (n2 <= max (domain g3));
      inversion H3; try eapply in_preserves_max;
      try transitivity (max (domain g3))...
    eauto.
    eauto.
    eauto.
    
    inverts H3; inverts H4.
    assert (EQ: f' = f0 /\ t0 = Chan un p t).
    eapply in_isMap with (g := g3)...
    destruct EQ; subst f0 t0 F1.
      econstructor;
        eapply in_map_iff;
        try exists ((n1, n2, f', Chan un p t));
                     try rewrite IN2;
                     try destruct f';
                     simpl...

    inverts H3; inverts H4.
    assert (EQ: f' = f0 /\ t0 = Chan un p t).
    eapply in_isMap with (g := g3)...
    destruct EQ; subst f0 t0 F1;                    
eapply T_Entry with (f := snd (fst (cast (n1, n2, f', Chan un p t))));
eapply in_map_iff;
  try exists ((n1, n2, f', Chan un p t));
               try rewrite IN2;
               try destruct f';
             simpl...
             + eauto.
             +  eauto.
             + eauto.
             + eauto.
             +  eauto.
             + eauto.
    
  - Case SpTop.
 assert (TS2 :  tEnv_split g1 g2 g3 pf1 pf2 pf3).
     eapply SpTop...

     assert (ND1: NoDup (domain g1)).
     eapply no_dup_split_no_dup_l...
     assert (MAX1: max (domain g1) <= M).
     erewrite split_max...
     assert (ND2: NoDup (domain g2)).
     eapply no_dup_split_no_dup_r with (g := g3)...
     assert (MAX2: max (domain g2) <= M).
     erewrite split_max  with (g := g3);
       try eapply split_comm...
     destruct n as [n1 n2].
     assert (MAX': max (domain (removeEntry (n1,n2) g1)) <= M).
     transitivity (max (domain g1)); try eapply max_removeEntry...
      assert (MAX'': max (domain (removeEntry (n1,n2) g2)) <= M).
      transitivity (max (domain g2)); try eapply max_removeEntry...
       assert (MAX''': max (domain (removeEntry (n1,n2) g3)) <= M).
       transitivity (max (domain g3)); try eapply max_removeEntry...

         eapply no_dup_removeEntry_no_dup with (a := (n1, n2)) in nd_pf as nd_pff.
    assert (nd_pf1 : NoDup (domain (removeEntry (n1, n2) g1))).
    eapply no_dup_split_no_dup_l...
    assert (nd_pf2 : NoDup (domain (removeEntry (n1, n2) g2))).
    eapply no_dup_split_no_dup_r with (g := removeEntry (n1, n2) g3)...
    eapply  no_dup_shift with (l := l) (n := M) in nd_pff as nd_pf'''; try eapply no_dup_isMap in nd_pf''' as pff'''.
    eapply  no_dup_shift with (l := l) (n := M) in nd_pf1 as nd_pf'; try eapply no_dup_isMap in nd_pf' as pff'.
       eapply  no_dup_shift with (l := l) (n := M) in nd_pf2 as nd_pf''; try eapply no_dup_isMap in nd_pf'' as pff''.
    

     case_eq (In2 (n1, n2) l); intros IN2.
    +  assert (IN2':  In (n1, n2) l).
       eapply in2_implies_in...
       assert (MPOS: M > 0).
       assert (max (domain g3) > 0).
       inversion H4; eapply max_pos with (u := (n1, n2)) (l1 := l),in_g_in_domain...
       lia.

       assert (nd_pfk1: NoDup (domain (removeEntry (n1, n2 + M)
      (map
         (fun x : name * name * flag * piType =>
          let (y, t0) := x in
          let (y0, f0) := y in
          let (a1, a2) := y0 in if In2 (a1, a2) l then (a1, a2 + M, f0, t0) else cast x) g1)))).
    eapply no_dup_removeEntry_no_dup,no_dup_shift...
    eapply no_dup_isMap in nd_pfk1 as pfk1.
     assert (nd_pfk2: NoDup (domain (removeEntry (n1, n2 + M)
      (map
         (fun x : name * name * flag * piType =>
          let (y, t0) := x in
          let (y0, f0) := y in
          let (a1, a2) := y0 in if In2 (a1, a2) l then (a1, a2 + M, f0, t0) else cast x) g2)))).
    eapply no_dup_removeEntry_no_dup,no_dup_shift...
    eapply no_dup_isMap in nd_pfk2 as pfk2.

     assert (nd_pfk3: NoDup (domain (removeEntry (n1, n2 + M)
      (map
         (fun x : name * name * flag * piType =>
          let (y, t0) := x in
          let (y0, f0) := y in
          let (a1, a2) := y0 in if In2 (a1, a2) l then (a1, a2 + M, f0, t0) else cast x) g3)))).
    eapply no_dup_removeEntry_no_dup,no_dup_shift...
    eapply no_dup_isMap in nd_pfk3 as pfk3.

  

     eapply SpTop with
        (n := (n1, n2 + M)) (pf' := pfk1) (pf'' := pfk2)
    (pf''' := pfk3);
      try erewrite  in_map_iff.
    eauto.
    try exists (n1, n2, f, Top);
                 simpl; try rewrite IN2...
    try exists (n1, n2, g, Top);simpl; try erewrite IN2...
    assert (IH : max (domain (removeEntry (n1, n2) g3)) <= M). eauto.

    eapply IHTS  with (pf' := pff') (pf'' := pff'') (pf''' := pff''')in IH; move IH at bottom.
    revert dependent pfk1.
    revert dependent pfk2.
    revert dependent pfk3.
    erewrite <-shift_removeEntry_3 with (M := M),
       <-shift_removeEntry_3 with (M := M),<-shift_removeEntry_3 with (M := M); intros.
    eapply split_cons_remove.split_pf...

    eauto.
    eauto.
    eauto.
    assert (x2 <= max (domain g1));
      try eapply in_preserves_max;
      try transitivity (max (domain g1))...
    eauto.
    eauto.
    eauto.
    eauto.
     assert (x2 <= max (domain g2));
      try eapply in_preserves_max;
      try transitivity (max (domain g2))...
    eauto.
    eauto.
    eauto.
    eauto.
     assert (x2 <= max (domain g3));
      try eapply in_preserves_max;
      try transitivity (max (domain g3))...
    eauto.
    eauto.
    eauto.
    (* flagOf
    (map
       (fun x : name * name * flag * piType =>
        let (y, t0) := x in let (y0, f0) := y in let (a1, a2) := y0 in if In2 (a1, a2) l then (a1, a2 + M, f0, t0) else cast x) g3)
    (n1, n2 + M) f' *)
    clear Case IHTS; inverts H3; inverts H4.
    assert (EQ: f' = f0 /\ t = Top).
    eapply in_isMap with (g := g3)...
    destruct EQ; subst;
      econstructor; eapply in_map_iff; destruct  f0.
     try exists (n1, n2, hid, Top); simpl; try rewrite IN2; 
                  unfold cast,castF,flag_eq;simpl; intuition...
      try exists (n1, n2, ill, Top); simpl; try rewrite IN2; 
                  unfold cast,castF,flag_eq;simpl; intuition...
      try exists (n1, n2, vis, Top); simpl; try rewrite IN2; 
                  unfold cast,castF,flag_eq;simpl; intuition...
    (* typeOf
    (map
       (fun x : name * name * flag * piType =>
        let (y, t0) := x in let (y0, f0) := y in let (a1, a2) := y0 in if In2 (a1, a2) l then (a1, a2 + M, f0, t0) else cast x) g3)
    (n1, n2 + M) (Chan un p t) *)
     clear Case IHTS; inverts H3; inverts H4.
    assert (EQ: f' = f0 /\ t = Top).
    eapply in_isMap with (g := g3)...
    destruct EQ; subst;
      econstructor; eapply in_map_iff; destruct  f0.
     try exists (n1, n2, hid, Top); simpl; try rewrite IN2; 
                  unfold cast,castF,flag_eq;simpl; intuition...
      try exists (n1, n2, ill, Top); simpl; try rewrite IN2; 
                  unfold cast,castF,flag_eq;simpl; intuition...
      try exists (n1, n2, vis, Top); simpl; try rewrite IN2; 
                   unfold cast,castF,flag_eq;simpl; intuition...
  +   assert (nd_pfk1: NoDup (domain (removeEntry (n1, n2)
      (map
         (fun x : name * name * flag * piType =>
          let (y, t0) := x in
          let (y0, f0) := y in
          let (a1, a2) := y0 in if In2 (a1, a2) l then (a1, a2 + M, f0, t0) else cast x) g1)))).
    eapply no_dup_removeEntry_no_dup,no_dup_shift...
    eapply no_dup_isMap in nd_pfk1 as pfk1.
     assert (nd_pfk2: NoDup (domain (removeEntry (n1, n2)
      (map
         (fun x : name * name * flag * piType =>
          let (y, t0) := x in
          let (y0, f0) := y in
          let (a1, a2) := y0 in if In2 (a1, a2) l then (a1, a2 + M, f0, t0) else cast x) g2)))).
    eapply no_dup_removeEntry_no_dup,no_dup_shift...
    eapply no_dup_isMap in nd_pfk2 as pfk2.

     assert (nd_pfk3: NoDup (domain (removeEntry (n1, n2)
      (map
         (fun x : name * name * flag * piType =>
          let (y, t0) := x in
          let (y0, f0) := y in
          let (a1, a2) := y0 in if In2 (a1, a2) l then (a1, a2 + M, f0, t0) else cast x) g3)))).
    eapply no_dup_removeEntry_no_dup,no_dup_shift...
    eapply no_dup_isMap in nd_pfk3 as pfk3.

    eapply in2_nIn_iff in IN2 as NIN.
     remember (match f with | hid => ill | _ => f end ) as F.
     remember (match g with | hid => ill | _ => g end ) as G.
     remember (match f' with | hid => ill | _ => f' end ) as F1.

    eapply SpTop with
        (n := (n1, n2)) (pf' := pfk1) (pf'' := pfk2)
    (pf''' := pfk3) (f := F) (g := G) (f' := F1);
      try erewrite  in_map_iff.
    destruct f, g, f'; subst; try inversion H...
    try exists (n1, n2, f, Top);
                 try rewrite IN2; try destruct f; simpl; subst...
    try exists (n1, n2, g, Top);
                   try rewrite IN2; try destruct g; simpl; subst...
    assert (IH : max (domain (removeEntry (n1, n2) g3)) <= M). eauto.

    eapply IHTS  with (pf' := pff') (pf'' := pff'') (pf''' := pff''')in IH; move IH at bottom.
    revert dependent pfk1.
    revert dependent pfk2.
    revert dependent pfk3.
    erewrite <-shift_removeEntry_2 with (M := M),
       <-shift_removeEntry_2 with (M := M),<-shift_removeEntry_2 with (M := M); intros.
    eapply split_cons_remove.split_pf...

    eauto.
    eauto.
    assert (n2 <= max (domain g1));
      try eapply in_preserves_max;
      try transitivity (max (domain g1))...
    eauto.
    eauto.
    eauto.
     assert (n2 <= max (domain g2));
      try eapply in_preserves_max;
      try transitivity (max (domain g2))...
    eauto.
    eauto.
    eauto.
     assert (n2 <= max (domain g3));
      inversion H3; try eapply in_preserves_max;
      try transitivity (max (domain g3))...
    eauto.
    eauto.
    eauto.
    
    inverts H3; inverts H4.
    assert (EQ: f' = f0 /\ t = Top).
    eapply in_isMap with (g := g3)...
    destruct EQ; subst f0 t F1.
      econstructor;
        eapply in_map_iff;
        try exists ((n1, n2, f', Top));
                     try rewrite IN2;
                     try destruct f';
                     simpl...

    inverts H3; inverts H4.
    assert (EQ: f' = f0 /\ t = Top).
    eapply in_isMap with (g := g3)...
    destruct EQ; subst f0 t F1;                    
eapply T_Entry with (f := snd (fst (cast (n1, n2, f', Top))));
eapply in_map_iff;
  try exists ((n1, n2, f', Top));
               try rewrite IN2;
               try destruct f';
             simpl...

              + eauto.
             +  eauto.
             + eauto.
             + eauto.
             +  eauto.
             + eauto.

             Unshelve.
             all:eapply map_is_map...
Qed.

Lemma eq_removeEntry: forall a1 a2 ff tt g,
    NoDup (domain ((a1, a2, ff, tt) :: g)) ->
    removeEntry (a1, a2) g = g.
Proof with eauto.
  introv pf; eapply removeEntry_idempot; try intros ABS;
    simpl in pf; inversion pf...
Qed.


Lemma remove_match {A}: forall eq_dec a n (l : list A),
    In a l ->
    ~ In a (remove eq_dec n l) ->
    n = a.
Proof with eauto.
  introv IN NIN; assert (NIN2 := NIN);
    eapply in_split in IN as (l1 &l2 &IN); subst.
  eapply notin_remove with (eq_dec := eq_dec) in NIN;
    rewrite remove_app in NIN; simpl in NIN.
  case_eq (eq_dec n a); intros; try rewrite H in *;
    repeat  rewrite remove_app in NIN; simpl in NIN...
  case_eq (eq_dec a a); intros; try rewrite H0 in *; try intuition.
  rewrite notin_remove in NIN; try intros ABS...
  rewrite notin_remove with (l := (remove eq_dec n l2)) in NIN; try intros ABS...
  assert (LEN:
            List.length
              ( remove eq_dec n l1 ++ remove eq_dec n l2) =
            List.length
              (remove eq_dec n l1 ++ a :: remove eq_dec n l2)).
  rewrite NIN...
  repeat rewrite app_length in LEN; simpl in LEN... lia.
  all:rewrite remove_app in NIN2;
    eapply not_in_app_and in NIN2; destruct NIN2 as [_ NIN2];
      simpl in NIN2; rewrite H in *; intuition.
Qed.  
  
#[global] Hint Resolve eq_removeEntry remove_match.

Lemma eq_map_no_dup: forall f k n n0 l M g (nd_pf: NoDup (domain g)), 
  f =
         (fun x : name * name * flag * piType =>
          let (y, t0) := x in
          let (y0, f) := y in
          let (a1, a2) := y0 in if In2 (a1, a2) l then (a1, a2 + M, f, t0) else cast x) ->
  k =
         (fun x : name * name * flag * piType =>
          let (y, t0) := x in
          let (y0, f) := y in
          let (a1, a2) := y0 in
          if In2 (a1, a2) (List.remove nat_pair_eq_dec (n, n0) l)
          then (a1, a2 + M, f, t0)
          else cast x) ->
 map f (removeEntry (n, n0) g) =
 map k (removeEntry (n, n0) g).
Proof with eauto.
  intros f k n n0 l M g nd_pf Heqf Heqk.
  dependent induction g; simpl; try destruct a as [[[a1 a2] ff] tt];try case_eq(pair_eq (a1, a2) (n, n0));intros...
  rewrite <-pairEq_eq in H; inversion H; subst n n0.
  assert (EQ: removeEntry (a1, a2) g = g)...
  rewrite <-EQ...
  simpl; rewrite IHg...
  assert (EQ:  f (a1, a2, ff, tt)  =
           k (a1, a2, ff, tt)).
  subst...
  case_eq (In2 (a1, a2) l); intros.
  - case_eq (In2 (a1, a2) (List.remove nat_pair_eq_dec (n, n0) l)); intros...
  rewrite in2_In_iff,in2_nIn_iff in *.
  assert (EQ: (n, n0) = (a1, a2))...
  assert (EQ2 : pair_eq (a1, a2) (a1, a2) = true). eapply pairEq_eq...
  rewrite EQ, EQ2 in H; discriminate.
  - case_eq (In2 (a1, a2) (List.remove nat_pair_eq_dec (n, n0) l)); intros...
    rewrite in2_In_iff,in2_nIn_iff in *.
   eapply in_remove in H1; intuition.
  - rewrite EQ...
Qed.

Lemma inverse_newEntries: forall p g a1 a2  f t (pf : isMap g),
    sl_pos p ->
    incl (secLabs p) (domain g) ->  
    In (a1, a2, f, t)
       (newEntries g
                   (map (fun x : name * name => (fst x, snd x + max (domain g))) (secLabs p)) (max (domain g))) ->
    In (a1, a2 - max (domain g)) (secLabs p) /\
    In (a1, a2 - max (domain g), f, t) g.
Proof with eauto.
  intros p g a1 a2  f t pf  SLP INCL IN.
  unfold sl_pos, pos in SLP.
  induction (secLabs p).
  - simpl in IN; eauto;unfold incl,domain in INCL;try specialize INCL with p0; try assert (IN2: In p0 (p0 :: l)); eauto;try eapply INCL in IN2; try contradiction.
  -  destruct a as [b1 b2]; simpl in IN;
     unfold newEntries in IN; fold newEntries in IN.
     case_eq (InB (b1, b2 + max (domain g)) g); intros.
     case_eq b; intros; subst; rewrite H in *.
     eapply inB_implies_In in H as (ff &tt &IN2).
     assert (ABS: b2 + max (domain g) <= max (domain g)).
     eapply in_g_in_domain in IN2;
       eapply in_preserves_max...
     assert (b2 = 0) by lia.
      assert (In (b1, b2) ((b1, b2) :: l))... rewrite H...
     unfold sl_pos,pos in SLP; specialize SLP with b1 b2;
       eauto; intuition.
     assert (EQ : b2 + max (domain g) - max (domain g) = b2 ) by lia. rewrite EQ in *.
     assert (IN2 : In (b1, b2) (domain g)). eapply INCL...
     eapply in_domain_in_g in IN2 as (ff &tt &IN2).
     eapply in_implies_InB in IN2;
       try rewrite IN2 in *; simpl in IN; try destruct IN as [A | B]; try inversion A; subst;
         try rewrite EQ in *.
     split...
     try eapply inB_implies_In_2 with (p := (f, t))...
     assert (IH: In (a1, a2 - max (domain g)) l /\ In (a1, a2 - max (domain g), f, t) g).
     eapply IHl... intros; specialize SLP with x1 x2; intuition.
     eapply incl_cons_inv...
     intuition.
     assumption.
Qed.
     
 Lemma newEntries_gte_max: forall g l m a1 a2 f t,
    In (a1, a2, f, t)
       (newEntries g
                   (map (fun x : name * name => (fst x, snd x + m)) l) m) ->
    m <= a2.
 Proof with eauto.
   intros g l m a1 a2 f t IN.
   induction l; simpl in IN; try contradiction.
   destruct (InB (fst a, snd a + m) g).
   destruct b...
   assert (EQ: snd a + m - m = snd a) by lia.
   rewrite EQ in *.
   destruct (InB (fst a, snd a) g).
   destruct b.
   all: destruct IN as [A | B]; eauto;
     inversion A; subst; lia.
 Qed.

 Lemma isMap_single : forall a,
     isMap (a :: nil).
 Proof with eauto.
   intros [[[a1 a2] f] t]; unfold isMap; intros; destruct H; inversion H; inversion H0;inversion H1; inversion H2; subst; intuition.
 Qed.

 #[global] Hint Resolve isMap_single.
 
Lemma isMap_single_removeEntry : forall a b,
     isMap (removeEntry b (a :: nil)).
 Proof with eauto.
   intros [[[a1 a2] f] t]; unfold isMap; intros; destruct H;
     try case_eq (pair_eq (a1,a2) b); intros; simpl in *; rewrite H1 in *; inversion H;
       try inversion H0; try inversion H2; inversion H3; subst; intuition.
 Qed.

 #[global] Hint Resolve isMap_single_removeEntry.

 Lemma cons_map: forall g pf1 l mx pf2,
     NoDup (domain g) ->
     pos l ->
     max (domain g) <= mx ->
   cons g pf1 ->
   cons
    (map
       (fun x : name * name * flag * piType =>
        let (y, t) := x in
        let (y0, f) := y in
        let (a1, a2) := y0 in if In2 (a1, a2) l then (a1, a2 + mx, f, t) else cast x)
       g) pf2.
 Proof with eauto.
   introv nd_pf; intros. dependent induction g. simpl...
   assert (pfg := pf1). eapply isMap_cons in pfg.
   destruct a as [[[a1 a2] ff] tt].
   remember  (fun x : name * name * flag * piType =>
              let (y, t) := x in
              let (y0, f) := y in
              let (a3, a4) := y0 in
              if In2 (a3, a4) l
              then (a3, a4 + mx, f, t)
              else cast x) as k.
    
      assert (EQ0:  (a1, a2, ff, tt) :: g = 
                    ((a1, a2, ff, tt) :: nil) ++ g).
      eauto.
      
      assert (EQ: k (a1, a2, ff, tt) :: map k g =
                  (k (a1, a2, ff, tt) :: nil) ++ map k g).
     eauto.
     revert dependent pf2; erewrite map_cons,EQ; intros.
     
     assert (pf: isMap (map k ((a1, a2, ff, tt)::nil))).
     subst; eapply map_is_map; try assumption;
       try eapply cons_max in H0; simpl...
     revert dependent pf1. rewrite EQ0; intros.
     assert (pf' : isMap (k (a1, a2, ff, tt) :: nil)).
     eauto.
     assert (pf'' : isMap (map k g )).
     subst; eapply map_is_map; try eapply max_cont in H0;inv nd_pf;
       try assumption.
     try rewrite cons_distr in H1; rewrite cons_distr with (pf1 := pf') (pf2 := pf''); intuition.
     subst k.
     revert dependent pf';
       case_eq (In2 (a1, a2) l); intros; inv H2;
         try discriminate; inv H4; inv H2; inv H4.
     eapply Co_top...
     eapply Co_un...
     eapply Co_lin...
     try destruct f; simpl; try eapply Co_top...
     try destruct f; simpl; try eapply Co_un...
     try destruct f; simpl; try eapply Co_lin...
     subst; eapply IHg...
     eapply max_cont in H0...
     Unshelve. all:eauto.
 Qed.


 #[global] Hint Resolve cons_map.

 
