Require Import List PeanoNat Bool Classical Lia Program.Equality Classical
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
        type_checking_1
        lts_no_dup 
        proposition27
        disjoint_newEntries
        tc_prelim
        type_system_rules.

Require Import CpdtTactics LibTactics. 


#[global] Hint Resolve typeCheck_rewrite_pf.



Definition castF f t :=
  if flag_eq f hid || flag_eq f ill
  then
    match t with
    | Chan lin _ t => (ill, Chan lin empty t)
    | _ => (ill, t)
    end
  else
    (f, t).

Definition cast (e : (name * name) * flag * piType) :=
  match e with
  | (a1, a2, f, t)  =>
    (a1, a2, fst (castF f t), snd (castF f t))
  end.

Definition illECast g := List.map cast g.

Fixpoint illEProj (g : typeEnv) l :=
  match g with
  | nil => nil
  | (a1, a2, hid, t) as x :: tl =>
    if In2 (a1, a2) l 
    then
      cast x :: illEProj tl l
    else
      illEProj tl l
  | x :: tl =>
    illEProj tl l
  end.

Lemma in2_false_illECast: forall x f t g,
    f = vis ->
    In (x, f, t) g ->
    In (x, f, t) (illECast g).
Proof with eauto.
  introv EQ IN.
  induction g;
    subst;
    try destruct a as [[[a1 a2] f1] t1];
    try unfold illECast in *;
    inversion IN;
    try inversion H;
    simpl...
  Qed. 

#[global] Hint Resolve in2_false_illECast.

Lemma illEC_eq_domain: forall g,
    domain (illECast g) = domain g.
Proof with eauto.
  induction g;
    subst;
    try destruct a as [[[a1 a2] f1] t1];
    try unfold illECast in *;
    try inversion H;
    simpl;
    try rewrite IHg...
Qed.




#[global] Hint Resolve pos_cons.

  
Lemma no_dup_shift: forall l g (nd_pf : NoDup (domain g)) n,
    pos l ->
    max (domain g) <= n ->
    NoDup (domain 
             (map (fun x =>
                     match x with
                       (a1, a2, f, t) =>
                       if In2 (a1, a2) l
                       then
                         (a1, a2 + n, f, t)
                       else
                         cast x
                     end) g)).
Proof with eauto.
  intros l g nd_pf n POS. intros. dependent induction g.
  - rewrite map_nil_eq...
  - destruct a as [[[a1 a2] f1] t1].
    assert (MAX := H).
    unfold domain in H; fold domain in H.
    unfold max in H; fold max in H.
    specialize IHg with n. 
    assert (nd_pf1 := nd_pf).
    unfold domain in nd_pf; fold domain in nd_pf.
    rewrite NoDup_cons_iff  in nd_pf. intuition.
    rewrite map_cons.
    case_eq (In2 (a1, a2) l); intros.
    + unfold domain; fold domain;  rewrite NoDup_cons_iff.
      split. intro ABS.
      apply in_domain_in_g in ABS.
      destruct ABS as [f2 [t2 IN]].
      rewrite in_map_iff in IN.
      destruct IN as [x IN]; destruct x as [[[b1 b2] f3] t3].
      intuition.
      case_eq (In2 (b1, b2) l); intros.
      rewrite H6 in H4.
      inversion H4. assert (b2 = a2). lia. subst.
      apply in_g_in_domain in H5...
      rewrite H6 in H4. inversion H4.
      destruct (castF f3 t3); inversion H8; subst.  
      apply in_g_in_domain, in_preserves_max in H5.
      subst;
        assert (a2 = 0).
      case_eq (a2 <? max (domain g)); intros; rewrite H8 in H. lia.
      rewrite Nat.ltb_ge in H8. lia.
      rewrite in2_In_iff in H2;
        unfold pos in POS; specialize POS with a1 a2; intuition.
      (*assert (pos (domain g)). eapply pos_cons...*)
      unfold domain in MAX; fold domain in MAX.
      assert ( max ( domain g) <= n).
      erewrite max_cons...
      intuition.
    + unfold cast; fold cast. 
      unfold domain, cast; fold domain.
      destruct  (castF f1, t1).
      apply NoDup_cons_iff.
      (*assert (pos (domain g)). eapply pos_cons...*)
      unfold domain in MAX; fold domain in MAX.
      assert ( max ( domain g) <= n).
      erewrite max_cons...
      intuition.
      apply in_domain_in_g in H3.
      destruct H3 as [f2 [t2 IN]].
      rewrite in_map_iff in IN.
      destruct IN as [x [EQ IN]]. destruct x as [[[b1 b2] f3] t3].
      case_eq (In2 (b1, b2) l); intros.
      rewrite H3 in EQ. inversion EQ.
      assert (a2 <= n). eapply cons_max...
      assert (b2 = 0). lia.
      rewrite in2_In_iff in H3;
        unfold pos in POS; specialize POS with b1 b2; intuition.
      assert (a2 <= n). eapply cons_max...
      rewrite H3 in EQ. inversion EQ; subst.
      eapply in_g_in_domain in IN...
Qed.




Lemma shift_removeEntry: forall n n0 g l M,
    pos l ->
    n0 <= M ->
    map
      (fun x : name * name * flag * piType =>
         let (y, t0) := x in
         let (y0, f0) := y in
         let (a1, a2) := y0 in
         if In2 (a1, a2) (List.remove nat_pair_eq_dec (n, n0) l)
         then (a1, a2 + M, f0, t0)
         else cast x) (removeEntry (n, n0) g) =
    removeEntry
      (n, n0)
      (map
         (fun x : name * name * flag * piType =>
            let (y, t0) := x in
            let (y0, f0) := y in
            let (a1, a2) := y0 in
            if In2 (a1, a2) (List.remove nat_pair_eq_dec (n, n0) l)
            then (a1, a2 + M, f0, t0)
            else cast x) g).
Proof with eauto.
  intros n n0 g l M POS LEQ.
  induction g.
  rewrite map_nil_eq...
  remember (fun x : name * name * flag * piType =>
              let (y, t0) := x in
              let (y0, f0) := y in
              let (a1, a2) := y0 in
              if In2 (a1, a2) (List.remove nat_pair_eq_dec (n, n0) l)
              then (a1, a2 + M, f0, t0)
              else cast x) as f.
  rewrite map_cons. destruct a as [[[a1 a2] f1] t1]. 
  unfold removeEntry at 1; fold removeEntry.
  case_eq (pair_eq (a1, a2) (n, n0)); intros EQ.
  rewrite <-pairEq_eq in EQ; inversion EQ.
  assert (EQ2: f (n, n0, f1, t1) = (n, n0, fst (castF f1 t1), snd (castF f1 t1))).
  subst f. assert (In2 (n, n0) (List.remove nat_pair_eq_dec (n, n0) l) = false).  assert (~In (n, n0) (List.remove nat_pair_eq_dec (n, n0) l)). apply remove_In...
  rewrite <-in2_In_iff in H.
  case_eq (In2 (n, n0) (List.remove nat_pair_eq_dec (n, n0) l)); intros. intuition; tauto. tauto.
  rewrite H... rewrite EQ2; unfold removeEntry; fold removeEntry. assert (pair_eq (n, n0) (n, n0) = true)... rewrite H...
  rewrite map_cons.
  assert (removeEntry (n, n0) (f (a1, a2, f1, t1) :: map f g) = f (a1, a2, f1, t1) :: removeEntry (n, n0) (map f g)).
  rewrite Heqf.
  case_eq (In2 (a1, a2) (List.remove nat_pair_eq_dec (n, n0) l)); intros. rewrite <-Heqf.
  unfold removeEntry at 1; fold removeEntry.
  assert (pair_eq (a1, a2 + M) (n, n0) = false).
  assert (n0 < a2 + M).
  rewrite in2_In_iff in H.
  apply in_remove in H.
  unfold pos in POS; specialize POS with a1 a2; intuition.
  rewrite <-pairEq_neq; intro ABS; inversion ABS; subst; intuition.
  rewrite H0... 
  rewrite <-Heqf.
  unfold removeEntry at 1; fold removeEntry.
  unfold cast; fold cast...
  rewrite EQ...
  rewrite IHg...
Qed.




#[global] Hint Resolve pos_remove.


#[global] Hint Resolve in_iff_swap.

Lemma map_is_map: forall g l M,
    pos l ->
    max (domain g) <= M ->
    NoDup (domain g) ->
    isMap
      (map
            (fun x : name * name * flag * piType =>
               let (y, t0) := x in
               let (y0, f0) := y in
               let (a1, a2) := y0 in
               if In2 (a1, a2) l
               then (a1, a2 + M, f0, t0)
               else cast x) g).
Proof with eauto using max_cont.
  introv POS MAX nd_pf; induction g.
  
  try rewrite map_nil_eq...
  destruct a as [[[a1 a2] f] t]; simpl;
    eapply no_dup_isMap in nd_pf as pf;
    eapply isMap_cons in pf; intuition.
  case_eq(In2 (a1, a2) l); intros.
    - eapply isMap_not_in.
  intro  ABS;
    try eapply in_domain_in_g in ABS as (ff &tt &ABS); try erewrite in_map_iff in ABS;
      try destruct ABS as ([[[x1 x2] fx1]ft1] &ABSEQ &ABS).
  case_eq (In2 (x1, x2) l); intros; rewrite H0 in *; inv ABSEQ. assert (x2 = a2). lia. subst.
  simpl in nd_pf; inv nd_pf...
  assert (a2+M <= max (domain g)).
  eapply in_preserves_max...
  eapply max_cont in MAX.
  assert (a2 = 0) by lia.
  rewrite in2_In_iff in *; unfold pos in *.
  specialize POS with a1 a2; intuition.
  
  eapply IHg; inv nd_pf...
    - eapply isMap_not_in.
       assert (a2 <= M).
       eapply cons_max...
 intro  ABS;
    try eapply in_domain_in_g in ABS as (ff &tt &ABS); try erewrite in_map_iff in ABS;
      try destruct ABS as ([[[x1 x2] fx1]ft1] &ABSEQ &ABS).
      case_eq (In2 (x1, x2) l); intros; rewrite H1 in *; inv ABSEQ.
  assert (x2 = 0) by lia.
  rewrite in2_In_iff in *; unfold pos in *.
  specialize POS with a1 x2; intuition.
  inv nd_pf...
  eapply IHg...  
Qed.

  Lemma var_not_in_map : forall x g l M,
    ~ In x (domain g) ->
    ~ In x l ->
    snd x < M ->
    ~ In x
      (domain
         (map
            (fun x : name * name * flag * piType =>
               let (y, t0) := x in
               let (y0, f0) := y in
               let (a1, a2) := y0 in
               if In2 (a1, a2) l
               then (a1, a2 + M, f0, t0)
               else cast x) g)).
  Proof with eauto.
    introv NIND NIN LT ABS.
    eapply in_domain_in_g in ABS as (f &t &ABS).
    rewrite in_map_iff in ABS.
    destruct ABS as ([[[x1 x2] ff] tt] &ABS &IN).
    case_eq (In2 (x1, x2) l); intros; rewrite H in *; inversion ABS; subst; simpl in *; try lia.
    eapply in_g_in_domain in IN; contradiction.
  Qed.
  
Lemma max_map : forall g l M,
    max (domain g) <=
    max (domain
           (map
              (fun x : name * name * flag * piType =>
                 let (y, t0) := x in
                 let (y0, f0) := y in
                 let (a1, a2) := y0 in
                 if In2 (a1, a2) l
                 then (a1, a2 + M, f0, t0)
                 else cast x) g)).
Proof with eauto.
  intros.
  case_eq( max (domain g) =? 0); intros.
  rewrite Nat.eqb_eq in *; rewrite H; lia.
  rewrite Nat.eqb_neq in *.
  assert (IN: exists y, In (y, max (domain g)) (domain g)).
  eapply max_in_domain...
  destruct IN as (a1 &IN).
  eapply in_domain_in_g in IN as (ff &tt &IN).
  eapply in_map with (f := (fun x : name * name * flag * piType =>
           let (y, t0) := x in
           let (y0, f0) := y in
           let (a0, a2) := y0 in if In2 (a0, a2) l then (a0, a2 + M, f0, t0) else cast x)) in IN.
  case_eq ((if In2 (a1, max (domain g)) l
          then (a1, max (domain g) + M, ff, tt)
          else cast (a1, max (domain g), ff, tt))); intros [[p1 p2] ff1]; intros; rewrite H0 in *.
  eapply in_g_in_domain in IN.
  assert (max (domain g) <= p2).
  case_eq (In2 (a1, max (domain g)) l); intros EQ;
  rewrite EQ in *; inversion H0; subst; lia...       
  eapply in_preserves_max in IN.
  lia.
Qed.


  

    #[global] Hint Resolve incl_cons inB_implies_In_2.

  
#[global] Hint Resolve in2_implies_in.

Lemma incl_illEP_illEC : forall g l,
    incl (illEProj g l) (illECast g).
Proof with eauto.
  unfold incl,illECast;intros; induction g.
  inversion H.
  destruct a as [[[a1 a2] f1] t1],a0 as [[[b1 b2] f2] t2], f2.
  unfold illEProj in H; fold illEProj in H;
    case_eq (In2 (a1, a2) l); intros IN; try rewrite IN in *;
      case_eq (In2 (b1, b2) l); intros IN2;try rewrite IN2 in *;
      try inversion H.
  erewrite map_cons,H0... intuition auto; erewrite map_cons; right...
  all:unfold illEProj in H; fold illEProj in H; try inversion H;
    erewrite map_cons;  try simpl in H0; try inversion H0; subst; simpl...
Qed.




Lemma bv_disjoint_g : forall p g (nd_pf : NoDup (domain g)) pf,
    typeCheck g pf p ->
    disjoint (bv p) (domain g).
Proof with eauto.
  introv nd_pf TC.
  eapply typeCheck_object_neq_subject in TC as NR.
    induction TC;simpl...
  - assert (ND: NoDup (domain ((n, vis, t) :: removeEntry n g))).
    eapply no_dup_cons_removeEntry...  
    eapply IHTC in ND.
    apply Peirce. intros ABS.
    eapply not_disjoint in ABS as (x &ABS1 &ABS2).
    eapply disjoint_absurd with (P := False) in ND; try contradiction...
    case_eq (pair_eq n x); intros PEQ; try rewrite <-pairEq_eq in PEQ; subst;simpl...
    eapply in_domain_in_g in ABS2 as (ff & tt &ABS2); eapply pairEq_neq in PEQ;
      try right; try eapply in_g_in_domain,removeEntry_in...
    simpl in NR...
    - apply Peirce; intros ABS.
     eapply not_disjoint in ABS as (x &ABS1 &ABS2).
     assert (ND1: NoDup (domain g1))...
     assert (ND2: NoDup (domain g2))...
     eapply IHTC1 in ND1;
       eapply IHTC2 in ND2...
     eapply in_app_iff in ABS1 as [ABS1 | ABS1].
     eapply disjoint_absurd with (P := False) in ND1; try contradiction...
     eapply split_domain_l_2...
     eapply disjoint_absurd with (P := False) in ND2; try contradiction...
      eapply split_domain_r...
    - apply Peirce; intros ABS.
     eapply not_disjoint in ABS as (x &ABS1 &ABS2).
     assert (ND:  NoDup (domain ((u, vis, t1) :: (v, vis, t2) :: removeEntry v (removeEntry u g)))).      simpl; econstructor; try intros ABS3;
                                                                                                            try inv ABS3; try simpl in NR; intuition...
     eapply in_domain_in_g in H3 as (ff &tt&IN);
       eapply in_removeEntry in IN.
     assert (~In (u,ff,tt) (removeEntry u g))...
     simpl; econstructor; try intros ABS3;
                                                                                                            try inv ABS3; try simpl in NR; intuition...
     eapply in_domain_in_g in ABS3 as (ff &tt&IN)...
     assert (~(In (v, ff, tt) (removeEntry v (removeEntry u g))))...
     eapply IHTC in ND.
     eapply disjoint_absurd with (P := False) in ND; try contradiction...
     case_eq (pair_eq x u); intros PEQ;
       try rewrite <-pairEq_eq in PEQ; subst...
     case_eq (pair_eq x v); intros PEQ2;
       try rewrite <-pairEq_eq in PEQ2; subst...
     simpl; repeat right...
     eapply in_domain_in_g in ABS2 as (ff &tt &ABS2);
       eapply pairEq_neq in PEQ;
       eapply pairEq_neq in PEQ2;
       eapply in_g_in_domain, removeEntry_in, removeEntry_in...
     simpl in NR...
-    apply Peirce; intros ABS.
     eapply not_disjoint in ABS as (x &ABS1 &ABS2).
     assert (ND:  NoDup (domain ((v, vis, t2) :: removeEntry v g))).
     eapply no_dup_cons_removeEntry...
      eapply IHTC in ND.
     eapply disjoint_absurd with (P := False) in ND; try contradiction...
     case_eq (pair_eq x v); intros PEQ2;
       try rewrite <-pairEq_eq in PEQ2; subst...
     eapply pairEq_neq in PEQ2; eapply in_domain_in_g in ABS2 as (ff &tt &ABS2). simpl; right; try eapply in_g_in_domain, removeEntry_in...
     simpl in NR...
- assert (ND: NoDup (domain ((u, vis, t1) :: (x, vis, t) :: removeEntry u g))).
  eapply no_dup_cons_removeEntry_app_1...
  intros ABS3; subst; eapply in_g_in_domain in H0; try contradiction.
  eapply IHTC in ND.
  split; try intros ABS;
    try rewrite <-surjective_pairing in ABS...
   apply Peirce; intros ABS.
     eapply not_disjoint in ABS as (y &ABS1 &ABS2).
   eapply disjoint_absurd with (P := False) in ND; try contradiction...
    case_eq (pair_eq y u); intros PEQ; try rewrite <-pairEq_eq in PEQ; subst;simpl...
    eapply in_domain_in_g in ABS2 as (ff &tt &ABS2);
      eapply pairEq_neq in PEQ; repeat right;
        try eapply in_g_in_domain,removeEntry_in...
    simpl in NR...
- assert (ND: NoDup (domain ((x, vis, t) :: g))).
  simpl; econstructor; try intros ABS;
  try eapply in_domain_in_g in ABS as (ff1 &tt1&ABS)...
  eapply IHTC in ND.
  split; try intros ABS;
    try rewrite <-surjective_pairing in ABS...
   apply Peirce; intros ABS.
     eapply not_disjoint in ABS as (y &ABS1 &ABS2).
   eapply disjoint_absurd with (P := False) in ND; try contradiction...
    case_eq (pair_eq y u); intros PEQ; try rewrite <-pairEq_eq in PEQ; subst;simpl...
    simpl in NR...
    - assert (ND: NoDup (domain ((x, vis, t) :: g))).
  simpl; econstructor; try intros ABS;
  try eapply in_domain_in_g in ABS as (ff1 &tt1&ABS)...
  eapply IHTC in ND.
  split; try intros ABS;
    try rewrite <-surjective_pairing in ABS...
   apply Peirce; intros ABS.
     eapply not_disjoint in ABS as (y &ABS1 &ABS2).
   eapply disjoint_absurd with (P := False) in ND; try contradiction...
    case_eq (pair_eq y u); intros PEQ; try rewrite <-pairEq_eq in PEQ; subst;simpl...
    simpl in NR...
Qed.

Lemma typeCheck_is_vis:
  forall (n : name * name) (g : typeEnv) (pf : isMap g) (p : dproc),
    typeCheck g pf p -> In n (fn p) -> exists t : piType,
        In (n, vis, t) g.
Proof with eauto.
  introv TC IN.
  eapply typeCheck_object_neq_subject in TC as NR.
  induction TC;simpl in IN;
    try rewrite <-surjective_pairing in *;
    try contradiction...
  - eapply in_remove in IN as(IN &DIFF);
      eapply IHTC in IN as (s &IN);
      try exists s; try inv IN; try inv H0; intuition...    
  - eapply in_app_iff in IN; inverts IN as IN;try eapply IHTC1 in IN; try eapply IHTC2 in IN; try destruct IN as (s &IN)...
    destruct n; eapply fsub_vis in IN; try inv IN...
    destruct n; eapply fsub_vis_r in IN; try inv IN...
  - try rewrite <-surjective_pairing in *;
      destruct IN as [IN | [IN|IN]]; subst.
    exists (Chan lin p t)...
    exists t'...
    eapply IHTC in IN; try destruct IN as (s &IN);
      try inverts IN as IN; try inv IN; try inv H3...
  - try rewrite <-surjective_pairing in *;
      destruct IN as [IN | [IN|IN]]; subst.
    exists (Chan un p t)...
    exists t'...
    eapply IHTC in IN; try destruct IN as (s &IN);
      try inverts IN as IN; try inv IN; try inv H3...    
  - try rewrite <-surjective_pairing in *.
    case_eq (nat_pair_eq_dec x u); introv PEQ; rewrite PEQ in *.
    eapply in_remove in IN as (IN &DIFF); eapply IHTC in IN;
      try destruct IN as (s &IN); try inv IN; try inv H3; try inv H4; subst...
    inv IN.
    exists (Chan lin p t)...
    eapply in_remove in H3 as (IN &DIFF); eapply IHTC in IN;
      try destruct IN as (s &IN); try inv IN; try inv H3; try inv H4; subst; try contradiction...
  - try rewrite <-surjective_pairing in *.
    case_eq (nat_pair_eq_dec x u); introv PEQ; rewrite PEQ in *.
    eapply in_remove in IN as (IN &DIFF); eapply IHTC in IN;
      try destruct IN as (s &IN); try inv IN; try inv H3; try inv H4; subst...
    inv IN.
    exists (Chan un p t)...
    eapply in_remove in H3 as (IN &DIFF); eapply IHTC in IN;
      try destruct IN as (s &IN); try inv IN; try inv H3; try inv H4; subst; try contradiction...
  - try rewrite <-surjective_pairing in *.
    case_eq (nat_pair_eq_dec x u); introv PEQ; rewrite PEQ in *.
    eapply in_remove in IN as (IN &DIFF); eapply IHTC in IN;
      try destruct IN as (s &IN); try inv IN; try inv H3; try inv H4; subst...
    inv IN.
    exists (Chan un p t)...
    eapply in_remove in H4 as (IN &DIFF); eapply IHTC in IN;
      try destruct IN as (s &IN); try inv IN; try inv H3; try inv H4; subst; try contradiction...
Qed.

Lemma fn_disjoint_sl : forall p g (nd_pf : NoDup (domain g)) pf,
    typeCheck g pf p ->
    disjoint (fn p) (secLabs p).
Proof with eauto.
  introv nd_pf TC.
  eapply typeCheck_object_neq_subject in TC as NR.
    induction TC...
  - simpl; rewrite <-surjective_pairing in *.
    assert (ND: NoDup (domain ((n, vis, t) :: removeEntry n g))).
    eapply no_dup_cons_removeEntry...  
    eapply IHTC in ND.
    apply Peirce. intros ABS.
    eapply not_disjoint in ABS as (x &ABS1 &ABS2).
    eapply disjoint_absurd with (P := False) in ND; try contradiction...
    specialize remove_In with (eq_dec := nat_pair_eq_dec)
(x := x) (l:=fn p) as NIN. 
    case_eq (pair_eq n x); intros PEQ; try rewrite <-pairEq_eq in PEQ; subst;simpl;try contradiction.
    eapply in_remove...
     specialize remove_In with (eq_dec := nat_pair_eq_dec)
(x := x) (l:=fn p) as NIN.
    case_eq (pair_eq n x); intros PEQ; try rewrite <-pairEq_eq in PEQ; subst;simpl; try contradiction.
    eapply pairEq_neq in PEQ.
    eapply in_app_iff in ABS2; inversion ABS2;
      intuition.
    try inversion H1;
      intuition.
    simpl in NR...
    - apply Peirce; intros ABS.
     eapply not_disjoint in ABS as (x &ABS1 &ABS2).
     assert (ND1: NoDup (domain g1))...
     assert (ND2: NoDup (domain g2))...
     eapply IHTC1 in ND1;
       eapply IHTC2 in ND2...
     eapply in_app_iff in ABS1 as [ABS1 | ABS1].
     eapply in_app_iff in ABS2 as [ABS2 | ABS2].
     assert (ABS3: exists t : piType, In (x, hid, t) g2)...
     destruct ABS3 as (t&ABS3).
     eapply typeCheck_is_vis in TC1 as (s &VIS)...
     eapply in_g_in_domain in VIS as IN4;
       erewrite split_domain_l in IN4;
       eapply in_domain_in_g in IN4 as (f &s' &IN4)...
     assert (ABS4: exists f2 : flag, flagOf g2 x f2 /\ flag_plus vis f2 f).
     eapply split_flag_plus...
     destruct ABS4 as (f2 &FYP &ABS5); inv FYP.
     assert (hid = f2 /\ t = t0)...
     intuition; subst; try inv ABS5...
     eapply disjoint_absurd with (P := False) in ND1; try contradiction...

     eapply in_app_iff in ABS2 as [ABS2 | ABS2].
     assert (ABS3: exists t : piType, In (x, hid, t) g2)...
     destruct ABS3 as (t&ABS3).
     eapply typeCheck_is_vis in TC2 as (s &VIS)...
     assert (hid = vis /\ t = s)...
     intuition; try discriminate...
     eapply typeCheck_is_vis in TC2 as (s &VIS)...
     eapply typeCheck_hid in TC1 as (s' &HID)...
     eapply in_g_in_domain in HID as IN4;
       erewrite split_domain_l in IN4;
       eapply in_domain_in_g in IN4 as (f &s'' &IN4)...
     assert (ABS4: exists f2 : flag, flagOf g2 x f2 /\ flag_plus hid f2 f).
     eapply split_flag_plus...
     destruct ABS4 as (f2 &FYP &ABS5); inv FYP.
     assert (vis = f2 /\ s = t)...
     intuition; subst; try inv ABS5...
    - apply Peirce; intros ABS;
     eapply not_disjoint in ABS as (x &ABS1 &ABS2).
      assert (ND:  NoDup (domain ((u, vis, t1) :: (v, vis, t2) :: removeEntry v (removeEntry u g)))).
      simpl; econstructor; try intros ABS3;
        try inv ABS3; try simpl in NR; intuition...
      try rewrite <-surjective_pairing in *;
     eapply in_domain_in_g in H3 as (ff &tt&IN);
       eapply in_removeEntry in IN.
     assert (~In (u,ff,tt) (removeEntry u g))...
     simpl; econstructor; try intros ABS3;
       try inv ABS3; try simpl in NR; intuition...
     eapply in_domain_in_g in ABS3 as (ff &tt&IN)...
     assert (~(In (v, ff, tt) (removeEntry v (removeEntry u g))))...
     eapply IHTC in ND.
     eapply disjoint_absurd with (P := False) in ND; try contradiction...
     case_eq (pair_eq x u); intros PEQ;
       try rewrite <-pairEq_eq in PEQ; subst; simpl in ABS2.
     assert (ABS3:
               exists t : piType, In (u, hid, t) ((u, vis, t1) :: (v, vis, t2) :: removeEntry v (removeEntry u g)))...
     destruct ABS3 as (s &ABS3).
     inverts ABS3 as ABS3; inv ABS3; try inv H3...
     eapply in_removeEntry in H3.
     assert (~In (u, hid, s) (removeEntry u g))...
     
     case_eq (pair_eq x v); intros PEQ2;
       try rewrite <-pairEq_eq in PEQ2; subst...
     assert (ABS3:
               exists t : piType, In (v, hid, t) ((u, vis, t1) :: (v, vis, t2) :: removeEntry v (removeEntry u g)))...
     destruct ABS3 as (s &ABS3).
     inverts ABS3 as ABS3; inv ABS3; try inv H3...
     assert (~In (v, hid, s) ((removeEntry v (removeEntry u g))))...
     eapply pairEq_neq in PEQ;
       eapply pairEq_neq in PEQ2; simpl in *;
         repeat (try rewrite <-surjective_pairing in *;
         subst; intuition).
     simpl in NR...
- apply Peirce; intros ABS;
     eapply not_disjoint in ABS as (x &ABS1 &ABS2).
  assert (ND:  NoDup (domain ((v, vis, t2) :: removeEntry v g))).
  eapply no_dup_cons_removeEntry...
     eapply IHTC in ND.
     eapply disjoint_absurd with (P := False) in ND; try contradiction...
     case_eq (pair_eq x u); intros PEQ;
       try rewrite <-pairEq_eq in PEQ; subst; simpl in ABS2.
     assert (ABS3:
               exists t : piType, In (u, hid, t) ((v, vis, t2) :: removeEntry v g))...
     destruct ABS3 as (s &ABS3).
     inverts ABS3 as ABS3; try inv ABS3; try inv H3...
     eapply in_removeEntry in ABS3.
     assert (vis = hid /\ Chan un p t = s)...
     intuition; try discriminate...
     
     case_eq (pair_eq x v); intros PEQ2;
       try rewrite <-pairEq_eq in PEQ2; subst...
     assert (ABS3:
               exists t : piType, In (v, hid, t) ((v, vis, t2) :: removeEntry v g))...
     destruct ABS3 as (s &ABS3).
     inverts ABS3 as ABS3; try inv ABS3; try inv H3...
     assert (~In (v, hid, s) (removeEntry v g))...
     eapply pairEq_neq in PEQ;
       eapply pairEq_neq in PEQ2; simpl in *;
         repeat (try rewrite <-surjective_pairing in *;
         subst; intuition).
     simpl in NR...

     
- assert (ND: NoDup (domain ((u, vis, t1) :: (x, vis, t) :: removeEntry u g))).
  eapply no_dup_cons_removeEntry_app_1...
  intros ABS3; subst; eapply in_g_in_domain in H0; try contradiction.
  eapply IHTC in ND.
try intros ABS;
    try rewrite <-surjective_pairing in ABS...
   apply Peirce; intros ABS.
     eapply not_disjoint in ABS as (y &ABS1 &ABS2).
   eapply disjoint_absurd with (P := False) in ND; try contradiction...
   case_eq (pair_eq y u); intros PEQ; try rewrite <-pairEq_eq in PEQ; subst;simpl in ABS2...
   specialize typeCheck_hid with (n := u) (pf := pf1) (p := q)
     as ABS3; eapply ABS3 in TC as (s &ABS4);
     try inv ABS4; try inv H3; try inv H4...
   assert (~In (u, hid, s) (removeEntry u g))...
   simpl in ABS1; repeat (rewrite <-surjective_pairing in *)...
   case_eq (nat_pair_eq_dec x u). intros.
   try rewrite H3 in *...                       
   eapply in_remove in ABS1 as (ABS1 &DIFF); subst...
   assert (TC2 := TC).
 specialize typeCheck_hid with (n := y) (pf := pf1) (p := q)
     as ABS3; eapply ABS3 in TC as (s &ABS4);
   try inv ABS4; try inv H3; try inv H4...
 intros. rewrite H3 in *; inv ABS1.
 assert (~ In (y, hid, s) (removeEntry y g))...
 eapply in_remove in H5 as (IN &DIFF).
 specialize typeCheck_is_vis with (n := y) (pf := pf1) (p := q)
     as ABS3'; eapply ABS3' in TC2 as (s' &ABS4);
     try inv ABS4; try inv H3; try inv H4...
simpl in NR... 
- assert (ND: NoDup (domain ((x, vis, t) :: g))).
  simpl; econstructor; try intros ABS;
  try eapply in_domain_in_g in ABS as (ff1 &tt1&ABS)...
  eapply IHTC in ND.
  try intros ABS;
    try rewrite <-surjective_pairing in ABS...
   apply Peirce; intros ABS.
     eapply not_disjoint in ABS as (y &ABS1 &ABS2).
     eapply disjoint_absurd with (P := False) in ND; try contradiction...
     case_eq (pair_eq y u); intros PEQ; try rewrite <-pairEq_eq in PEQ; subst;simpl; simpl in ABS2...
     specialize typeCheck_hid with (n := u) (pf := pf1) (p := q)
     as ABS3; eapply ABS3 in TC as (s &ABS4);
   try inv ABS4; try inv H3; try inv H4...
     assert (vis = hid /\ Chan un p t = s)...
     intuition; try discriminate...
     simpl in ABS1; repeat rewrite <-surjective_pairing in *.
     case_eq (nat_pair_eq_dec x u); introv ABS;
       rewrite ABS in *;
       try eapply pairEq_neq in PEQ;
       subst...
     inv ABS1...
     eapply in_remove in H3; intuition...
    simpl in NR...
    - assert (ND: NoDup (domain ((x, vis, t) :: g))).
  simpl; econstructor; try intros ABS;
  try eapply in_domain_in_g in ABS as (ff1 &tt1&ABS)...
  eapply IHTC in ND.
  try intros ABS;
    try rewrite <-surjective_pairing in ABS...
   apply Peirce; intros ABS.
     eapply not_disjoint in ABS as (y &ABS1 &ABS2).
   eapply disjoint_absurd with (P := False) in ND; try contradiction...
    case_eq (pair_eq y u); intros PEQ; try rewrite <-pairEq_eq in PEQ; subst;simpl; simpl in ABS2...
     specialize typeCheck_hid with (n := u) (pf := pf1) (p := q)
     as ABS3; eapply ABS3 in TC as (s &ABS4);
   try inv ABS4; try inv H3; try inv H4...
     assert (vis = hid /\ Chan un p t = s)...
     intuition; discriminate...
     assert (vis = hid /\ Chan un p t = s)...
     intuition; discriminate...
     assert (vis = hid /\ Chan un p t = s)...
     intuition; discriminate...
     assert (vis = hid /\ Chan un p t = s)...
     intuition; discriminate...
     eapply pairEq_neq in PEQ.
     simpl in ABS1; repeat rewrite <-surjective_pairing in *.
     case_eq (nat_pair_eq_dec x u). intros. rewrite H4 in *; subst...
     intros. rewrite H4 in *.
     try inv ABS1...
     eapply in_remove in H5; intuition. 
     simpl in NR...
Qed.  

Lemma bv_disjoint_sl : forall p g (nd_pf : NoDup (domain g)) pf,
    typeCheck g pf p ->
    disjoint (bv p) (secLabs p).
Proof with eauto.
  intros; eapply disjoint_incl,typeCheck_no_dup...
  eapply bv_disjoint_g...
Qed.


  
Lemma cons_illEProj : forall g l pf,
    cons (illEProj g l) pf.
Proof with eauto.
  intros g l; induction g; simpl;
    try destruct a as [[[a1 a2] f] t];
    try destruct f,t; try assumption.
  - simpl...
  - case_eq (In2 (a1, a2) l); intros PEQ; destruct m;
      repeat simpl; intros; try eapply IHg.
    + assert (pf' : isMap (removeEntry (a1, a2) ((a1, a2, ill, Chan lin empty t) :: illEProj g l))).
      eapply isMap_removeEntry...
      eapply Co_lin with (pf' := pf').
      eauto.
      gen pf'; unfold removeEntry; rewrite pairEq_eq_true...
    + assert (pf' : isMap (removeEntry (a1, a2) ((a1, a2, ill, Chan un p t) :: illEProj g l))).
      eapply isMap_removeEntry...
      eapply Co_un with (pf' := pf').
      eauto.
      gen pf'; unfold removeEntry; rewrite pairEq_eq_true... -  case_eq (In2 (a1, a2) l); intros PEQ;
                                                                  repeat simpl; intros; try eapply IHg.
      assert (pf' : isMap (removeEntry (a1, a2) ((a1, a2, ill, Top) :: illEProj g l))).
      eapply isMap_removeEntry...
      try eapply Co_top with (pf' := pf').
      eauto.
      gen pf'; unfold removeEntry; rewrite pairEq_eq_true...
Qed.



