Require Import
        Bool List Omega PeanoNat Program.Equality Classical
        ListAddOns
        operations pi_syntax 
        header.

(**************** Preliminaries to Proposition 2.7 *******************)

Section Preliminaries_Proposition27.

  
  Lemma split_in : forall (p:name*name) (m1 m2: map_nat_nat),
    In p (m1 ++ p :: m2).
  Proof.
    intros. apply in_app_iff with (l := m1). intuition. 
  Qed.

  Lemma split_in_remove : forall (p1 p2:name*name) (m1 m2: map_nat_nat),
      (In p1 (m1 ++ p2 :: m2) /\ p1 <> p2) -> In p1 (m1++m2).
  Proof.
    intros. apply in_app_iff with (l := m1). destruct H.
    apply in_app_iff with (l := m1) in H. destruct H. intuition. intuition.  
    apply in_inv in H. intuition. 
  Qed.

  Notation dp := domain_projection.
  Notation cp := codomain_projection.

  Lemma cp_distr : forall (l1 l2 : list (nat *nat)),
      cp (l1 ++ l2) = cp l1 ++ cp l2.
  Proof.
    intros. induction l1, l2.  unfold cp.  fold cp. auto. auto.
    assert ((a :: l1) ++ nil = a :: l1). intuition.
    rewrite H. unfold cp at 3. intuition.
    assert ((a :: l1) ++ p :: l2 = a :: l1 ++ p :: l2). intuition.
    rewrite H. destruct a. unfold cp at 1 2. fold cp.
    rewrite IHl1. intuition.
  Qed.
  
  Lemma in_dp : forall (p: name*name) (m: map_nat_nat),
      In p m -> In (fst p) (dp m).
  Proof.
    intros. induction m.
    - intuition.
    - apply in_inv in H. intuition. unfold dp. fold dp. intuition.
      rewrite H0. unfold fst.
      unfold In. assert (R := rec_In). specialize R with (A := name).
      rewrite <- R. simpl.
      assert (exists n1 n2, p = (n1, n2)). intuition.
      exists (fst p). exists (snd p). apply surjective_pairing.
      destruct H. destruct H. rewrite H. intuition.
      unfold dp. fold dp. unfold In.
      assert (R := rec_In). specialize R with (A := name).
      rewrite <- R.
      case_eq (dp m). intros. rewrite -> H1 in H. intuition.
      intros. rewrite -> H1 in H. apply in_inv in H. intuition. 
  Qed.
  
  Lemma dp_distr : forall m1 m2,
      dp (m1 ++ m2) = dp m1 ++ dp m2.
  Proof.
    intros. induction m1. intuition. unfold dp at 1. simpl. fold dp.
    rewrite IHm1. intuition.
  Qed. 
  
  Lemma map_is_structure : forall m k v v',
      (structure_is_map m /\ In (k, v) m /\ In (k, v') m) -> v = v'.
  Proof.
    intros.  destruct H as [H1 [H2 H3]]. unfold structure_is_map in H1.
    
    assert (v <> v' -> NoDup (dp m) -> False). intro.
    
    apply in_split in H2. apply in_split in H3.
    destruct H2. destruct H0. destruct H3. destruct H2.
    assert (In (k,v) m). rewrite -> H0. apply split_in with (p := (k,v)).
    assert (In (k,v') m). rewrite -> H2. apply split_in with (p := (k,v')).
    
    assert (In (k, v) (x1 ++ x2)). assert (H5 := H3). rewrite -> H2 in H5. 
    assert ( v<> v' -> (k, v) <> (k,v')). intuition. apply projections_injective in H7. intuition. 
    assert (H7 :  In (k, v) (x1 ++ (k, v') :: x2) /\ (k, v) <> (k, v')). auto. 
    apply split_in_remove with (p1 := (k, v)) (p2 := (k, v')) in H7. tauto.
    assert (dp m = dp m) by auto.
    rewrite -> H2 in H6 at 2 . rewrite dp_distr in H6. 
    unfold dp in H6 at 3. simpl in H6. intuition. fold dp in H6.
    rewrite -> H6 in H7. 
    apply in_app_iff in H5. intuition.
    apply in_dp in H8. simpl in H8.

    assert (H9:  NoDup (dp x1 ++ k :: dp x2) /\  In k (dp x1)) by auto. 
    apply no_dup_app_l in H9. intuition. 

    apply in_dp in H8. simpl in H8.
    assert (H9: NoDup (dp x1 ++ k :: dp x2) /\  In k (dp x2)) by auto. 
    apply no_dup_app_r in H9. intuition.

    apply Peirce. intuition. 
  Qed.

  Theorem beq_sym: forall n m : nat, 
      beq_nat n m = beq_nat m n.
  Proof.
    induction n as [|n' IH]; destruct m; auto.
    apply IH.
  Qed.

  Lemma beq_switch :forall x y b,
      (x =? y) = b <-> b = ( y =? x).
  Proof.
    intros. intuition. 
    case_eq (b). intuition. rewrite H0 in H.
    assert (x = y). apply beq_nat_true; auto. rewrite <- H1.
    apply beq_nat_refl.  intuition. rewrite H0 in H. rewrite <- H. apply beq_sym.
    assert ((y =? x) = b ) by auto. rewrite <- H0. apply beq_sym. 
  Qed.  

  Lemma seclabs_of_pmap: forall p x1 x2 v1 v2,
      secLabs (pmap p x1 x2 v1 v2) = secLabs p.
  Proof with eauto.
    intros; induction p.
    all:unfold pmap; fold pmap...
    unfold secLabs; fold secLabs.
    rewrite IHp1, IHp2...
     unfold secLabs; fold secLabs; rewrite IHp...
  Qed.

  Hint Resolve seclabs_of_pmap.

  Lemma identif_seclabs_of_dep_relabel :
  forall (p : dproc) (s : list (name * name)) (pf : NoDup s),
    secLabs (dep_relabel p s pf) =
    List.map (fun x => (fst x, snd x + max s)) (secLabs p).
Proof.
  intros.
  dependent induction p.
  - simpl. tauto. 
  - specialize IHp with s pf. intuition.
  - specialize IHp1 with s pf. specialize IHp2 with s pf. intuition. 
    unfold dep_relabel. fold dep_relabel. unfold secLabs. fold secLabs.
    rewrite map_app. 
    rewrite IHp1. rewrite IHp2. tauto. 
  - specialize IHp with s pf.
    unfold dep_relabel. fold dep_relabel.
    unfold secLabs. fold secLabs. rewrite map_app. rewrite seclabs_of_pmap.
    rewrite <-IHp. simpl. tauto. 
  - specialize IHp with s pf. intuition.
  - specialize IHp with s pf. intuition.
Qed.

  
 

  Notation ble_nat := Nat.leb.
  Notation blt_nat := Nat.ltb.
  
  (** The following three theorems are taken from *)
  (** https://github.com/nicolaidahl/BPlusTrees *)
  (** BPlusTrees/code/HelperProofs.v *)

  Theorem n_lt_m__Sn_lt_Sm : forall n m,
      n < m -> S n < S m.
  Proof.
    intros. induction H; omega.
  Qed.

  Theorem blt_nat_n_m_false__blt_nat_Sn_Sm : forall n m,
      blt_nat n m = false -> blt_nat (S n)  (S m) = false.
  Proof.
    intros n m H.  destruct m. unfold blt_nat. simpl. reflexivity.
    unfold blt_nat. simpl. unfold blt_nat in H. simpl in H. apply H.
  Qed.
  
  Theorem blt_nat_false : forall n m,
      blt_nat n m = false <-> ~(n < m).
  Proof. 
    split; generalize dependent m.
    unfold not. intros. unfold blt_nat in H.
    apply Nat.leb_nle in H. omega.
    induction n. 
    intros. destruct m. unfold blt_nat. simpl. reflexivity.
    unfold not in H. intuition. 
    intros. destruct m. compute. reflexivity.
    apply blt_nat_n_m_false__blt_nat_Sn_Sm.
    apply IHn.
    unfold not. unfold not in H.
    intro. apply H. 
    apply n_lt_m__Sn_lt_Sm. apply H0.
  Qed.

  
  Lemma in_preserves_max : forall (x y :nat) (l : list (nat*nat)),
      In (x, y) l -> y <= max l.
  Proof.
    intros. unfold max. induction l. intuition. apply in_inv in H. intuition.
    rewrite H0. fold max. intuition.
    case_eq (y <? max l). intuition. 
    apply Nat.ltb_lt in H. unfold lt in H. assert (y <= S y). auto with arith.
    transitivity (S y).  tauto. tauto. 
    intuition.  fold max. fold max in H.
    inversion H. 
    assert (L := Nat.ltb_nlt). 
    case_eq ( blt_nat b (max l)). intros. intuition.
    intros. 
    apply Nat.ltb_nlt in H2. apply Peirce. intuition.
    case_eq ( blt_nat b (S m)). intuition.
    intuition. 
    apply Nat.ltb_nlt in H3. apply Peirce. intuition.
  Qed.
  
  Theorem incl_preserves_max : forall (l m : list (nat * nat)),
      incl l m -> max m >= max l.
  Proof.
    intros. induction l. 
    - unfold max. fold max. intuition.     
    - assert (H5 := H). apply incl_distr with (l1 := a::nil) in H. destruct H. intuition.
      unfold max at 2.  fold max. assert (a = (fst a, snd a)).
      apply surjective_pairing. rewrite H2. 
      case_eq (snd a <? max l). intuition. intuition. unfold incl in H.
      specialize H with a. assert (In a (a::nil)). intuition. intuition.
      
      rewrite H2 in H6. apply in_preserves_max in H6. intuition. 
  Qed.

  Theorem plus_max_preserves_disjoint: forall l1 l2 m,
      ((m >= max l1) /\ (m >= max l2) /\ (disjoint_2 l1 l2)) ->
      disjoint_2
        (List.map (fun x => (fst x, snd x + m)) l1)
        (List.map (fun x => (fst x, snd x + m)) l2).
  Proof.
    intros. destruct H as [H1 [H2 H3]].
    induction l1.
    - simpl. apply dis_nil.
    - assert (incl l1 (a::l1)).
      apply incl_appr with (m := a::nil) (l := l1) (n := l1).
      intuition.
      apply incl_preserves_max in H. intuition.
      assert (m >= max l1). unfold ge in H1. unfold ge in H2.
      unfold ge in IHl1. unfold ge in H. unfold ge.
      transitivity (max (a :: l1)). tauto. tauto. intuition.
      apply disjoint_2_cons_l in H3. intuition.
      simpl. apply disjoint_2_l_cons. intuition.
      apply in_map_iff in H4. destruct H4. intuition.
      remember (fst x) as x1. remember (snd x) as x2.
      remember (fst a) as a1. remember (snd a) as a2.
      apply projections_injective in H7. intuition.
      assert (x1 = a1). intuition.
      assert (x2 + m  = a2 + m). intuition.
      assert (x2 = a2).  intuition.
      assert (a = x). apply injective_projections. intuition. intuition.
      rewrite <-H12 in H8. intuition.
  Qed.

  
End Preliminaries_Proposition27.

(*********************** Proposition 2.7 **************************)

Section Proposition27.

  (* This is the proof of item 3 of Proposition 2.7. *)
  (* Item 1 makes no sense in the coq implementation. *)
  (* Item 2 is true, but I do not need the result (up to now) *)

  
  Definition incl_ (l m:list (name*name)) :=
    forall a:name*name,
      In a l ->
      In a m /\
      count_occ nat_pair_eq_dec  l a =
      count_occ  nat_pair_eq_dec m a.

  Lemma incl2_incl :
    forall l m,
      incl_ l m -> incl l m.
  Proof.
    intros. unfold incl_ in H. unfold incl.
    intuition. specialize H with a; intuition. 
  Qed.

  
  Lemma incl_pres: forall a l s,
      incl_ (a :: l) s -> NoDup s -> incl_ l s.
  Proof.
    intros. unfold incl_. intros. split.
    unfold incl_ in H. specialize H with a0.
    specialize in_cons with (prod name name) a a0 l.
    intuition.
    unfold incl_ in H. specialize H with a0.
    specialize in_cons with (prod name name) a a0 l.
    intuition.
    specialize NoDup_count_occ' with (prod name name) nat_pair_eq_dec s.
    intuition.
    specialize H2 with a0. intuition. rewrite H6. rewrite H6 in H4.
    assert (a <> a0). intuition.
    rewrite H2 in H4.
    specialize count_occ_cons_eq with  (prod name name) nat_pair_eq_dec l a0 a0.
    intuition.
    assert ( count_occ nat_pair_eq_dec l a0 = 0); intuition.
    specialize count_occ_In with  (prod name name) nat_pair_eq_dec l a0.
    intros. rewrite H9 in H1. intuition.
    specialize count_occ_cons_neq with  (prod name name) nat_pair_eq_dec l a a0.
    intros.
    intuition.
  Qed.

   Lemma pres_incl: forall a l s,
      incl_ l s -> NoDup s ->  NoDup (a :: l) ->
      In a s -> incl_ (a :: l) s.
  Proof with eauto.
    intros. unfold incl_. intros. split.
    - unfold incl_ in H. specialize H with a0.
      inversion H3. subst...
      intuition.
    - inversion H3. subst...
      specialize NoDup_count_occ' with (prod name name) nat_pair_eq_dec (a0 :: l) as L.
      specialize NoDup_count_occ' with (prod name name) nat_pair_eq_dec s as R.
      intuition.
      specialize H8 with a0; specialize H6 with a0; intuition.
      specialize NoDup_count_occ' with (prod name name) nat_pair_eq_dec (a :: l) as L.
      intuition.
      specialize H7 with a0; intuition.
      rewrite H6.
      unfold incl_ in H. specialize H with a0.
      intuition.
      assert (~In a l /\ NoDup l). apply NoDup_cons_iff...
      intuition. rewrite NoDup_count_occ' with (decA :=  nat_pair_eq_dec) in H10.
      specialize H10 with a0... intuition.
  Qed.
  
  Lemma incl_preserves_no_dup: forall (l s : list (name*name)),
      incl_ l s -> NoDup s -> NoDup l.
  Proof.  
    intros. induction l.
    apply NoDup_nil.
    rewrite NoDup_cons_iff. split.
    assert (ND := H). unfold incl_ in H.
    specialize H with a. (assert (K := in_eq)).
    specialize K with (prod name name) a l. intuition.
    (assert (N := count_occ_cons_eq)).
    specialize N with (prod name name) nat_pair_eq_dec l a a. intuition.
    (assert (O := count_occ_In)).
    specialize O with (prod name name) nat_pair_eq_dec l a. intuition.
    assert (count_occ nat_pair_eq_dec (a :: l) a > 1). intuition.
    rewrite H3 in H5.
    assert ( L:= NoDup_count_occ).
    specialize L with (prod name name) nat_pair_eq_dec s.
    rewrite L in H0. specialize H0 with a.
    intuition.
    specialize incl_pres with a l s. intuition.
  Qed.
  
 


Hint Resolve NoDup_cons_iff pres_incl.

  Lemma incl_incl2 : forall l1 l2,
      NoDup l1 -> NoDup l2 -> incl l1 l2 ->
      incl_ l1 l2.
  Proof with eauto.
    intros.
    induction l1, l2.
    unfold incl_...
    unfold incl_. intros. inversion H2.
    eapply incl_l_nil in H1... inversion H1.
    assert (~In a l1 /\ NoDup l1)...
    eapply NoDup_cons_iff...
    assert (~In p l2 /\ NoDup l2)...
    eapply NoDup_cons_iff...
    apply incl_cons_inv in H1.
    intuition.
Qed.

  

  Definition count_cons_app :=
    count_occ_app nat_pair_eq_dec.

  
  Lemma incl2_distr : forall l1 l2 m,
      incl_ (l1++l2) m -> NoDup m -> incl_ l1 m /\ incl_ l2 m.
  Proof.
    intros. split.
    - unfold incl_.
      intros. 
      unfold incl_ in H.
      specialize H with (a := a).
      rewrite in_app_iff in H.
      intuition.
      specialize NoDup_count_occ' with (prod name name) nat_pair_eq_dec m. intros. intuition.
      specialize H with a. intuition.
      rewrite H6. rewrite H6 in H4.
      rewrite count_cons_app in H4.
      specialize count_occ_In with (prod name name) nat_pair_eq_dec l1 a. intros.
      intuition.
    - unfold incl_.
      intros. 
      unfold incl_ in H.
      specialize H with (a := a).
      rewrite in_app_iff in H.
      intuition.
      specialize NoDup_count_occ' with (prod name name) nat_pair_eq_dec m. intros. intuition.
      specialize H with a. intuition.
      rewrite H6. rewrite H6 in H4.
      rewrite count_cons_app in H4.
      specialize count_occ_In with (prod name name) nat_pair_eq_dec l2 a. intros.
      intuition.
  Qed.

  Lemma wf_pmap : forall p x1 x2 v1 v2,
     NoDup (secLabs p) -> NoDup (secLabs (pmap p x1 x2 v1 v2)).
  Proof with eauto.
    intros.  
    rewrite seclabs_of_pmap...
  Qed.
  
  Proposition  prop27 : forall (p :dproc) (s : list (name*name)) (pf : NoDup s),
      incl_ (secLabs p) s -> NoDup (secLabs (dep_relabel p s pf)). 
  Proof.
    intros. 
    induction p.
    - unfold dep_relabel. unfold wf. unfold secLabs.  apply NoDup_nil.
    - unfold dep_relabel. fold dep_relabel.
      unfold wf. unfold secLabs. fold secLabs. fold wf.
      unfold secLabs in H. fold secLabs in H. intuition.
    - unfold secLabs in H. fold secLabs in H.
      assert (H10 := H).
      apply incl2_distr in H. intuition.
      unfold dep_relabel. fold dep_relabel. unfold wf. 
      unfold secLabs. fold secLabs. 
      apply no_dup_iff.  intuition.
      apply disjoint_car.
      rewrite identif_seclabs_of_dep_relabel.
      rewrite identif_seclabs_of_dep_relabel.
      apply plus_max_preserves_disjoint.
      intuition.
      apply incl_preserves_max.  apply incl2_incl. tauto.
      apply incl_preserves_max.  apply incl2_incl. tauto.
      apply disjoint_car.
      apply incl_preserves_no_dup in H10. apply no_dup_iff in H10. intuition.
      all:try assumption.
    - unfold secLabs in H. fold secLabs in H.
      assert (H3 := H).  apply incl2_distr in H.
      intuition.
      unfold dep_relabel.  fold dep_relabel.
      assert (In (n, n0) s). unfold incl_ in H0. specialize H0 with (n, n0).
      assert (In (n, n0) ((n,n0) :: nil)). intuition.
      assert (incl (secLabs p ++ (n, n0) :: nil) s).
      apply incl2_incl. tauto. intuition.
      apply incl2_incl in H0.
      unfold wf. unfold secLabs. fold secLabs. apply no_dup_iff.
      intuition.  apply wf_pmap. tauto.
      apply NoDup_cons. intuition. apply NoDup_nil.
      erewrite seclabs_of_pmap,identif_seclabs_of_dep_relabel. 
      apply disjoint_commute. apply disjoint_car.
      apply dis_cons. intuition.
      apply in_map_iff in H4. destruct H4. destruct H4.
      remember (fst x) as x1. remember (snd x) as x2.
      apply projections_injective in H4. 
      assert (x1 = n). intuition.
      assert (x2 + max s = n0 + max s). intuition.
      assert (x2 = n0). intuition. 
      assert (x = (n, n0)). assert (S := surjective_pairing).
      specialize S with name name x. rewrite S. intuition.
      apply incl_preserves_no_dup in H3. 
      apply no_dup_iff in H3. intuition. rewrite <- H9 in H13.
      apply disjoint_r_cons in H13. intuition. tauto.
      apply dis_nil. tauto.
    - unfold dep_relabel. fold dep_relabel. unfold wf.
      assert (H10 := H). apply incl_preserves_no_dup in H.
      unfold secLabs in H10. fold secLabs in H10. intuition.
      unfold secLabs. fold secLabs.  intuition. 
    - unfold dep_relabel. fold dep_relabel. unfold wf.
      assert (H10 := H). apply incl_preserves_no_dup in H.
      unfold secLabs in H10. fold secLabs in H10. intuition.
      unfold secLabs. fold secLabs.  intuition. 
    Qed.

End Proposition27.
