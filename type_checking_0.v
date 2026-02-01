Require Import
        Bool List Omega PeanoNat Program.Equality  Classical
        ListAddOns Max RemoveEntry Domain NewEntries
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
        type_system_rules
        disjoint_newEntries.


Fixpoint nonRec_typable p :=
  match p with
  | dInp u1 u2 v1 v2 p
  | dOut u1 u2 v1 v2 p
  | dBang u1 u2 v1 v2 p =>
    (u1, u2) <> (v1, v2) /\ nonRec_typable p
  | dPar p q  =>
    nonRec_typable p /\ nonRec_typable q
  | dNu u1 u2 p =>
    nonRec_typable p
  | dZero => True
  end.

Hint Unfold nonRec_typable.

Hint Resolve nonRecTypes.

Lemma typeCheck_object_neq_subject: forall g p pf,
    typeCheck g pf p -> nonRec_typable p.
Proof with eauto.
  intros.
  dependent induction H.
  all:eauto.
   
  unfold nonRec_typable. fold nonRec_typable.
  assert ((Chan lin p t) = t' -> False); unfold not. intros ABS; subst t'.
  assert (K := nonRecTypes).
  destruct K as [NR1 NR2].
  inversion H0. inversion H4.
  eauto.
  eauto.
  eauto.
  eauto.
  split; unfold not. intros ABS.
  rewrite  <-surjective_pairing in ABS.
  rewrite  <-surjective_pairing in ABS.
  subst v.
  apply type_of_map with
      g u  (Chan lin p t) t' in pf as CONTRA...
  assumption.

  unfold nonRec_typable. fold nonRec_typable.
  assert ((Chan un p t) = t' -> False); unfold not. intros ABS; subst t'.
  assert (K := nonRecTypes).
  destruct K as [NR1 NR2].
  inversion H0. inversion H4.
  eauto.
  eauto.
  eauto.
  eauto.
  split; unfold not. intros ABS.
  rewrite  <-surjective_pairing in ABS.
  rewrite  <-surjective_pairing in ABS.
  subst v.
  apply type_of_map with
      g u  (Chan un p t) t' in pf as CONTRA...
  assumption.

  
  unfold nonRec_typable. fold nonRec_typable.
  intuition.
  rewrite  <-surjective_pairing in H4.
  rewrite  <-surjective_pairing in H4.
  subst.
  apply in_g_in_domain in H0...

  unfold nonRec_typable. fold nonRec_typable.
  split. unfold not; intros.
   rewrite  <-surjective_pairing in H4.
  rewrite  <-surjective_pairing in H4.
  subst.
  apply in_g_in_domain in H0...
  assumption.

  unfold nonRec_typable. fold nonRec_typable.
  split. unfold not; intros.
   rewrite  <-surjective_pairing in H5.
  rewrite  <-surjective_pairing in H5.
  subst.
  apply in_g_in_domain in H0...
  assumption.
Qed.

Lemma typeCheck_vis: forall n t g pf p,
    typeCheck g pf p ->
    In (n, vis, t) g ->
    ~In n (secLabs p).
Proof with eauto.
  intros.
  unfold not; intro ABS.
  generalize dependent n.
  generalize dependent t.
  dependent induction H.
  - intros. unfold secLabs in ABS...
  - intros.
    assert (n = n0 -> False). intros ABS2.
    subst n0.
    apply flag_of_map with
        g n hid vis in pf as ABS3.
    inversion ABS3; subst...
    eauto.
    eauto.

    unfold secLabs in ABS; fold secLabs in ABS.
    apply in_app_iff in ABS.
    intuition.
    + assert (n0 <> n) by auto.
      apply removeEntry_in with
          n0 vis t0 n g in H4.
      apply in_cons with
          (a := (n, vis, t))
          (b := (n0, vis, t0)) 
          (l := (removeEntry n g))
        in H4.
      specialize IHtypeCheck with t0 n0.
      intuition.
      assumption.
    + inversion H3.
      rewrite <-surjective_pairing in H4.
      intuition.
      inversion H4.
  - intros t n IN ABS.
    unfold secLabs in ABS; fold secLabs in ABS.
    apply fsuper_vis with
        g1 g2 g pf1 pf2 pf n t
      in IN as FVIS.
    inversion FVIS; inversion H2; inversion H3; subst.
    specialize IHtypeCheck1 with t0 n.
    specialize IHtypeCheck2 with t1 n.
    intuition.
    specialize not_in_and_app with
        (a := n) (l := secLabs p2) (m := secLabs p1) as NIAA; intuition.  
    eauto.
  - intros t0 n IN ABS.
    unfold secLabs in ABS; fold secLabs in ABS.
    case_eq (pair_eq n u).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    specialize IHtypeCheck with t1 u.
    intuition.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    case_eq (pair_eq n v).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    specialize IHtypeCheck with t2 v.
    intuition.
    intro PNEQ2; rewrite <-pairEq_neq in PNEQ2.
    apply removeEntry_in with
        n vis t0 u g
      in PNEQ as IN2.
    apply removeEntry_in with
        n vis t0 v (removeEntry u g)
      in PNEQ2 as IN3.
    specialize IHtypeCheck with t0 n.
    intuition.
    all:eauto.
  - intros t0 n IN ABS.
    unfold secLabs in ABS; fold secLabs in ABS.
    case_eq (pair_eq n u).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    specialize IHtypeCheck with t0 u.
    assert (INR: In (u, vis, t0) (removeEntry v g)).
    eapply removeEntry_in...
    unfold not; intros; subst.
    assert (vis = vis /\ Chan un p t = t').
    eapply in_isMap... destruct H4. subst.
    inversion H0. destruct H6.  inversion H6.
    apply nonRecTypes in H12...
    assert (In (u, vis, t0) ((v, vis, t2) :: removeEntry v g)).
    eapply in_cons...
    intuition.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    case_eq (pair_eq n v).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    specialize IHtypeCheck with t2 v.
    intuition.
    intro PNEQ2; rewrite <-pairEq_neq in PNEQ2.
    apply removeEntry_in with
        n vis t0 u g
      in PNEQ as IN2.
    apply removeEntry_in with
        n vis t0 v (removeEntry u g)
      in PNEQ2 as IN3.
    specialize IHtypeCheck with t0 n.
    assert (In (n, vis, t0) (removeEntry v g)).
    apply removeEntry_in...
    assert (In (n, vis, t0) ((v, vis, t2) :: removeEntry v g)).
    apply in_cons...
    intuition.
    all:eauto.  
  - remember x as v; subst x.
    intros t0 n IN ABS.
    unfold secLabs in ABS; fold secLabs in ABS.
    case_eq (pair_eq n u).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    specialize IHtypeCheck with t1 u.
    intuition.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    case_eq (pair_eq n v).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    specialize IHtypeCheck with t v.
    intuition.
    intro PNEQ2; rewrite <-pairEq_neq in PNEQ2.
    apply removeEntry_in with
        n vis t0 u g
      in PNEQ as IN2.
    apply removeEntry_in with
        n vis t0 v (removeEntry u g)
      in PNEQ2 as IN3.
    specialize IHtypeCheck with t0 n.
    intuition.
    all:eauto.
  - intros t0 n IN ABS.
    unfold secLabs in ABS; fold secLabs in ABS.
    case_eq (pair_eq n u).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    specialize IHtypeCheck with t0 u.
    assert (In (u, vis, t0) ((x, vis, t) :: g)).
    apply in_cons...
    intuition.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize IHtypeCheck with t0 n.
    assert (In (n, vis, t0) ((x, vis, t) :: g)).
    apply in_cons...
    intuition.
  - intros t0 n IN ABS.
    unfold secLabs in ABS; fold secLabs in ABS.
    case_eq (pair_eq n u).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    specialize IHtypeCheck with t0 u.
    assert (In (u, vis, t0) ((x, vis, t) :: g)).
    apply in_cons...
    intuition.
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    specialize IHtypeCheck with t0 n.
    assert (In (n, vis, t0) ((x, vis, t) :: g)).
    apply in_cons...
    intuition.
Qed.

Lemma typeCheck_hid: forall n g pf p,
    typeCheck g pf p ->
    In n (secLabs p) ->
    exists t,
      In (n, hid, t) g.
Proof with eauto.
  intros.
  generalize dependent n.
  dependent induction H.
  - intros. unfold secLabs in H0; inversion H0...
  - intros.
    case_eq (pair_eq n n0).
    intro PEQ; rewrite <-pairEq_eq in PEQ; subst n.
    exists t...
    intro PNEQ; rewrite <-pairEq_neq in PNEQ.
    unfold secLabs in H1; fold secLabs in H1.
    apply in_app_iff in H1.
    intuition.
    specialize IHtypeCheck with n0; intuition.
    destruct H1 as [t0 IN].
    apply in_inv in IN.
    intuition.
    inversion H1...
    apply in_removeEntry in H1.
    exists t0...
    apply in_inv in H2.
    intuition.
    rewrite <-surjective_pairing in H1.
    intuition.
  - intros. 
    unfold secLabs in H2; fold secLabs in H2.
    apply in_app_iff in H2.
    intuition.
    specialize IHtypeCheck2 with n.
    intuition.
    destruct H2 as [t IN].
    destruct n.
    apply fsub_hid_r with
        g1 g2 g pf1 pf2 pf n n0 t
      in IN.
    inversion IN; subst.
    exists t0...
    all:eauto.
    
    specialize IHtypeCheck1 with n.
    intuition.
    destruct H2 as [t IN].
    destruct n.
    apply fsub_hid with
        g1 g2 g pf1 pf2 pf n n0 t
      in IN.
    inversion IN; subst.
    exists t0...
    all:eauto.
  - intros.
    unfold secLabs in H4; fold secLabs in H4.
    specialize IHtypeCheck with n.
    intuition.
    destruct H5 as [t3 IN].
    apply in_app_iff with (l := (u, vis, t1) :: nil)  in IN.
    intuition.
    inversion H5; inversion H6...
    apply in_app_iff with (l := (v, vis, t2) :: nil)  in H5.
    intuition.
    inversion H6. inversion H5...
    inversion H5.
    apply in_removeEntry in H6.
    eauto.
  - intros.
    unfold secLabs in H4; fold secLabs in H4.
    specialize IHtypeCheck with n.
    apply IHtypeCheck in H4.
    destruct H4 as [t3 IN].
    apply in_app_iff with (l := (v, vis, t2) :: nil)  in IN.
    inversion IN. inversion H4. inversion H5. inversion H5.
    exists t3. eauto.
  - intros.
    assert (K4 := H3).
    unfold secLabs in K4; fold secLabs in K4.
    specialize IHtypeCheck with n.
    intuition.
    destruct H5 as [t3 IN].
    apply in_app_iff with (l := (u, vis, t1) :: nil)  in IN.
    intuition.
    inversion H5; inversion H6...
    apply in_app_iff with (l := (x, vis, t) :: nil)  in H5.
    intuition.
    inversion H6. inversion H5...
    inversion H5.
    apply in_removeEntry in H6.
    eauto.
  - intros.
    assert (K4 := H3).
    unfold secLabs in H4; fold secLabs in H4.
    specialize IHtypeCheck with n.
    apply IHtypeCheck in H4.
    destruct H4 as [t0 IN]; exists t0.
    inversion IN. inversion H4...
    assumption.
    - intros.
    unfold secLabs in H4; fold secLabs in H4.
    specialize IHtypeCheck with n.
    apply IHtypeCheck in H5.
    destruct H5 as [t0 IN]; exists t0.
    inversion IN. inversion H5...
    assumption.
Qed.



Lemma super_in_sub: forall g1 g2 g pf1 pf2 pf n f t,
    tEnv_split g1 g2 g pf1 pf2 pf ->
    In (n, f, t) g ->
    exists f1 t1 f2 t2,
      In (n, f1, t1) g1 /\ In (n, f2, t2) g2.
Proof with eauto.
  intros.
   assert (In n (domain g)).
    apply in_g_in_domain with (f := f) (t := t)...
    assert ( In n (domain g1) <-> In n (domain g)).
    apply split_domain_l with (pf1 := pf1) (pf2 := pf2) (pf := pf) ...
    assert ( In n (domain g2) <-> In n (domain g)).
    apply split_domain_r with (pf1 := pf1) (pf2 := pf2) (pf := pf) ...
    assert (In n (domain g1)); intuition.
    assert (In n (domain g2)); intuition.
    apply in_domain_in_g in H6; apply in_domain_in_g in H3.
    destruct H6 as [f2 [t2 IN2]].
    destruct H3 as [f1 [t1 IN1]].
    exists f1, t1, f2, t2.
    intuition.
Qed.

