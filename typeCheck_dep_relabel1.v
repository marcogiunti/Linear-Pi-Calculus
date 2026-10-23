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
        split_cons_remove
        sne_premises.


Require Import Classical.

Require Import CpdtTactics LibTactics.


Import ListNotations.



Lemma typeCheck_weak2 g pf p k pfk pf1 (nd_pf : NoDup (domain k ++ domain g)):
  typeCheck g pf p ->
  cons k pfk ->
  disjoint (bv p) (domain k) -> 
  typeCheck (k ++ g) pf1 p.
Proof with eauto.
  introv TC CONS DIS.

  assert (nd_pf1 : NoDup (domain g ++ domain k)).
  rewrite no_dup_iff in *; intuition.
  try eapply disjoint_commute...

  assert (ND1 := nd_pf1).
  rewrite <-domain_distr in nd_pf1.
  eapply no_dup_isMap in nd_pf1 as pf'.

  assert (TC2 : typeCheck (g ++ k) pf' p).
  eapply typeCheck_weak2;
    try erewrite <-domain_distr...

  eapply typeCheck_impl with (pf1 := pf');
    try erewrite domain_distr;
    try eassumption.

  introv; split; introv IN; eapply in_app_iff in IN as [IN1 | IN2];
    try eapply in_app_iff...
Qed.



Lemma in_bv_lt_max x1 x2 g p pf (nd_pf :NoDup (domain g)):
  typeCheck g pf p ->
  In (x1, x2) (bv p) ->
  x2 < max (domain g).
Proof with eauto.
  introv TC IN; dependent induction TC; simpl in IN;
    try eapply IHTC in IN; 
    try contradiction;
    try eassumption;
    try eapply no_dup_cons_removeEntry;
    try eassumption.
  4:{ Case TOutL.
    assert (NR: nonRec_typable (dOut (fst u) (snd u) (fst v) (snd v) q)).
    eapply typeCheck_object_neq_subject...
    destruct NR as [NR1 NR2].
    erewrite removeEntry_swap.
    eapply no_dup_cons_removeEntry_app;
      repeat erewrite <-surjective_pairing in NR1...
     repeat erewrite <-surjective_pairing in NR1...
  }
  - 
    try erewrite max_same_domain with (m := domain g);
      try eassumption;
      try destruct n;
      try eapply in_removeEntry_cons_iff;
      try eapply in_g_in_domain;
       try eassumption.
  - eapply in_app_iff in IN as [IN1 | IN2].
    eapply IHTC1 in IN1; clear IHTC1 IHTC2.
    erewrite <-split_max with (pf1 := pf1)...
    try eapply no_dup_split_no_dup_l...
      eapply IHTC2 in IN2; clear IHTC1 IHTC2.
      erewrite <-split_max with (pf1 := pf2);
        try eassumption.
      eapply split_comm...
    try eapply no_dup_split_no_dup_r...

  - Case TOutL.
    assert (NR: nonRec_typable (dOut (fst u) (snd u) (fst v) (snd v) q)).
    eapply typeCheck_object_neq_subject...
    destruct NR as [NR1 NR2].

    try erewrite max_same_domain with (m := domain g);
      try eassumption;
      try destruct u,v;
      simpl in NR1;
       rewrite removeEntry_swap;
       intros;
       try erewrite <-in_removeEntry_cons_iff_2;
       try tauto;
      try eapply in_g_in_domain;
      try eassumption...

     - Case TOutUn.
    assert (NR: nonRec_typable (dOut (fst u) (snd u) (fst v) (snd v) q)).
    eapply typeCheck_object_neq_subject...
    destruct NR as [NR1 NR2].
    

    try erewrite max_same_domain with (m := domain g);
      try eassumption;
      try destruct v;
      simpl in NR1;
       intros;
       try erewrite <-in_removeEntry_cons_iff;
       try tauto;
      try eapply in_g_in_domain;
      try eassumption.

     - Case TInL.
    assert (NR: nonRec_typable (dInp (fst u) (snd u) (fst x) (snd x) q)).
    eapply typeCheck_object_neq_subject...
    destruct NR as [NR1 NR2].

    inv IN as [EQ |CONT]; try inv EQ...
    
    eapply IHTC in CONT.
    try erewrite max_same_domain
      with (l := domain ((x, vis, t) :: (u, vis, t1) :: removeEntry u g)) in CONT.
      try erewrite <-rewrite_max_var in CONT.

    try erewrite max_same_domain with (m := domain g);
      try eassumption;
      try destruct u,x;
      simpl in NR1;
       intros;
       try erewrite <-in_removeEntry_cons_iff;
       try tauto;
      try eapply in_g_in_domain;
      try eassumption.

      try erewrite <-max_same_domain with (m := domain g);
      try eassumption;
      try destruct u,x;
      simpl in NR1;
       intros;
       try erewrite <-in_removeEntry_cons_iff;
       try tauto;
      try eapply in_g_in_domain;
        try eassumption.

      try eapply cons_cons_iff.


      eapply no_dup_cons_removeEntry_app_1;
        repeat rewrite <-surjective_pairing in *...

     -  Case TInUn.
    assert (NR: nonRec_typable (dInp (fst u) (snd u) (fst x) (snd x) q)).
    eapply typeCheck_object_neq_subject...
    destruct NR as [NR1 NR2].

    inv IN as [EQ |CONT]; try inv EQ...
    
    eapply IHTC in CONT.
    try erewrite max_same_domain
      with (l := domain ((x, vis, t) :: (u, vis, t1) :: removeEntry u g)) in CONT.
      try erewrite <-rewrite_max_var in CONT.

    try erewrite max_same_domain with (m := domain g);
      try eassumption;
      try destruct u,x;
      simpl in NR1;
       intros;
       try erewrite <-in_removeEntry_cons_iff;
       try tauto;
      try eapply in_g_in_domain;
      try eassumption.

      try erewrite <-max_same_domain with (m := domain g);
      try eassumption;
      try destruct u,x;
      simpl in NR1;
       intros;
       try erewrite <-in_removeEntry_cons_iff;
       try tauto;
      try eapply in_g_in_domain;
        try eassumption.

      simpl; econstructor...

-  Case TInU.
    assert (NR: nonRec_typable (dBang (fst u) (snd u) (fst x) (snd x) q)).
    eapply typeCheck_object_neq_subject...
    destruct NR as [NR1 NR2].

    inv IN as [EQ |CONT]; try inv EQ...
    
    eapply IHTC in CONT.
    try erewrite max_same_domain
      with (l := domain ((x, vis, t) :: (u, vis, t1) :: removeEntry u g)) in CONT.
      try erewrite <-rewrite_max_var in CONT.

    try erewrite max_same_domain with (m := domain g);
      try eassumption;
      try destruct u,x;
      simpl in NR1;
       intros;
       try erewrite <-in_removeEntry_cons_iff;
       try tauto;
      try eapply in_g_in_domain;
      try eassumption.

      try erewrite <-max_same_domain with (m := domain g);
      try eassumption;
      try destruct u,x;
      simpl in NR1;
       intros;
       try erewrite <-in_removeEntry_cons_iff;
       try tauto;
      try eapply in_g_in_domain;
        try eassumption.

      simpl; econstructor...

      Unshelve.
      all:eauto.
Qed.
      
Lemma typeCheck_dep_relabel1: forall p g pf nd_pf l pf1,
    incl (secLabs p) l ->
    disjoint (fn p) l ->
    disjoint (bv p) l ->
    pos l ->
    typeCheck g pf p ->
    typeCheck
      (map (fun x =>
              match x with
                (a1, a2, f, t) =>
                if In2 (a1, a2) l
                then
                  (a1, a2 + max (domain g), f, t)
                else
                  cast x
              end) g)
      pf1
      (dep_relabel p (domain g) nd_pf).
Proof with eauto.
  intros p g pf nd_pf l pf1 IN DIS DIS2 POS TC.
  generalize dependent l.
  dependent induction TC.
  -  intros; simpl; econstructor...
  -  Case TNew.
     assert (TN : typeCheck g pf (dNu (fst n) (snd n) p))...
     destruct n as [n n0]; unfold fst, snd in *.
     
     intros. unfold dep_relabel; fold dep_relabel.
 
     assert (INL: In (n, n0) l).
     unfold incl in IN; simpl in IN;
       specialize IN with (n, n0); eapply IN, in_app_iff; right...
     assert (ISIN: In2 (n, n0) l = true).
     eapply in2_In_iff...
       assert (LE: n0 <= max (domain g)).
       subst; eapply min_max...
        assert (MAX: max (domain g) > 0).
     eapply max_pos...
       assert (NIN:  ~In (n, n0) (domain (map (fun x : name * name * flag * piType =>
              let (y, t) := x in
              let (y0, f) := y in
              let (a1, a2) := y0 in
              if In2 (a1, a2) l then (a1, a2 + max (domain g), f, t) else cast x) g))).
       intros ABS; eapply in_domain_in_g in ABS as (ff &tt &ABS); erewrite in_map_iff in ABS; destruct ABS as ([[[x1 x2] ff1] tt1] &ABS  &IN2); case_eq (In2 (x1, x2) l); intros EQ2; rewrite EQ2 in *;inversion ABS.
         assert (x2 = 0); try lia;
           unfold pos in POS; specialize POS with x1 x2;
             assert (x2 >0); try eapply POS; eauto;
               try lia. 
         subst x1 x2. erewrite in2_nIn_iff in *. contradiction.
         assert (INM :
               In (n, n0 + max (domain g)) (domain (map (fun x : name * name * flag * piType =>
              let (y, t) := x in
              let (y0, f) := y in
              let (a1, a2) := y0 in
              if In2 (a1, a2) l then (a1, a2 + max (domain g), f, t) else cast x) g))).
         eapply in_g_in_domain,in_map_iff.
          exists (n, n0, hid, t); split;  try rewrite ISIN...
    
     assert (LE2 : n0 < n0 + max (domain g)). lia. 
     assert (DIFF:  (n, n0) <> (n, n0 + max (domain g))).
     intros ABS; inversion ABS; lia.
     assert (PNEQ: pair_eq (n, n0 + max (domain g)) (n, n0 ) = false).
     eapply pairEq_neq...
     assert (PEQ: pair_eq (n, n0) (n, n0) = true).
     eapply pairEq_eq...
      assert (PEQ2: pair_eq (n, n0 + max (domain g)) (n, n0+ max (domain g)) = true).
      eapply pairEq_eq...
      assert (NDPF2 : NoDup (domain ((n, n0, vis, t) :: removeEntry (n, n0 + max (domain g)) (map (fun x : name * name * flag * piType =>
              let (y, t) := x in
              let (y0, f) := y in
              let (a1, a2) := y0 in
              if In2 (a1, a2) l then (a1, a2 + max (domain g), f, t) else cast x) g)))).
        simpl;
           eapply NoDup_cons; try intros ABS;
             try eapply no_dup_shift;
             try eapply in_domain_in_g in ABS as (ff & tt &ABS); try eapply in_removeEntry, in_g_in_domain in ABS;
               try contradiction;
               eapply no_dup_removeEntry_no_dup,
               no_dup_shift...
        eapply no_dup_isMap in NDPF2 as PF2.
     
     assert (nd_pf'':
               NoDup (domain (
                          ((n, n0 + max (domain g), vis, t)
                             :: (removeEntry
                                   ((n, n0 + max (domain g))) (map
                                                                        (fun x : name * name * flag * piType =>
                                                                           let (y, t0) := x in
                                                                           let (y0, f) := y in
                                                                           let (a1, a2) := y0 in
                                                                           if In2 (a1, a2) l then (a1, a2 + max (domain g), f, t0) else cast x) g)))))).
     apply no_dup_cons_removeEntry. 
     apply no_dup_shift...
     apply no_dup_isMap in nd_pf'' as pf''.
     eapply TNew with (n := (n, n0 + max (domain g)))(t := t) (pf1 := pf'').
     + simpl in *.
       specialize in_map with (x := (n, n0, hid, t)) (l := g) (f := (fun x : name * name * flag * piType =>
                                                                        let (y, t0) := x in
                                                                        let (y0, f) := y in
                                                                        let (a0, a3) := y0 in if In2 (a0, a3) l then (a0, a3 + max (domain g), f, t0) else cast x)) as INMAP.
       intuition.
       rewrite ISIN in H0...
     + remember  (fun x : name * name * flag * piType =>
                      let (y, t0) := x in
                      let (y0, f) := y in
                      let (a1, a2) := y0 in
                      if In2 (a1, a2) l
                      then (a1, a2 + max (domain ((n, n0, vis, t) :: removeEntry (n, n0) g)), f, t0)
                      else cast x)  as f.
         rewrite max_removeEntry_cons
           with (a1 := n) (a2 := n0) (f1 := vis) (t1 := t)
           in Heqf.
         rewrite max_same_domain with (l := domain g) in Heqf.
         revert dependent pf''.         
         rewrite <-Heqf.
         intros.
         revert dependent pf1. 
         (*rewrite <- Heqf.*)
         intros.
         assert (f (n, n0, vis, t) = (n, n0 + max (domain g ), vis, t)).
         rewrite Heqf, ISIN...
         specialize IHTC with (l := List.remove nat_pair_eq_dec  (n, n0) l).
         rewrite map_cons in IHTC.
         assert (EQM :
                   ((if In2 (n, n0) (List.remove nat_pair_eq_dec (n, n0) l)
                     then
                       (n, n0 + max (domain ((n, n0, vis, t) :: removeEntry (n, n0) g)), vis,
                        t)
                     else cast (n, n0, vis, t))) = cast (n, n0, vis, t)).
         assert (~In (n, n0) (List.remove nat_pair_eq_dec (n, n0) l)). apply remove_In...
         assert (In2 (n, n0) (List.remove nat_pair_eq_dec (n, n0) l) = false).
         rewrite <-in2_In_iff in H1. 
         case_eq (In2 (n, n0) (List.remove nat_pair_eq_dec (n, n0) l)); intros. intuition. tauto.
         rewrite H2...
         move IHTC at bottom.
         rewrite EQM in IHTC.
         remember (fun x : name * name * flag * piType =>
                     let (y, t0) := x in
                     let (y0, f) := y in
                     let (a1, a2) := y0 in
                     if In2 (a1, a2) (List.remove nat_pair_eq_dec (n, n0) l)
                     then
                       (a1, a2 + max (domain ((n, n0, vis, t) :: removeEntry (n, n0) g)),
                        f, t0)
                     else cast x) as k.
         assert (nd_pf' :
                   NoDup (domain ((n, n0 , vis, t) :: removeEntry (n, n0) g))).
         eapply no_dup_cons_removeEntry...
         unfold domain in nd_pf'; fold domain in nd_pf'.
         assert (nd_pf''' : NoDup
                              (domain
                                 ((n, n0 , vis, t) :: map k (removeEntry (n, n0) g)))).
         assert (map k (removeEntry (n, n0) g) =
                 removeEntry (n, n0) (map k g)).
         subst k; eapply shift_removeEntry...
         erewrite <-max_removeEntry_cons.
         eapply in_preserves_max with (x := n), in_g_in_domain...
         eauto.
         eapply in_g_in_domain...
         rewrite H1.
         eapply no_dup_cons_removeEntry.
         subst k; eapply no_dup_shift...
         erewrite <-max_removeEntry_cons...
         apply no_dup_isMap in nd_pf''' as pf'.
         subst k; 
           specialize IHTC with (pf1 := pf') (nd_pf := nd_pf').
         assert (H1 : pos (List.remove nat_pair_eq_dec (n, n0) l))...
         apply IHTC in H1.
         simpl.
         assert (EQD :
                   (dep_relabel p (domain ((n, n0, vis, t) :: removeEntry (n, n0) g)) nd_pf' =
                    (dep_relabel p (domain g) nd_pf))).
         eapply max_dep_relabel, max_same_domain.
         assert (forall x, In x (domain g) <-> In x (domain ((n, n0, vis, t) :: removeEntry (n, n0) g))).
         eapply in_removeEntry_cons_iff...
         eapply in_iff_swap...
         rewrite EQD in H1. clear H0 EQM EQD.
         remember (dep_relabel p (domain g) nd_pf) as q.
         remember (max (domain g)) as M.

         remember (fun x : name * name * flag * piType =>
                     let (y, t0) := x in
                     let (y0, f) := y in
                     let (a1, a2) := y0 in
                     if In2 (a1, a2) (List.remove nat_pair_eq_dec (n, n0) l)
                     then
                       (a1, a2 + max (domain ((n, n0, vis, t) :: removeEntry (n, n0) g)),
                        f, t0)
                     else cast x) as k.
         assert (EQK: map k (removeEntry (n, n0) g) =
                      map f (removeEntry (n, n0) g)).
         (* since g is no dup *)
         erewrite Heqk, <-max_removeEntry_cons,<-HeqM,Heqf.
         symmetry. eapply eq_map_no_dup... eauto. eauto.
         revert dependent pf'.
         rewrite EQK. intros.
         assert (EQR: removeEntry (n, n0 + M) (map f g)  =
                      (map f (removeEntry (n, n0) g))).
         (* since (n, n0) in l *)
         symmetry. eapply shift_removeEntry_3 with (l := l)...
          (* forall x1 x2 : name, In (x1, x2) (domain g) -> x2 <= max (domain g))*)
         subst; eapply min_max...

         (*typeCheck ((n, n0 + M, vis, t) :: removeEntry (n, n0 + M) (map f g)) pf''
    (pmap q n n0 n (n0 + M)) *)
         revert dependent pf'. rewrite <-EQR; intros.
         (**** SUBSTITUTION!!!!!!! ****)
         unfold cast, castF,flag_eq in H1; simpl in H1.
         (*typeCheck ((n, n0 + M, vis, t) :: removeEntry (n, n0 + M) (map f g)) pf''
    (pmap q n n0 n (n0 + M))*)
            assert (EQRM: removeEntry (n, n0) ((n, n0, vis, t) :: removeEntry (n, n0 + M) (map f g)) =
                       removeEntry (n, n0 + M) (map f g)).
            simpl; try rewrite pairEq_eq_true...
             
         revert dependent nd_pf''. revert dependent pf''.
         simpl.
         rewrite <-EQRM, removeEntry_shift with (a2 := (n0 + M)),removeEntry_swap.
         intros. assert (IH := H1).
         remember (match t with | Chan lin p t => Chan lin empty t | _ => t end ) as N.
         assert (PF3:  isMap ([(n, n0 + M, vis, N)] ++ (n, n0, vis, t) :: removeEntry (n, n0 + M) (map f g))).
         erewrite app_cons,removeEntry_shift;
           try eapply no_dup_isMap, no_dup_cons_removeEntry; simpl; try eapply
           NoDup_cons; try intros ABS;
             subst f M; try contradiction;try eapply no_dup_shift...
        assert (DIFFM :  (n, n0 + M) <> (n, n0)).
          intros ABS; inversion ABS. assert (M = 0). lia.
         subst.
         assert (n0 = 0). lia. 
         unfold pos in POS; move POS at bottom; specialize POS with n n0; intuition.
         assert (nd_pfIH:
                   NoDup (domain ([(n, n0 + M, vis, N)] ++ (n, n0, vis, t) :: removeEntry (n, n0 + M) (map f g)))).
         erewrite removeEntry_shift, app_cons.
         eapply no_dup_cons_removeEntry;
           simpl; econstructor; subst f; move NIN at bottom.
         assumption.
         eapply no_dup_shift...
         subst... assumption.
         eapply no_dup_isMap in nd_pfIH as pfIH.
         assert (pfk : isMap [(n, n0 + M, vis, N)]).
         econstructor; intuition; try inversion H2; try inversion H3;
           try inversion H0; try inversion H4; subst...
         eapply typeCheck_weak2
           with (pfk := pfk) (pf1 := pfIH) in IH.
         
         

         assert (nd_pfIH2 :
                   NoDup (domain ( ((n, n0 + M, vis, t)
           :: removeEntry (n, n0 + M)
           (removeEntry (n, n0) ([(n, n0 + M, vis, N)] ++ (n, n0, vis, t) :: removeEntry (n, n0 + M) (map f g))))))).
         erewrite  app_cons; eapply no_dup_cons_removeEntry.
           erewrite <-removeEntry_shift;
           unfold removeEntry; fold removeEntry;
             try rewrite pairEq_eq_true;
             subst f;
             try eapply no_dup_cons_removeEntry, no_dup_shift...
           subst...
         eapply no_dup_isMap in nd_pfIH2 as pfIH2.
         assert (IH2: In (n, n0 + M, vis, N) ([(n, n0 + M, vis, N)] ++ (n, n0, vis, t) :: removeEntry (n, n0 + M) (map f g))).
         eapply in_app_iff; left...

         eapply  typeCheck_substitution with (b1 := n) (b2 := n0 + M) (x1 := n) (x2 := n0) (p := q) (s := t) (s2 := t)
                 (pf := pfIH) (pf1 :=pfIH2) in IH2.
         assert (EQ:
                   removeEntry (n, n0 + M)
                               (removeEntry (n, n0)
                   ([(n, n0 + M, vis, N)] ++
                                          (n, n0, vis, t) :: removeEntry (n, n0 + M) (map f g))) =
                   removeEntry (n, n0 + M)(removeEntry (n, n0) ((n, n0, vis, t) :: map f g))).
         rewrite app_cons; 
           unfold removeEntry; fold removeEntry;
         rewrite PNEQ, PEQ;
         unfold removeEntry; fold removeEntry;
           rewrite PEQ2...
         revert dependent nd_pf''. revert dependent pf''.
         rewrite <-EQ. intros...
         
         
         (*  NoDup
    (domain ([(n, n0 + M, vis, N)] ++ (n, n0, vis, t) :: removeEntry (n, n0 + M) (map f g))) *)
         erewrite removeEntry_shift,app_cons.
         eapply no_dup_cons_removeEntry;simpl;
           eapply NoDup_cons; try intros ABS;
             subst f M; try eapply no_dup_shift...
         eauto.
         
         (* In (n, n0 + M, ?f, ?s1) ((n, n0, vis, t) :: map f g) *)
         right; eapply in_app_iff;right...
         eauto.

         erewrite app_cons,removeEntry_shift,<-max_removeEntry_cons.
         eauto.
         simpl; eapply NoDup_cons;
             subst f M; try eapply no_dup_shift...
         
         subst f;simpl...  
         eauto.
         discriminate.
         subst N; destruct t; try destruct m... 
         rewrite <-pol_cup_id at 3; try econstructor...
         eauto.
         (* NoDup
    (domain [(n, n0 + M, vis, N)] ++
     domain ((n, n0, vis, t) :: removeEntry (n, n0 + M) (map f g)))*)
         erewrite <-domain_distr,app_cons,removeEntry_shift.
         eapply no_dup_cons_removeEntry; simpl; eapply NoDup_cons;try intros ABS;
             subst f M; try eapply no_dup_shift...
         eauto.
         (* cons [(n, n0 + M, vis, N)] ?pfk  *)
         subst N; destruct t; try destruct m.
         eapply Co_lin...
         eapply Co_un...
         eapply Co_top...
         

         subst q; rewrite bv_dep_relabel.
         apply Peirce; introv ABS;
           eapply not_disjoint in ABS as (x &ABS1 &ABS2).
         unfold domain in ABS2; try inv ABS2; try contradiction.
         eapply in_bv_lt_max with (pf := pf1) in ABS1; try eassumption.
         assert (EQ:
                  max (domain ((n, n0, vis, t) :: removeEntry (n, n0) g)) = max (domain g)).
         erewrite <-max_same_domain...
         rewrite EQ in ABS1. lia.
         
         
         
         eauto.
         eauto.
         
         unfold secLabs in IN; fold secLabs in IN; simpl in IN...
         move IN at bottom.
         unfold incl. unfold incl in IN; intros. specialize IN with a. assert (In a (secLabs p ++ (n, n0) :: nil)). eapply in_app_iff...
         intuition auto.
         eapply in_in_remove...
         simpl in TN; move TN at bottom.
         assert (ND: incl (secLabs (dNu n n0 p)) (domain g) /\ NoDup (secLabs (dNu n n0 p))).
         eapply typeCheck_no_dup...
         destruct ND as [_ ND]; unfold secLabs in ND; fold secLabs in ND. eapply no_dup_disjoint in ND; rewrite <-disjoint_car, disjoint_2_comm in ND; inversion ND; subst; destruct H8 as [NIN2 _]; intro; subst; intuition.

         move DIS at bottom; unfold fn in DIS; fold fn in DIS; simpl in DIS.
         eapply disjoint_remove_swap...

         unfold bv in DIS2; fold bv in DIS2; simpl in DIS2.
         eapply disjoint_remove_inv...
         
         unfold removeEntry; fold removeEntry.
         rewrite PEQ.
         assert (forall x : name * name,
                    In x (domain g) <-> In x (domain ((n, n0, vis, t) :: removeEntry (n, n0) g))).
         eapply in_removeEntry_cons_iff...
         (*forall x : name * name,
  In x (domain ((n, n0, vis, t) :: removeEntry (n, n0) g)) <-> In x (domain g)*)
         eauto.
         eapply no_dup_cons_removeEntry...
         simpl...
         Unshelve.
         all:eauto.  
  - Case TPar. intros. 
    assert (nd_pf2 : NoDup (domain ( (map
       (fun x : name * name * flag * piType =>
        let (y, t) := x in
        let (y0, f) := y in
        let (a1, a2) := y0 in
        if In2 (a1, a2) l then (a1, a2 + max (domain g2), f, t) else cast x) g2)))).
    eapply no_dup_shift; try eapply no_dup_split_no_dup_r...
    eapply no_dup_isMap in nd_pf2 as pf''.
     assert (nd_pf1 : NoDup (domain ( (map
       (fun x : name * name * flag * piType =>
        let (y, t) := x in
        let (y0, f) := y in
        let (a1, a2) := y0 in
        if In2 (a1, a2) l then (a1, a2 + max (domain g1), f, t) else cast x) g1)))).
     eapply no_dup_shift; try eapply no_dup_split_no_dup_l with (g := g)...
     eapply no_dup_isMap in nd_pf1 as pf'.
    unfold secLabs,fn, bv in *; fold secLabs in *; fold fn in *; fold bv in *;
    simpl; eapply incl_distr in IN as [IH2 IH1];
    eapply IHTC1 in IH1;
    eapply IHTC2 in IH2.
    try eapply TPar with (pf1 := pf') (pf2 := pf''); try erewrite split_dep_relabel; try eapply split_comm; try eassumption.
    revert dependent pf''. revert dependent pf'.
     erewrite split_max with (pf1 := pf2) (pf := pf),
                             split_max  with (pf1 := pf1) (pf := pf). intros.
     eapply split_map.
     eauto.
     eauto.
     eapply split_comm...
     lia.
     eauto.
     eapply split_comm...
     eapply split_comm...
     all:eauto.
     
  - Case TOutL.
    assert (TOL :  typeCheck
                     g pf (dOut (fst u) (snd u) (fst v) (snd v) q))...
    intros.
    assert (DIFFUV: u <> v).
    destruct u,v; eapply  typeCheck_object_neq_subject in TOL;
      simpl in TOL; intuition.
    remember  (fun x : name * name * flag * piType =>
                 let (y, t0) := x in
                 let (y0, f) := y in
                 let (a1, a2) := y0 in
                 if In2 (a1, a2) l
                 then (a1, a2 + max (domain g), f, t0)
                 else cast x)  as f.

    unfold dep_relabel; fold dep_relabel.
    simpl in DIS; unfold fn in DIS; fold fn in DIS; destruct DIS as [FNU [FNV DIS]].

    assert (FU: forall t1, f (u, vis, t1) = (u, vis, t1)).
    intros;
      subst f; destruct u;
        case_eq (In2 (n, n0) l); intros IN2.
    simpl in FNU; rewrite in2_In_iff in IN2;  intuition auto.
    unfold cast,castF at 1.
    unfold flag_eq at 1; fold flag_eq; simpl...
    assert (FV: forall t2, f (v, vis, t2) = (v, vis, t2)).
    intros; subst f; destruct v;
      case_eq (In2 (n, n0) l); intros IN2.
    simpl in FNU; rewrite in2_In_iff in IN2;  intuition auto.
    unfold cast,castF at 1.
    unfold flag_eq at 1; fold flag_eq; simpl...
    assert (nd_pf15 : NoDup (domain (((u, vis, t1) :: (v, vis, t2) :: removeEntry v (removeEntry u (map f g)))))).
    rewrite removeEntry_swap;
      subst f; try eapply no_dup_cons_removeEntry_app;
               try eapply no_dup_shift...
    eapply no_dup_isMap in nd_pf15 as pf15.
    eapply TOutL with (pf1 := pf15).
    eauto. eauto.
    
    assert (INM : In (f (u, vis, Chan lin p t)) (map f g)).
    eapply in_map... erewrite FU in INM... 
    assert (INM : In (f (v, vis, t')) (map f g)).
    eapply in_map... erewrite FV in INM...

    assert (u <> v).
    eapply typeCheck_object_neq_subject in TOL; move TOL at bottom. unfold nonRec_typable in TOL; fold nonRec_typable in TOL; destruct TOL as [ABS _]; rewrite <-surjective_pairing in ABS; rewrite <-surjective_pairing in ABS; intuition auto...

    assert (nd_pf'' :
              NoDup (domain (((u, vis, t1) :: (v, vis, t2) :: removeEntry v (removeEntry u g))))).
    erewrite removeEntry_swap. eapply no_dup_cons_removeEntry_app...
    intuition auto.
    assert (IH: incl (secLabs q) l ).
    simpl in IN; intuition.
    assert (nd_pf2 : NoDup (domain (
                    (map
                       (fun x : name * name * flag * piType =>
                          let (y, t) := x in
                          let (y0, f) := y in
                          let (a1, a2) := y0 in
                          if In2 (a1, a2) l
                          then
                            (a1,
                             a2 +
                             max
                               (domain
                                  ((u, vis, t1)
                                     :: (v, vis, t2) :: removeEntry v (removeEntry u g))), f, t)
                          else cast x)
                       ((u, vis, t1) :: (v, vis, t2) :: removeEntry v (removeEntry u g)))))).
    eapply no_dup_shift...
    eapply no_dup_isMap in nd_pf2 as pf2.
    eapply IHTC with (pf1 := pf2) (nd_pf := nd_pf'') in IH.
    revert dependent pf15.
    erewrite <-FU,<-FV. intros.
    
    assert (MAX: max (domain g) = max (domain ((u, vis, t1) :: (v, vis, t2) :: removeEntry v (removeEntry u g)))).
    destruct u, v; erewrite removeEntry_swap, max_removeEntry_cons_app...

    move IH at bottom.
    destruct u, v. 
    revert dependent pf2;
      rewrite <-MAX,<-Heqf,max_dep_relabel with (nd_pf1 := nd_pf), map_cons, map_cons. 
    erewrite shift_removeEntry_2 with (f := f) (M := max (domain g)), shift_removeEntry_2 with (f := f) (M := max (domain g)).  
    intros...
    all:eauto; simpl;try eapply in_preserves_max... 
  - Case TOutUn.
    assert (TOU :  typeCheck
                     g pf (dOut (fst u) (snd u) (fst v) (snd v) q))...
    intros.
    remember  (fun x : name * name * flag * piType =>
                 let (y, t0) := x in
                 let (y0, f) := y in
                 let (a1, a2) := y0 in
                 if In2 (a1, a2) l
                 then (a1, a2 + max (domain g), f, t0)
                 else cast x)  as f.

    unfold dep_relabel; fold dep_relabel.
    simpl in DIS; unfold fn in DIS; fold fn in DIS; destruct DIS as [FNU [FNV DIS]].

    assert (FU: forall t1, f (u, vis, t1) = (u, vis, t1)).
    intros;
      subst f; destruct u;
        case_eq (In2 (n, n0) l); intros IN2.
    simpl in FNU; rewrite in2_In_iff in IN2;  intuition auto.
    unfold cast,castF at 1.
    unfold flag_eq at 1; fold flag_eq; simpl...
    assert (FV: forall t2, f (v, vis, t2) = (v, vis, t2)).
    intros; subst f; destruct v;
      case_eq (In2 (n, n0) l); intros IN2.
    simpl in FNU; rewrite in2_In_iff in IN2;  intuition auto.
    unfold cast,castF at 1.
    unfold flag_eq at 1; fold flag_eq; simpl...
    assert (nd_pf15 : NoDup (domain ((v, vis, t2) :: removeEntry v (map f g)))).
    subst f; eapply no_dup_cons_removeEntry, no_dup_shift...
    eapply no_dup_isMap in nd_pf15 as pf15.
    eapply TOutUn with (pf1 := pf15).
    eauto. eauto.
    
    assert (INM : In (f (u, vis, Chan un p t)) (map f g)).
    eapply in_map... erewrite FU in INM... 
    assert (INM : In (f (v, vis, t')) (map f g)).
    eapply in_map... erewrite FV in INM...

    assert (u <> v).
    eapply typeCheck_object_neq_subject in TOU; move TOU at bottom. unfold nonRec_typable in TOU; fold nonRec_typable in TOU; destruct TOU as [ABS _]; rewrite <-surjective_pairing in ABS; rewrite <-surjective_pairing in ABS; intuition auto...

    assert (nd_pf'' :
              NoDup (domain ((v, vis, t2) :: removeEntry v g))).
    eapply no_dup_cons_removeEntry...
    assert (IH: incl (secLabs q) l ).
    simpl in IN; intuition.
    assert (nd_pf2 : NoDup (domain (
                    (map
                       (fun x : name * name * flag * piType =>
                          let (y, t) := x in
                          let (y0, f) := y in
                          let (a1, a2) := y0 in
                          if In2 (a1, a2) l
                          then
                            (a1,
                             a2 +
                             max
                               (domain
                                  ((v, vis, t2) :: removeEntry v g)), f, t)
                          else cast x)
                       ( (v, vis, t2) :: removeEntry v g))))).
    eapply no_dup_shift...
    eapply no_dup_isMap in nd_pf2 as pf2.
    eapply IHTC with (pf1 := pf2) (nd_pf := nd_pf'') in IH.
    revert dependent pf15.
    erewrite <-FV. intros.
    
    assert (MAX: max (domain g) = max (domain ((v, vis, t2) :: removeEntry v g))).
    destruct v; erewrite max_removeEntry_cons...

    move IH at bottom.
    destruct v.
    revert dependent pf2; rewrite <-MAX,<-Heqf,max_dep_relabel with (nd_pf1 := nd_pf), map_cons. erewrite shift_removeEntry_2 with (f := f) (M := max (domain g)).  
    intros...
     all:eauto; simpl;try eapply in_preserves_max...
  - Case TInL.
    assert (TOL :  typeCheck
                     g pf (dInp (fst u) (snd u) (fst x) (snd x) q))...
    intros.
    remember  (fun x : name * name * flag * piType =>
                 let (y, t0) := x in
                 let (y0, f) := y in
                 let (a1, a2) := y0 in
                 if In2 (a1, a2) l
                 then (a1, a2 + max (domain g), f, t0)
                 else cast x)  as f.

    assert (x<> u). destruct x, u; eapply in_diff_not_in...
    assert (NOTIN: ~In x l).  unfold bv in DIS2; fold bv in DIS2; eapply disjoint_l_cons in DIS2; rewrite <-surjective_pairing in DIS2; intuition auto.
    
    unfold dep_relabel; fold dep_relabel.
    simpl in DIS; unfold fn in DIS; fold fn in DIS.
    assert (EQ: (if nat_pair_eq_dec (fst x, snd x) (fst u, snd u)
                 then List.remove nat_pair_eq_dec (fst x, snd x) (fn q)
                 else (fst u, snd u) :: List.remove nat_pair_eq_dec (fst x, snd x) (fn q)) = (fst u, snd u) :: List.remove nat_pair_eq_dec (fst x, snd x) (fn q)).
    case (nat_pair_eq_dec (fst x, snd x) (fst u, snd u)). intros; rewrite <-surjective_pairing,<-surjective_pairing in e; intuition auto. intros... rewrite EQ in DIS; clear EQ.
    assert (~ In u l). destruct u; eapply disjoint_l_cons...
    assert (FU: forall t1, f (u, vis, t1) = (u, vis, t1)).
    intros;
      subst f; destruct u;
        case_eq (In2 (n, n0) l); intros IN2.
    rewrite in2_In_iff in IN2;  intuition auto.
    unfold cast,castF at 1.
    unfold flag_eq at 1; fold flag_eq; simpl...
    assert (nd_pf15 : NoDup (domain (((u, vis, t1) :: (x, vis, t) :: removeEntry u (map f g))))).
    subst f; destruct x as [x1 x2], u; erewrite removeEntry_shift;
      try eapply no_dup_cons_removeEntry; simpl;
        try econstructor; try eapply var_not_in_map;
          try eapply no_dup_shift...
    eapply no_dup_isMap in nd_pf15 as pf15.
    eapply TInL with (pf1 := pf15).
    eauto. 
    
    assert (INM : In (f (u, vis, Chan lin p t)) (map f g)).
    eapply in_map... erewrite FU in INM...

    subst f; eapply var_not_in_map...

    assert (max (domain g) <= max (domain (map f g))).
    subst f; eapply max_map...
    lia.

    assert (nd_pf'' :
              NoDup (domain (((u, vis, t1) :: (x, vis, t) :: removeEntry u g)))).
    assert (NoDup (domain ((u, vis, t1) :: removeEntry u g))).
    eapply no_dup_cons_removeEntry...
    assert (NoDup (domain ((x, vis, t):: (u, vis, t1) :: removeEntry u g))).
    eapply NoDup_cons... fold domain.
    intro. inversion H6...
    (* In x (domain (removeEntry u g)) -> False *)
    eapply in_domain_in_g in H7 as (ff &tt &ABS);
      eapply in_removeEntry,in_g_in_domain in ABS; contradiction.
    (*NoDup (domain ((u, vis, t1) :: (x, vis, t) :: removeEntry u g))*)
    destruct x as [x1 x2], u; erewrite removeEntry_shift;
      try eapply no_dup_cons_removeEntry; simpl;
        try econstructor...
    
    assert (IH: incl (secLabs q) l ).
    simpl in IN; intuition.
    assert (nd_pf2 : NoDup (domain 
                    (map
                       (fun x0 : name * name * flag * piType =>
                          let (y, t0) := x0 in
                          let (y0, f) := y in
                          let (a1, a2) := y0 in
                          if In2 (a1, a2) l
                          then
                            (a1,
                             a2 + max (domain ((u, vis, t1) :: (x, vis, t) :: removeEntry u g)),
                             f, t0)
                          else cast x0) ((u, vis, t1) :: (x, vis, t) :: removeEntry u g)))).
    eapply no_dup_shift...
    eapply no_dup_isMap in nd_pf2 as pf2.
    eapply IHTC with (pf1 := pf2) (nd_pf := nd_pf'') in IH.
    revert dependent pf15.
    erewrite <-FU. intros.
    
    assert (MAX: max (domain g) = max (domain ((u, vis, t1) :: (x, vis, t) :: removeEntry u g))).
    assert (max (domain g) = max (domain ((u, vis, t1) :: removeEntry u g))).
    destruct u. eapply max_removeEntry_cons...
    assert (max (domain g) = max (domain ((x, vis, t) :: (u, vis, t1) :: removeEntry u g))).
    erewrite <-rewrite_max_var with (g := (u, vis, t1) :: removeEntry u g)... 
    erewrite max_same_domain with (l := domain g).
    eauto.
    (* forall x0 : name * name,
  In x0 (domain ((u, vis, t1) :: removeEntry u g)) <-> In x0 (domain g)*)
    destruct u; intros; eapply cons_removeEntry_iff...
    rewrite H6.
    eapply max_same_domain.
    (*forall x0 : name * name,
  In x0 (domain ((x, vis, t) :: (u, vis, t1) :: removeEntry u g)) <->
  In x0 (domain ((u, vis, t1) :: (x, vis, t) :: removeEntry u g))*)
    eapply cons_cons_iff...
    move IH at bottom.
    destruct u. revert dependent pf2; rewrite <-MAX,<-Heqf,max_dep_relabel with (nd_pf1 := nd_pf), map_cons, map_cons.
    revert dependent pf15. rewrite Heqf. 
    erewrite shift_removeEntry_2 with (M := max (domain g )).
    destruct x. move NOTIN at bottom. rewrite <-in2_nIn_iff in NOTIN.
    rewrite NOTIN.
    intros... 
    eauto.
    assumption.
    simpl; try eapply in_preserves_max...
    tauto.
    destruct x; erewrite removeEntry_shift,<-max_removeEntry_cons,<-rewrite_max_var; simpl...
    eapply disjoint_l_cons in DIS;
    destruct DIS as [DIS _]; eapply disjoint_remove in DIS; eauto; erewrite <-surjective_pairing...
    unfold bv in DIS2; fold bv in DIS2; eapply disjoint_l_cons in DIS2; intuition auto.
    all:eauto. 
  - Case TInUn.
    assert (TOL :  typeCheck
                     g pf (dInp (fst u) (snd u) (fst x) (snd x) q))...
    intros.
    remember  (fun x : name * name * flag * piType =>
                 let (y, t0) := x in
                 let (y0, f) := y in
                 let (a1, a2) := y0 in
                 if In2 (a1, a2) l
                 then (a1, a2 + max (domain g), f, t0)
                 else cast x)  as f.

    assert (x<> u). destruct x, u; eapply in_diff_not_in...
    assert (NOTIN: ~In x l).  unfold bv in DIS2; fold bv in DIS2; eapply disjoint_l_cons in DIS2; rewrite <-surjective_pairing in DIS2; intuition auto.
    
    unfold dep_relabel; fold dep_relabel.
    simpl in DIS; unfold fn in DIS; fold fn in DIS.
    assert (EQ: (if nat_pair_eq_dec (fst x, snd x) (fst u, snd u)
                 then List.remove nat_pair_eq_dec (fst x, snd x) (fn q)
                 else (fst u, snd u) :: List.remove nat_pair_eq_dec (fst x, snd x) (fn q)) = (fst u, snd u) :: List.remove nat_pair_eq_dec (fst x, snd x) (fn q)).
    case (nat_pair_eq_dec (fst x, snd x) (fst u, snd u)). intros; rewrite <-surjective_pairing,<-surjective_pairing in e; intuition auto. intros... rewrite EQ in DIS; clear EQ.
    assert (~ In u l). destruct u; eapply disjoint_l_cons...
    assert (FU: forall t1, f (u, vis, t1) = (u, vis, t1)).
    intros;
      subst f; destruct u;
        case_eq (In2 (n, n0) l); intros IN2.
    rewrite in2_In_iff in IN2;  intuition auto.
    unfold cast,castF at 1.
    unfold flag_eq at 1; fold flag_eq; simpl...
    assert (pf15 : isMap (((x, vis, t) ::(map f g)))).
    eapply isMap_not_in; subst f. eapply var_not_in_map...
    eapply map_is_map...
    
    eapply TInUn with (pf1 := pf15).
    eauto. 
    
    assert (INM : In (f (u, vis, Chan un p t)) (map f g)).
    eapply in_map... erewrite FU in INM...

    subst f; eapply var_not_in_map...

    assert (max (domain g) <= max (domain (map f g))).
    subst f; eapply max_map...
    lia.

    assert (nd_pf'' :
              NoDup (domain ((x, vis, t) :: g))).
    eapply NoDup_cons... fold domain.
    
    assert (IH: incl (secLabs q) l ).
    simpl in IN; intuition.
    assert (pf2 :  isMap
                     (map
                        (fun x0 : name * name * flag * piType =>
                           let (y, t0) := x0 in
                           let (y0, f) := y in
                           let (a1, a2) := y0 in if In2 (a1, a2) l then (a1, a2 + max (domain ((x, vis, t) :: g)), f, t0) else cast x0)
                        ((x, vis, t) :: g))).
    
    eapply map_is_map...
    eapply IHTC with (pf1 := pf2) (nd_pf := nd_pf'') in IH.
    
    assert (MAX: max (domain g) = max ( domain((x, vis, t) :: g))).
    erewrite <-rewrite_max_var... 
    
    move IH at bottom.
    
    destruct x. move NOTIN at bottom. rewrite <-in2_nIn_iff in NOTIN.
    revert dependent pf2; rewrite map_cons, NOTIN.
    unfold cast at 3. unfold castF. unfold flag_eq.
    erewrite max_dep_relabel with (g := (n, n0, vis, t) :: g) (nd_pf1 := nd_pf).
    intros...
    subst f. revert dependent pf15; rewrite MAX... 

    intuition auto.
    eapply disjoint_l_cons in DIS.
    destruct DIS as [DIS _]; eapply disjoint_remove in DIS; eauto; erewrite <-surjective_pairing...
    unfold bv in DIS2; fold bv in DIS2; eapply disjoint_l_cons in DIS2; intuition auto.
    eauto.

  - Case TInU.
    assert (TOL :  typeCheck
                     g pf (dBang (fst u) (snd u) (fst x) (snd x) q))...
    intros.
    remember  (fun x : name * name * flag * piType =>
                 let (y, t0) := x in
                 let (y0, f) := y in
                 let (a1, a2) := y0 in
                 if In2 (a1, a2) l
                 then (a1, a2 + max (domain g), f, t0)
                 else cast x)  as f.

    assert (x<> u). destruct x, u; eapply in_diff_not_in...
    assert (NOTIN: ~In x l).  unfold bv in DIS2; fold bv in DIS2; eapply disjoint_l_cons in DIS2; rewrite <-surjective_pairing in DIS2; intuition auto.
    
    unfold dep_relabel; fold dep_relabel.
    simpl in DIS; unfold fn in DIS; fold fn in DIS.
    assert (EQ: (if nat_pair_eq_dec (fst x, snd x) (fst u, snd u)
                 then List.remove nat_pair_eq_dec (fst x, snd x) (fn q)
                 else (fst u, snd u) :: List.remove nat_pair_eq_dec (fst x, snd x) (fn q)) = (fst u, snd u) :: List.remove nat_pair_eq_dec (fst x, snd x) (fn q)).
    case (nat_pair_eq_dec (fst x, snd x) (fst u, snd u)). intros; rewrite <-surjective_pairing,<-surjective_pairing in e; intuition auto. intros... rewrite EQ in DIS; clear EQ.
    assert (~ In u l). destruct u; eapply disjoint_l_cons...
    assert (FU: forall t1, f (u, vis, t1) = (u, vis, t1)).
    intros;
      subst f; destruct u;
        case_eq (In2 (n, n0) l); intros IN2.
    rewrite in2_In_iff in IN2;  intuition auto.
    unfold cast,castF at 1.
    unfold flag_eq at 1; fold flag_eq; simpl...
    
    assert (pf15 : isMap (((x, vis, t) ::(map f g)))).
    eapply isMap_not_in; eauto; subst f; eapply var_not_in_map;eauto;eapply map_is_map...

    assert (nd_pf16 : NoDup (domain (vis_proj (map f g) ++ ill_proj (map f g)))).
    erewrite domain_distr,no_dup_iff.
    split. subst f; try eapply no_dup_vis_proj,no_dup_shift...
    split. subst f; try eapply no_dup_ill_proj, no_dup_shift...
    subst f; eapply disjoint_projections, no_dup_shift...
    eapply no_dup_isMap in nd_pf16 as pf16.
    
    eapply TInU with (pf1 := pf15) (pf2 := pf16).
    eauto. 
    
    assert (INM : In (f (u, vis, Chan un p t)) (map f g)).
    eapply in_map... erewrite FU in INM...

    subst f; eapply var_not_in_map...

    assert (max (domain g) <= max (domain (map f g))).
    subst f; eapply max_map...
    lia.
    
    (* cons (vis_proj (map f g) ++ ill_proj (map f g)) pf16 *)
    erewrite tc_ill_vis.cons_distr in *; split.
    subst; eapply cons_vis_proj_map  with (M := max (domain g));
      intuition... 
    eapply cons_ill_proj_map with (M := max (domain g)) (l := l);
      intuition...

    assert (nd_pf'' :
              NoDup (domain ((x, vis, t) :: g))).
    eapply NoDup_cons... fold domain.
    
    assert (IH: incl (secLabs q) l ).
    simpl in IN; intuition.
    assert (pf3 :  isMap
                     (map
                        (fun x0 : name * name * flag * piType =>
                           let (y, t0) := x0 in
                           let (y0, f) := y in
                           let (a1, a2) := y0 in if In2 (a1, a2) l then (a1, a2 + max (domain ((x, vis, t) :: g)), f, t0) else cast x0)
                        ((x, vis, t) :: g))).
    
    eapply map_is_map...
    eapply IHTC with (pf1 := pf3) (nd_pf := nd_pf'') in IH.
    
    assert (MAX: max (domain g) = max ( domain((x, vis, t) :: g))).
    erewrite <-rewrite_max_var...

    
    move IH at bottom.
    
    destruct x. move NOTIN at bottom. rewrite <-in2_nIn_iff in NOTIN.
    revert dependent pf3; rewrite map_cons, NOTIN.
    unfold cast at 3. unfold castF. unfold flag_eq.
    erewrite max_dep_relabel with (g := (n, n0, vis, t) :: g) (nd_pf1 := nd_pf).
    intros...
    subst f. revert dependent pf15; rewrite MAX... 

    intuition auto.
    eapply disjoint_l_cons in DIS.
    
    destruct DIS as [DIS _]; eapply disjoint_remove in DIS; eauto; erewrite <-surjective_pairing...
    unfold bv in DIS2; fold bv in DIS2; eapply disjoint_l_cons in DIS2; intuition auto.
    eauto.
    Unshelve.
    24: { eapply isMap_distr in pf2; intuition. }
    24: { eapply isMap_distr in pf2; intuition. } 
    all : try assumption.
    try eapply no_dup_split_no_dup_r with (g := g)...
    try eapply no_dup_split_no_dup_r with (g := g)...
    try eapply no_dup_split_no_dup_r with (g := g)...
    try eapply no_dup_split_no_dup_l with (g := g).
    eauto.
    eauto.
    try eapply no_dup_split_no_dup_r with (g := g)...
    eapply isMap_distr in pf16; intuition.
    Unshelve.
    all:  eapply isMap_distr in pf16; intuition.
Qed.
