Require Import
        Bool List Omega PeanoNat Program.Equality
        ListAddOns Max RemoveEntry Domain NewEntries
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
        (*split_existential_2*) 
        type_checking_1
        lts_no_dup 
        proposition27
        disjoint_newEntries
	      tc_prelim
        split_cons_remove
        type_system_rules.



   Lemma type_plus_distr: forall s1 s2 s r1 r2 r t, 
      type_plus s r t ->
      type_plus s1 s2 s ->
      type_plus r1 r2 r ->
      (is_unrestricted s ->
       s1 = s2 /\ s2 = s /\ r1 = r2 /\ r2 = r) ->
      exists t1 t2,
        type_plus s1 r1 t1 /\
        type_plus s2 r2 t2 /\
        type_plus t1 t2 t /\
        (is_unrestricted s -> t1 = t2 /\ t2 = t).
  Proof with eauto using un_is_unrestricted.
    intros.
    destruct s. destruct m. destruct p.
    - inversion H; inversion H0.  subst.
      assert (p2 = p)... inversion H11...
      assert (p0 = empty /\ p3 = empty). inversion H7; inversion H11; subst...
      inversion H7... inversion H7... 
      exists r1, r2. inversion H11; subst; intuition.
      all:inversion H1...       
    - inversion H; inversion H0.  subst.
      inversion H11. subst. inversion H7.
      subst. assert (r1 =  (Chan lin empty s) /\ r2 =  (Chan lin empty s)). inversion H1. inversion H6; subst...
      intuition.
      exists r1, (Chan lin inp s). subst; intuition.
      subst.
      inversion H1. inversion H6; subst p t.
      exists (Chan lin empty s), (Chan lin io s).
      intuition. inversion H3. destruct H14. inversion H14.
      subst...
      exists (Chan lin out s), (Chan lin inp s).
      intuition.
      subst. 
      inversion H9. inversion H9. subst.
      inversion H7; inversion H1; inversion H10; subst.
      exists (Chan lin inp s),  (Chan lin empty s).
      intuition. 
      exists (Chan lin inp s),  (Chan lin empty s).
      intuition.
      inversion H15. inversion H15.
      inversion H1. inversion H4; subst.
      exists (Chan lin inp s),  (Chan lin out s).
      intuition.
      inversion H6. inversion H6.
      exists (Chan lin io s),  (Chan lin empty s).
      intuition.
      inversion H10. inversion H10.
    - inversion H; inversion H0.  subst.
      inversion H11. subst. inversion H7.
      subst. assert (r1 =  (Chan lin empty s) /\ r2 =  (Chan lin empty s)). inversion H1. inversion H6; subst...
      intuition.
      exists r1, (Chan lin out s). subst; intuition.
      subst.
      inversion H1. inversion H6; subst p t.
      exists (Chan lin empty s), (Chan lin io s).
      intuition. inversion H3. destruct H14. inversion H14.
      subst...
      exists (Chan lin inp s), (Chan lin out s).
      intuition.
      subst. 
      inversion H9. inversion H9. subst.
      inversion H7; inversion H1; inversion H10; subst.
      exists (Chan lin out s),  (Chan lin empty s).
      intuition. 
      exists (Chan lin out s),  (Chan lin empty s).
      intuition.
      inversion H15. inversion H15.
      inversion H1. inversion H4; subst.
      exists (Chan lin out s),  (Chan lin inp s).
      intuition.
      inversion H6. inversion H6.
      exists (Chan lin io s),  (Chan lin empty s).
      intuition.
      inversion H10. inversion H10.
    - inversion H. inversion H7; subst.
       assert (r1 = (Chan lin empty s) /\ r2 =(Chan lin empty s)). inversion H1. inversion H6; subst...
       intuition. subst.
       exists s1, s2; intuition.
       inversion H0. apply Tp_LinPlus...
       inversion H0. apply Tp_LinPlus...
    - assert (is_unrestricted (Chan un p s))...
      eapply H2 in H3; intuition;subst...
      inversion H; subst...
      exists  (Chan un (pol_cup p p2) s),
      (Chan un  (pol_cup p p2) s).
      intuition.
      rewrite <-pol_cup_id at 3...
    - exists Top, Top. intuition.
      inversion H. inversion H0; inversion H1;  subst...
      inversion H10. inversion H9.
      inversion H. inversion H0; inversion H1;  subst...
      inversion H10. inversion H9.
      inversion H. inversion H0; inversion H1;  subst...
      inversion H...
   Qed.



  Hint Resolve beq_nat_refl.

 
 
 


      Lemma true_true :  true && true = true.
      Proof. intuition.
      Qed.

      Lemma diff_false: forall x1 x2 v1 v2,
          (x1, x2) <> (v1, v2) ->
          (v1 =? x1) && (v2 =? x2) = false.
      Proof with eauto.
        intros.
        unfold andb;
        case_eq (v1 =? x1); intros;
          case_eq (v2 =? x2); intros;
        try rewrite Nat.eqb_eq in *; subst; intuition.
      Qed.

      Lemma pol_plus_middle: forall q1 q2 q3 q4 q5 p1,
        pol_plus q1 q2 q3 ->
        pol_plus q3 q4 q5 ->
        pol_plus q1 p1 q5 ->
        pol_plus q2 q4 p1.
      Proof with eauto.
        intros q1 q2 q3 q4 q5 p1 A B C.
        destruct p1.
        - inversion C; inversion B; inversion A; subst...
          all:discriminate.
        - inversion C; inversion B; inversion A; subst...
          all:discriminate.
        - inversion C; inversion B; inversion A; subst...
          all:discriminate.
        - inversion C; inversion B; inversion A; subst...
          all:discriminate.
      Qed.
