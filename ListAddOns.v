Require Export compat.
Require Import List PeanoNat Bool Classical Lia Program.Equality.

Require Import CpdtTactics LibTactics.

Set Implicit Arguments.
Open Scope bool_scope.
Open Scope list_scope.

Import ListNotations.

Section ListAddOns.

  Variable A : Type.

  Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.

  Lemma cons_app : forall a (l: list A),
      a :: l = [a] ++ l.
  Proof.
    intros.
    unfold app.
    reflexivity.
  Qed.

  

  Lemma map_nil_eq : forall (A B : Type) (f : A -> B)  l,
      l = nil -> map f l = nil.
  Proof with eauto.
    intros.  unfold map; subst...
  Qed.

  
  Lemma in_second: forall (x : A)  a l,
      In x (a :: x :: l).
  Proof.
    intros. apply in_app_iff  with (l := a :: nil) (l' := x ::l); right; apply in_eq.
  Qed.

  Lemma in_iff_swap: forall (l1 l2 : list A),
      (forall x,
          In x l1 <-> In x l2) ->
      (forall x,
          In x l2 <-> In x l1).
  Proof with eauto.
    intuition auto; try eapply H...
  Qed.

  Lemma in_iff_middle: forall (l1 l2 : list A),
      (forall x y,
          In x (l1 ++ y :: l2) <-> In x (y :: l1 ++ l2)).
  Proof with eauto using in_eq.
    split; introv IN; try eapply in_app_iff in IN as [IN1 |CONT].
    try right; try eapply in_app_iff;try left...
    inv CONT...
    right; try eapply in_app_iff; repeat right...
    inv IN as [EQ|CONT]; try eapply in_app_iff...
    try eapply in_app_iff in CONT as [IN1|IN2]; intuition.
  Qed.

  
  (* Lemmas taken from   https://github.com/coq/coq/blob/master/theories/Lists/List.v *)

  Lemma incl_nil_l : forall A (l : list A), incl nil l.
  Proof.
    intros. unfold incl; intros. inversion H.
  Qed.

  Lemma incl_l_nil : forall (l : list A), incl l nil -> l = nil.
  Proof.
    intros l; destruct l as [|a l]; intros Hincl.
    - reflexivity.
    - exfalso; apply Hincl with a; simpl; auto.
  Qed.

  

  Lemma incl_cons_inv : forall (a:A) (l m:list A),
      incl (a :: l) m -> In a m /\ incl l m.
  Proof.
    intros a l m Hi.
    split; [ | intros ? ? ]; apply Hi; simpl; auto.
  Qed.

  Lemma incl_app_inv : forall (l1 l2 m : list A),
      incl (l1 ++ l2) m -> incl l1 m /\ incl l2 m.
  Proof.
    intro l1; induction l1 as [|a l1 IHl1]; intros l2 m Hin; split; auto.
    - apply incl_nil_l.
    - intros b Hb; inversion_clear Hb; subst; apply Hin.
      + now constructor.
      + simpl; apply in_cons.
        apply incl_appl with l1; [ apply incl_refl | assumption ].
    - apply IHl1.
      now apply incl_cons_inv in Hin.
  Qed.

  
  

  Lemma incl_cons: forall (l : list A) a,
      incl l (a :: l).
  Proof with eauto. 
    intros; eapply incl_app_inv with (l1 := a :: nil); erewrite <-app_comm_cons, app_nil_l; eapply incl_refl...
  Qed. 

  Hint Resolve incl_nil_l incl_l_nil incl_cons_inv incl_app_inv.

  Lemma count_occ_app  l1 l2 x :
    count_occ eq_dec (l1 ++ l2) x = count_occ eq_dec l1 x + count_occ eq_dec l2 x.
  Proof.
    induction l1 as [ | h l1 IHl1]; cbn; trivial.
    now destruct (eq_dec h x); [ rewrite IHl1 | ].
  Qed.

  Definition remove := remove eq_dec.

  Lemma in_remove: forall l x y, In x (remove y l) -> In x l /\ x <> y.
  Proof.
    intro l; induction l as [|z l IHl]; intros x y Hin.
    - inversion Hin.
    - simpl in Hin.
      destruct (eq_dec y z) as [Heq|Hneq]; subst; split.
      + right; now apply IHl with z.
      + intros Heq; revert Hin; subst; apply remove_In.
      + inversion Hin; subst; [left; reflexivity|right].
        now apply IHl with y.
      + destruct Hin as [Hin|Hin]; subst.
        * now intros Heq; apply Hneq.
        * intros Heq; revert Hin; subst; apply remove_In.
  Qed.

  Lemma notin_remove : forall l (x : A),
      ~ In x l ->
      remove x l = l.
  Proof.
    intros l x; induction l as [|y l IHl]; simpl; intros Hnin.
    - reflexivity.
    - destruct (eq_dec x y); [subst|f_equal]; tauto.
  Qed.

  
  Lemma remove_app :
    forall l1 l2 (x:A),
      remove x (l1 ++ l2) = remove x l1 ++ remove x l2.
  Proof with auto.
    induction l1; simpl... intros.
    cases_if; crush. 
  Qed.


  Lemma elt_eq_unit l1 l2 (a b : A) :
    l1 ++ a :: l2 = [b] -> a = b /\ l1 = [] /\ l2 = [].
  Proof.
    intros Heq.
    apply app_eq_unit in Heq.
    now destruct Heq as [[Heq1 Heq2]|[Heq1 Heq2]]; inversion_clear Heq2.
  Qed.

  Lemma NoDup_filter  f (l : list A) : NoDup l -> NoDup (filter f l).
  Proof.
    induction l as [|a l IHl]; simpl; intros Hnd; auto.
    apply NoDup_cons_iff in Hnd.
    destruct (f a); [ | apply IHl; easy ].
    apply NoDup_cons_iff; split; [intro H|]; intuition.
    apply filter_In in H; intuition.
  Qed.

  Lemma app_cons_inv : forall a b (l1 l2 l3 l4 : list A),
      l1 ++ a :: l2 = l3 ++ b :: l4 ->
      ~In b l1 -> ~In a l3 -> a = b.
  Proof with eauto.
    intros a b l1 l2 l3 l4 H H0 H1.
    dependent induction l1; destruct l3; simpl in *.
    - injection H as (). reflexivity.
    - apply Decidable.not_or in H1 as []. contradict H1. injection H...
    - apply Decidable.not_or in H0 as []. contradict H0. injection H...
    - injection H as (). eapply IHl1...
  Qed.

  

  Lemma not_in_filter  f e (l : list A) : ~ In e l -> ~ In e (filter f l).
  Proof with eauto.
    intros H. induction l... simpl.
    apply not_in_cons in H as [H H0].
    destruct (f a)... apply not_in_cons...
  Qed.

  Lemma in_equal_lists (l1 l2 : list A) e : l1 = l2 -> In e l1 -> In e l2.
  Proof. intros. subst. exact H0. Qed.

  
  Lemma in_in_remove : forall l (x y :A), x <> y -> In x l -> In x (remove y l).
  Proof.
    intros l; induction l as [|z l IHl]; simpl; intros x y Hneq Hin.
    - apply Hin.
    - destruct (eq_dec y z); subst.
      + destruct Hin.
        * exfalso; now apply Hneq.
        * now apply IHl.
      + simpl; destruct Hin; [now left|right].
        now apply IHl.
  Qed.

  

  Lemma last_length : forall (l : list A) a, List.length (l ++ a :: nil) = S (List.length l).
  Proof.
    intros ; rewrite List.app_length ; simpl.
    rewrite <- plus_n_Sm, plus_n_O; reflexivity.
  Qed.



  (* end *)


  Lemma app_unit_hd  a (l1 l2 l3 : list A):
    a :: l1 = l2 ++ l3 ->
    exists l4, l2 = a:: l4 \/
               l2 = nil /\ l3 = a::l4.
  Proof with eauto.
    introv EQ. gen a l1 l3. induction l2.
    intros; exists l1...
    intros. 
    inv EQ...
  Qed.
  
  Lemma app_unit_tl a (l1 l2 l3 : list A):
    l1 ++ [a]=l2 ++ l3 ->
    exists l4, l3 = l4++[a] \/
               l3 = nil /\ l2 = l4++[a].
  Proof with eauto using app_unit_hd.
    introv EQ; gen a l1 l2. induction l3.
    intros; exists l1; rewrite app_nil_r in *; intuition. 
    intros.
    
    assert (EQ2: l2 ++ a :: l3 =
                 (l2 ++ [a]) ++ l3).
    rewrite <-app_assoc, cons_app...
    rewrite EQ2 in EQ; clear EQ2;
      try eapply IHl3 in EQ as (l4 &[A1|B1]); clear IHl3;
        intuition; subst.
    exists (a::l4)...
    exists (nil:list A); left...
    assert (REV:  rev(l2 ++ [a]) = rev(l4 ++ [a0]));
      try rewrite H0...
    repeat rewrite rev_unit in REV; inv REV...
  Qed.

  Lemma app_eq_not_in (l1 l2 l3 l4 : list A) a:
    l1 ++ a :: l2 = l3 ++ a :: l4 ->
    ~In a l3 ->
    ~In a l4 ->
    ~In a l1 /\ ~In a l2.
  Proof with eauto.
    introv EQ NIN1 NIN2.
    assert (CO: count_occ eq_dec (l3 ++ a :: l4) a =
                S(count_occ eq_dec l3 a + count_occ eq_dec l4 a)).
    erewrite count_occ_app; simpl; case_eq (eq_dec a a); intros; try contradiction...
    assert (EQ1: count_occ eq_dec l3 a=0).
    erewrite <-count_occ_not_In...
    assert (EQ2: count_occ eq_dec l4 a=0).
    erewrite <-count_occ_not_In...
    erewrite EQ1,EQ2,<-EQ,count_occ_app in *;
      simpl in CO;case_eq (eq_dec a a); introv ID;
        rewrite ID in *; try contradiction...
    assert (count_occ eq_dec l1 a = 0 /\
            count_occ eq_dec l2 a =0) by lia.
    repeat erewrite count_occ_not_In...
  Qed.

  Theorem app_eq_app (x1 x2 y1 y2: list A) : x1++x2 = y1++y2 ->
                                             exists l, (x1 = y1++l /\ y2 = l++x2) \/ (y1 = x1++l /\ x2 = l++y2).
  Proof.
    revert y1. induction x1 as [|a x1 IH].
    - cbn. intros y1 ->. exists y1. now right.
    - intros [|b y1]; cbn.
      + intros <-. exists (a :: x1). now left.
      + intros [=-> [l Hl] %IH]. exists l.
        now destruct Hl as [[-> ->]|[-> ->]]; [left|right].
  Qed.
  
  Lemma app_eq_middle (l1 l2 l3 l4 : list A) a:
    l1 ++ a :: l2 = l3 ++ a :: l4 ->
    ~In a l3 ->
    ~In a l4 ->
    l1 = l3 /\ l2 = l4.
  Proof with eauto.
    introv EQ NIN3 NIN4.
    apply app_eq_app in EQ as  (l &[B|C]).
    destruct l; destruct B as (B1&B2);
      try rewrite app_nil_l,app_nil_r in *;
      inv B2; intuition.
    destruct l; destruct C as (B1&B2);
      try rewrite app_nil_l,app_nil_r in *;
      inv B2; intuition.
  Qed.
  

  Definition diff  (l : list A) el :=
    forall x, In x l -> x <> el.

  Lemma diff_app: forall (l1 l7 m1 m2 : list A)  el,
      l1 ++ l7 = m1 ++ el :: m2 ->
      diff l1 el ->
      exists m', l7 = m' ++ el :: m2.
  Proof with eauto.
    intros; assert (DIFF:=H0);unfold diff in *.
    revert dependent l1. revert dependent l7.
    induction m1.
    - exists (nil : list A); destruct l1; inversion H; subst; specialize DIFF with el; intuition...
    - intros;
        destruct l1; inversion H; subst; specialize H0 with el; intuition...
      assert ( forall x : A, In x l1 -> x = el -> False).
      intros x ABS; specialize DIFF with x; intuition.
      eauto.
  Qed.

  Lemma app_inv_head_iff:
    forall l l1 l2 : list A, l ++ l1 = l ++ l2 <-> l1 = l2.
  Proof.
    intro l; induction l as [|? l IHl]; split; intros H; simpl; auto.
    - apply IHl. inversion H. auto.
    - subst. auto.
  Qed.


  Theorem in_split2: forall x (l:list A), In x l -> exists l1 l2, l = l1++x::l2 /\ ~In x l1.
  Proof.
    intros x l; induction l as [|a l IHl]; simpl; [destruct 1|destruct 1 as [?|H]].
    - subst a; auto.
      exists (nil : list A) l; auto.
    - destruct (IHl H) as (l1,(l2,(H0,H1)));
        clear IHl.
      case_eq (eq_dec a x); intros; subst.
      exists (nil:list A) (l1 ++ x :: l2); intuition.
      exists (a::l1) l2; simpl. split. apply f_equal. auto.
      intuition.
  Qed.

  

  Lemma incl_incl : forall (l : list A),
      incl l l.
  Proof with eauto. unfold incl in *; induction l...
  Qed.


  Lemma not_in_app_and : forall A (l m:list A) (a:A), 
      ~In a (l ++ m) -> ~In a l /\ ~In a m. 
  Proof.
    intros.
    split.
    induction l; intuition.
    induction m; intuition.
  Qed.

  Lemma not_in_and_app : forall  (l m:list A) (a:A), 
      ~In a l ->
      ~In a m ->
      ~In a (l ++ m). 
  Proof.
    intros.
    induction l; intuition.
    induction m; intuition.
    apply in_inv with (l := l ++ nil) in H1.
    intuition; subst.
    specialize in_eq with (a := a) (l := l) as INEQ; intuition.
    apply in_inv with (l := l ++ a1 :: m) in H1.
    intuition; subst.
    specialize in_eq with (a := a) (l := l) as INEQ; intuition.
  Qed.


  Lemma in_nil: forall (l : list A), In l [] -> l = [].
  Proof. intuition. Qed.



  Lemma in_concat : forall l (y : A),
      In y (concat l) <-> exists x, In x l /\ In y x.
  Proof.
    intro l; induction l as [|a l IHl]; simpl; intro y; split; intros H.
    contradiction.
    destruct H as (x,(H,_)); contradiction.
    destruct (in_app_or _ _ _ H) as [H0|H0].
    exists a; auto.
    destruct (IHl y) as (H1,_); destruct (H1 H0) as (x,(H2,H3)).
    exists x; auto.
    apply in_or_app.
    destruct H as (x,(H0,H1)); destruct H0.
    subst; auto.
    right; destruct (IHl y) as (_,H2); apply H2.
    exists x; auto.
  Qed.

  

  Lemma find_app  : forall f (l1 l2 : list A),
      find f l1 = None ->
      find f (l1 ++ l2) = find f l2.
  Proof with auto.
    intros.
    induction l1...
    rewrite <- app_comm_cons...
    simpl. simpl in H.
    destruct (f a)...
    discriminate H.
  Qed.


  Lemma find_app_tl : forall f (l1 l2 : list A),
      find f l2 = None ->
      find f (l1 ++ l2) = find f l1.
  Proof.
    intros f l1 l2 H.
    induction l1 as [|a l1 IHl1], l2.
    - simpl. reflexivity.
    - exact H.
    - rewrite <- app_nil_end. reflexivity.
    - simpl. case (f a).
      + reflexivity.
      + exact IHl1.
  Qed.

  Lemma filter_app  f (l l':list A) :
    filter f (l ++ l') = filter f l ++ filter f l'.
  Proof.
    induction l as [|x l IH]; simpl; trivial.
    destruct (f x); simpl; now rewrite IH.
  Qed.


  Lemma length_filter : forall f (l : list A),
      length (filter f l) <= length l.
  Proof with auto.
    intros f l.
    induction l as [|a l IH]...
    simpl.
    case (f a).
    simpl.
    apply le_n_S.
    trivial.
    eapply le_trans with (length l).
    exact IH.
    apply Nat.le_succ_diag_r.
  Qed.


  Lemma filter_conjunction :
    forall f1 f2 (l: list A),
      filter f1 (filter f2 l) = filter (fun a:A => (f1 a) && (f2 a)) l.
  Proof with auto.
    intros.
    induction l...
    rewrite cons_app.
    repeat rewrite filter_app.
    rewrite <- IHl. clear IHl.
    assert (filter f1 (filter f2 [a]) = filter (fun a0 : A => f1 a0 && f2 a0) [a]).
    - unfold filter. case (f2 a).
      + case (f1 a)...
      + rewrite andb_comm...
    - rewrite <- H.
      reflexivity.
  Qed.

  Lemma nodup_prop_aux_single :
    forall (l_left l_right: list A) a,
      NoDup (l_left ++ a :: l_right) ->
      ~ In a l_left /\
      ~ In a l_right.
  Proof.
    intros.
    apply NoDup_remove in H as [_ H].
    apply not_in_app_and in H.
    exact H.
  Qed.

  Lemma nodup_prop_aux :
    forall (l1 l2 l3: list A) a b,
      NoDup (l1 ++ a :: l2 ++ b :: l3) ->
      ~ In a l1 /\
      ~ In a l2 /\
      ~ In a l3 /\
      ~ In b l1 /\
      ~ In b l2 /\
      ~ In b l3 /\
      a <> b.
  Proof.
    intros.
    apply nodup_prop_aux_single in H as tmp. destruct tmp as [not_in_a_l1 tmp].
    apply not_in_app_and in tmp as [not_in_a_l2 tmp].
    apply not_in_cons in tmp as [a_not_b not_in_a_l3].
    rewrite app_comm_cons in H.
    rewrite app_assoc in H.
    apply nodup_prop_aux_single in H as [tmp not_in_b_l3].
    apply not_in_app_and in tmp as [not_in_b_l1 tmp].
    apply not_in_cons in tmp as [_ not_in_b_l2].
    repeat split; trivial.
  Qed.

  
  Lemma Forall_nil_iff : forall (P : A -> Prop),
      Forall P nil <-> True.
  Proof.
    easy.
  Qed.

  Lemma Forall_cons_iff : forall (P : A -> Prop) (a:A) l, Forall P (a :: l) <-> P a /\ Forall P l.
  Proof.
    intros. now split; [intro H; inversion H|constructor].
  Qed.
  
  Lemma Forall_app : forall (P : A -> Prop) l1 l2 ,
      Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
  Proof.
    induction l1 as [|a l1 IH]; cbn.
    - intros. rewrite Forall_nil_iff; intuition.
    - intros. rewrite !Forall_cons_iff, IH, and_assoc.
      intuition.
  Qed.

  Lemma  forallb_filter : forall f (l : list A),
      forallb f (filter f l) = true.
  Proof with eauto.
    intros. induction l...
    simpl in *;
      case_eq (f a); intros;simpl; unfold andb; try rewrite H...
  Qed.

  
  Lemma flat_map_app {B} (f : A -> list B) (l1 l2 : list A) :
    flat_map f (l1 ++ l2) =
    flat_map f l1 ++ flat_map f l2.
  Proof with eauto.
    repeat rewrite flat_map_concat_map,map_app,concat_app;
      repeat rewrite <-flat_map_concat_map...
  Qed.

  Lemma flat_map_cons {B} (f : A -> list B) x (l : list A) :
    flat_map f (x :: l) =
    flat_map f [x] ++ flat_map f l.
  Proof with eauto.
    repeat rewrite flat_map_concat_map,map_cons,concat_cons;
      repeat rewrite <-flat_map_concat_map, app_nil_r...
  Qed.


  Lemma in_app_or x y (l l1 l2 : list A):
    In x l ->
    l = l1 ++ y :: l2 ->
    In x l1 \/ x = y \/ In x l2.
  Proof with eauto.
    intros IN EQ; subst;
      try eapply in_app_iff in IN as [IN | IN];
      try inversion IN; subst...
  Qed.

  Lemma length_inv : forall (x y : A) l1 l2 l3 l4,
      l1 ++ x :: l3 = l2 ++ y :: l4 ->
      List.length l1 = List.length l2 ->
      x = y /\ l1 = l2.
  Proof with eauto.
    intros. generalize dependent y.
    dependent induction l1.
    intros.
    assert (NIL: Datatypes.length (nil : list A) = 0)... erewrite NIL in H0.
    assert (Datatypes.length l2 = 0)...
    erewrite length_zero_iff_nil in H1.
    subst. inversion H...
    intros. destruct l2.
    assert (NIL: Datatypes.length (nil : list A) = 0)... erewrite NIL in H0. simpl in H0. lia.
    assert ( x = y /\ l1 = l2); inversion H...
    repeat (subst; intuition auto).
  Qed.

  Lemma length_inv_tl : forall (x y : A) l1 l2 l3 l4,
      l1 ++ x :: l3 = l2 ++ y :: l4 ->
      List.length l3 = List.length l4 ->
      x = y /\ l1 = l2.
  Proof with eauto.
    intros. generalize dependent y.
    dependent induction l3.
    intros.
    assert (NIL: Datatypes.length (nil : list A) = 0)... erewrite NIL in H0.
    assert (Datatypes.length l4 = 0)...
    erewrite length_zero_iff_nil in H1.
    subst. eapply app_inj_tail in H; intuition. 
    intros.
    eapply IHl3...
    eapply length_inv in H; intuition; subst...
    assert (LEN: List.length (l1 ++ x :: a :: l3) = List.length(l2 ++ y :: l4)). rewrite H...
    rewrite app_length,app_length in LEN. 
    assert (EQ: Datatypes.length (x :: a :: l3) = S (Datatypes.length (a :: l3))). simpl...
    rewrite EQ, H0 in LEN.
    simpl in LEN. lia. 
  Qed.



  Lemma length_inv_tl_2 : forall (l1 l2 l3 l4 : list A),
      l1 ++ l3 = l2 ++ l4 ->
      List.length l3 = List.length l4 ->
      l1 = l2.
  Proof with eauto.
    intros. 
    dependent induction l3.
    intros.
    assert (NIL: Datatypes.length (nil : list A) = 0)... erewrite NIL in H0.
    assert (Datatypes.length l4 = 0)...
    erewrite length_zero_iff_nil in H1.
    subst... rewrite app_nil_r,app_nil_r in H...
    destruct l4. simpl in H0. lia.
    simpl in H0. assert ((Datatypes.length l3) = (Datatypes.length l4)) by lia.
    eapply length_inv_tl...
  Qed.

  Lemma length_inv_2 : forall (l1 l2 l3 l4 : list A),
      l1 ++ l3 = l2 ++ l4 ->
      List.length l1 = List.length l2 ->
      l3 = l4.
  Proof with eauto.
    intros. 
    dependent induction l1.
    intros.
    assert (NIL: Datatypes.length (nil : list A) = 0)... erewrite NIL in H0.
    assert (Datatypes.length l2 = 0)...
    erewrite length_zero_iff_nil in H1.
    subst... 
    destruct l4. simpl in H0.
    assert (LEN:Datatypes.length ((a :: l1) ++ l3) = Datatypes.length  (l2 ++ nil)). rewrite H...
    erewrite app_length,app_length in LEN;simpl in LEN.
    erewrite <-H0 in LEN.
    assert (Datatypes.length l3 = 0) by lia.
    eapply length_zero_iff_nil ...
    eapply IHl1 with (l2 := tl l2) (l4 := a0 :: l4)...
    destruct l2. simpl in H0. lia .
    inversion H...
    simpl in H0...
    destruct l2. simpl in H0. lia .
    simpl...
  Qed.

  Lemma inv_tail : forall (a b c : A) l1 l2, 
      a :: b :: l1 = l2 ++ c :: nil ->
      (l1 = nil /\ b = c) \/
      exists l3, l1 = l3 ++ c :: nil.
  Proof with eauto.
    intros. generalize dependent a; generalize dependent b.  generalize dependent c. dependent induction l1...
    intros. assert (LEN: List.length (a :: b :: nil) = List.length (l2 ++ c :: nil)). rewrite H...
    erewrite app_length in LEN;destruct l2;simpl in LEN. lia. 
    assert (LEN2:List.length l2 = 0) by lia.
    erewrite length_zero_iff_nil in LEN2; subst; inversion H...

    intros. assert (LEN:  List.length (a0 :: b :: a :: l1) = List.length(l2 ++ c :: nil)). rewrite H...
    erewrite app_length in LEN;destruct l2. simpl in LEN; lia. 
    right.
    rewrite <-app_comm_cons in H.
    specialize @length_inv_2 with (l1 := a0 :: nil) (l2 := (a1 ::nil)) as K.
    eapply K,IHl1 in H as [(EQN & EQ) | (m3 & IH)].
    subst. exists (nil: list A)...
    subst. exists (a :: m3)...
    simpl...
  Qed.

  
  
  Lemma cons_cons_iff: forall (a b : A) (l : list A),
      (forall x, In x (a :: b :: l) <-> In x (b :: a :: l)).
  Proof with eauto using in_eq.
    intros. split; intros.
    inversion H; subst. right...
    inversion H0; subst...
    repeat right... 
    inversion H; subst. right...
    inversion H0; subst...
    repeat right...
  Qed.

  Lemma cons_cons_cons_iff: forall  (a b c : A) (l : list A),
      (forall x, In x (a :: b :: c :: l) <-> In x (b :: c :: a :: l)).
  Proof with eauto using in_eq.
    intros. split; intros.
    inversion H; subst. right; right...
    inversion H0; subst...
    inversion H1 as [EQ|CONT]; subst; right...
    repeat right... 
    inversion H; subst. right...
    inversion H0. subst; right; right...
    inversion H1; subst...
    repeat right...
  Qed.




End ListAddOns.