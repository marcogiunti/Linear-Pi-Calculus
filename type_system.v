Require Import
        Bool List Lia PeanoNat
        operations pi_syntax pairEq.

(********************** Type System **************************)
Section TypeSystem.

  Inductive pol : Set := empty | inp | out | io.
  Inductive mode : Set := lin | un.
  Inductive piType : Set :=
  | Chan : mode -> pol -> piType -> piType
  | Top : piType.
  Inductive flag : Set := hid | ill | vis. 

  Definition isMap (l : list ((name * name) * flag * piType)) :=
    forall x f1 t1 f2 t2,
      In (x, f1, t1) l /\ In (x, f2, t2) l ->
      f1 = f2 /\ t1 = t2.
  Definition typeEnv := list ((name * name) * flag * piType).
  
  Fixpoint pol_eq (p1 p2 : pol) : bool :=
    match p1, p2 with
    | empty, empty | inp, inp | out, out | io, io => true
    | _, _  => false
    end.

  Fixpoint mode_eq (m1 m2 : mode) : bool :=
    match m1, m2 with
    | lin, lin | un, un => true
    | _, _ => false
    end.
  
  Fixpoint type_eq (t1 t2 : piType) : bool :=
    match t1, t2 with
    | Top, Top => true
    | Chan m1 p1 t1, Chan m2 p2 t2 =>
      if mode_eq m1 m2
      then (if pol_eq p1 p2 then type_eq t1 t2 else false)
      else false
    | _, _ => false
    end.

  Fixpoint flag_eq (f1 f2 : flag) : bool :=
    match f1, f2 with
    | hid, hid | ill, ill | vis, vis => true
    | _, _  => false
    end.              

  (** Meant to be used in type environments g s.t.
      NoDup (domain g) *)
  Fixpoint removeEntry (y : (name * name)) (g : typeEnv) :=
    match g with
    | nil => nil
    | (x, f, t) :: tail =>
      if pair_eq x y
      then 
        tail
      else (x, f, t) :: removeEntry y tail
    end.

  Inductive typeOf : typeEnv -> (name * name) -> piType -> Prop :=
  | T_Entry : forall g n f t,
      In (n, f, t) g -> typeOf g n t.

  Inductive flagOf : typeEnv -> (name * name) -> flag -> Prop :=
  | F_Entry : forall g n f t,
      In (n, f, t) g -> flagOf g n f.

  Fixpoint pol_cup (p1 p2 : pol) : pol :=
    match p1, p2 with
    | empty, _ => p2
    | io, _ => io
    | _, io => io
    | out, inp => io
    | out, _ => out
    | inp, out => io
    | inp, _ => inp
    end.

  Inductive pol_plus : pol -> pol -> pol -> Prop :=
  | Pp_emptyL : forall p, pol_plus empty p p
  | Pp_emptyR : forall p, pol_plus p empty p
  | Pp_inpL:  pol_plus inp out io
  | Pp_inpR:  pol_plus out inp io.

  Inductive type_plus : piType -> piType -> piType -> Prop := 
  | Tp_Base : type_plus Top Top Top
  | Tp_LinPlus : forall p1 p2 p t,
      pol_plus p1 p2 p ->
      type_plus (Chan lin p1 t) (Chan lin p2 t) (Chan lin p t)
  | Tp_UnPlus : forall p1 p2 t,
      type_plus (Chan un p1 t) (Chan un p2 t) (Chan un (pol_cup p1 p2) t).

  
  Lemma pol_cup_id : forall p,
      pol_cup p p = p.
  Proof.
    destruct p; intuition.
  Qed.

Lemma pol_cup_empty : forall p,
    pol_cup empty p = p.
Proof with eauto.
  intros. 
  destruct p...
Qed.


Lemma pol_cup_empty_r : forall p,
    pol_cup p empty = p.
Proof with eauto.
  intros. 
  destruct p...
Qed.

Lemma pol_cup_empty_res : forall p1 p2,
    pol_cup p1 p2 = empty -> p1 = empty /\ p2 = empty.
Proof with eauto.
  intros. 
  destruct p1, p2...
  all: inversion H.
Qed.
  
  Lemma pol_cup_comm : forall p1 p2,
      pol_cup p1 p2 = pol_cup p2 p1.
  Proof.
    intros. induction p1. induction p2. tauto.
    unfold pol_cup; tauto.
    unfold pol_cup; tauto.
    unfold pol_cup; tauto.
    unfold pol_cup. fold pol_cup. induction p2. 
    unfold pol_cup; tauto.
    unfold pol_cup; tauto.
    unfold pol_cup; tauto.
    unfold pol_cup; tauto.
    unfold pol_cup. fold pol_cup. induction p2. 
    unfold pol_cup; tauto.
    unfold pol_cup; tauto.
    unfold pol_cup; tauto.
    unfold pol_cup; tauto.
    unfold pol_cup. fold pol_cup. induction p2. 
    unfold pol_cup; tauto.
    unfold pol_cup; tauto.
    unfold pol_cup; tauto.
    unfold pol_cup; tauto.
  Qed. 
  
  Lemma pol_plus_comm : forall p1 p2 p3,
      pol_plus p1 p2 p3 <-> pol_plus p2 p1 p3.
  Proof.
    intros. intuition.
    induction p1. induction p2.
    inversion H. apply Pp_emptyL.  apply Pp_emptyL.
    inversion H. apply Pp_emptyR.
    inversion H. apply Pp_emptyR.
    inversion H. apply Pp_emptyR.
    induction p2.
    inversion H. apply Pp_emptyL.
    inversion H.
    inversion H. apply Pp_inpR.
    inversion H.
    induction p2.
    inversion H. apply Pp_emptyL.
    inversion H.
    inversion H. apply Pp_inpL.
    tauto.
    inversion H.
    inversion H. apply Pp_emptyL.

    induction p2. induction p1.
    inversion H. apply Pp_emptyL.  apply Pp_emptyL.
    inversion H. apply Pp_emptyR.
    inversion H. apply Pp_emptyR.
    inversion H. apply Pp_emptyR.
    induction p1.
    inversion H. apply Pp_emptyL.
    inversion H.
    inversion H. apply Pp_inpR.
    inversion H.
    induction p1.
    inversion H. apply Pp_emptyL.
    inversion H.
    inversion H. apply Pp_inpL.
    tauto.
    inversion H.
    inversion H. apply Pp_emptyL.
  Qed.
  
  Lemma type_plus_comm : forall t1 t2 t3,
      type_plus t1 t2 t3 <-> type_plus t2 t1 t3.
  Proof.
    intuition.
    - destruct H. apply Tp_Base. rewrite pol_plus_comm in H.
      apply Tp_LinPlus with (t := t) in H. tauto.
      rewrite pol_cup_comm. apply Tp_UnPlus.
    - destruct H. apply Tp_Base. rewrite pol_plus_comm in H.
      apply Tp_LinPlus with (t := t) in H. tauto.
      rewrite pol_cup_comm. apply Tp_UnPlus.
  Qed.

  

  Lemma pol_cup_pol_cup: forall p p2,
      (pol_cup p (pol_cup p p2) = (pol_cup p p2)).
  Proof with eauto.
    destruct p.
    all:intuition.
    destruct p2; intuition.
    destruct p2; intuition.
  Qed.
  
  Lemma pol_cup_distr: forall p p1 p2,
      pol_cup (pol_cup p p1) (pol_cup p p2) = pol_cup p (pol_cup p1 p2).
  Proof with eauto.
    intros. destruct p.
    all:destruct p1, p2; unfold pol_cup...
  Qed.




  Definition is_linear (t : piType) :=
    exists p t', t = Chan lin p t'.

  Definition is_unrestricted (t : piType) :=
    exists p t', t = Chan un p t'.

  Inductive type_sub : piType -> piType -> Prop :=
  | Ts_id : forall t,
      type_sub t t 
  | Ts_empty : forall m q t,
      type_sub (Chan m empty t) (Chan m q t)
  | Ts_inp : forall m t,
      type_sub (Chan m inp t) (Chan m io t)
  | Ts_out : forall m t,
      type_sub (Chan m out t) (Chan m io t).

  Definition type_remove (t : piType) (s : piType) (r : piType) :=
    type_sub s t /\ type_plus s r t /\ (is_unrestricted t -> r = t).

  Lemma type_remove_top : forall t1 t2,
      type_remove Top t1 t2 -> (t1 = Top /\ t2 = Top).
  Proof.
    intros. unfold type_remove in H. intuition. inversion H0. tauto.
    inversion H0. rewrite <- H1 in H. inversion H.  tauto.
  Qed.

  Lemma type_remove_top_2 : forall t1 t2,
      (t1 = Top /\ t2 = Top) -> type_remove Top t1 t2.
  Proof.
    intros. destruct H. subst t1 t2. unfold type_remove. split.
    apply Ts_id. 
    split. apply Tp_Base.
    intros. tauto.
  Qed.

  Lemma type_remove_lin :   forall t t1 t2,
      (type_remove (Chan lin io t) t1 t2 ->
       (t1 = (Chan lin io t) /\ t2 = (Chan lin empty t)) \/
       (t1 = (Chan lin inp t) /\ t2 = (Chan lin out t)) \/
       (t1 = (Chan lin out t) /\ t2 = (Chan lin inp t)) \/
       (t1 = (Chan lin empty t) /\ t2 = (Chan lin io t))) /\
      (type_remove (Chan lin inp t) t1 t2 ->
       (t1 = (Chan lin inp t) /\ t2 = (Chan lin empty t)) \/
       (t1 = (Chan lin empty t) /\ t2 = (Chan lin inp t))) /\
      (type_remove (Chan lin out t) t1 t2 ->
       (t1 = (Chan lin out t) /\ t2 = (Chan lin empty t)) \/
       (t1 = (Chan lin empty t) /\ t2 = (Chan lin out t))) /\
      (type_remove (Chan lin empty t) t1 t2 ->
       t1 = (Chan lin empty t) /\ t2 = (Chan lin empty t)).
  Proof.
    split.
    - intros. unfold type_remove in H. destruct H as [H1 [H2 H3]]. inversion H1.
      subst t1 t0. inversion H2. inversion H5. tauto.
      subst t0 m t1. inversion H2. subst t2. inversion H6. tauto.
      subst t1 t0 m. inversion H2. subst t2 t0. inversion H5. tauto.
      subst t1 t0 m. inversion H2. subst t2 t0. inversion H5. tauto.
    - split. intros.
      unfold type_remove in H. destruct H as [H1 [H2 H3]]. inversion H1.
      subst t1 t0. inversion H2. inversion H5. tauto.
      subst t1 t0. inversion H2. inversion H8. tauto.
      split. intros.
      unfold type_remove in H. destruct H as [H1 [H2 H3]]. inversion H1.
      subst t1 t0. inversion H2. inversion H5. tauto.
      subst t1 t0. inversion H2. inversion H8. tauto.
      intros.
      unfold type_remove in H. destruct H as [H1 [H2 H3]]. inversion H1.
      subst t1 t0. inversion H2. inversion H5. tauto. tauto.
      subst t1 t0. inversion H2. inversion H8. tauto. tauto.
  Qed.

  Lemma type_remove_lin_2 :   forall t t1 t2,
      (((t1 = (Chan lin io t) /\ t2 = (Chan lin empty t)) \/
        (t1 = (Chan lin inp t) /\ t2 = (Chan lin out t)) \/
        (t1 = (Chan lin out t) /\ t2 = (Chan lin inp t)) \/
        (t1 = (Chan lin empty t) /\ t2 = (Chan lin io t)))
       -> (type_remove (Chan lin io t) t1 t2)) /\
      (((t1 = (Chan lin inp t) /\ t2 = (Chan lin empty t)) \/
        (t1 = (Chan lin empty t) /\ t2 = (Chan lin inp t)))
       -> type_remove (Chan lin inp t) t1 t2) /\
      (((t1 = (Chan lin out t) /\ t2 = (Chan lin empty t)) \/
        (t1 = (Chan lin empty t) /\ t2 = (Chan lin out t)))
       -> type_remove (Chan lin out t) t1 t2) /\
      ((t1 = (Chan lin empty t) /\ t2 = (Chan lin empty t))
       -> type_remove (Chan lin empty t) t1 t2).
  Proof.
    split.
    - intros. intuition.
      + subst t1 t2. unfold type_remove. split.
        * apply Ts_id.
        * split. apply Tp_LinPlus. apply Pp_emptyR.
          intro. unfold is_unrestricted in H. destruct H. destruct H. inversion H.
      + subst t1 t2. unfold type_remove. split.
        * apply Ts_inp.
        * split. apply Tp_LinPlus. apply Pp_inpL.
          intro. unfold is_unrestricted in H. destruct H. destruct H. inversion H.
      + subst t1 t2. unfold type_remove. split.
        * apply Ts_out.
        * split. apply Tp_LinPlus. apply Pp_inpR.
          intro. unfold is_unrestricted in H. destruct H. destruct H. inversion H.
      + subst t1 t2. unfold type_remove. split.
        * apply Ts_empty.
        * split. apply Tp_LinPlus. apply Pp_emptyL.
          intro. unfold is_unrestricted in H. destruct H. destruct H. inversion H.
    - split. intros. intuition.
      + subst t1 t2. unfold type_remove. split.
        * apply Ts_id.
        * split. apply Tp_LinPlus. apply Pp_emptyR.
          intro. unfold is_unrestricted in H. destruct H. destruct H. inversion H.
      + subst t1 t2. unfold type_remove. split.
        * apply Ts_empty.
        * split. apply Tp_LinPlus. apply Pp_emptyL.
          intro. unfold is_unrestricted in H. destruct H. destruct H. inversion H.
      + split.
        * intro. intuition.
          subst t1 t2. unfold type_remove. split. apply Ts_id.
          split. apply Tp_LinPlus. apply Pp_emptyR.
          intro. unfold is_unrestricted in H. destruct H. destruct H. inversion H.
          subst t1 t2. unfold type_remove. split. apply Ts_empty.
          split. apply Tp_LinPlus. apply Pp_emptyL.
          intro. unfold is_unrestricted in H. destruct H. destruct H. inversion H.
        * intro. intuition.
          subst t1 t2. unfold type_remove. split. apply Ts_id.
          split. apply Tp_LinPlus. apply Pp_emptyR.
          intro. unfold is_unrestricted in H. destruct H. destruct H. inversion H.
  Qed.

  
  Lemma un_is_unrestricted: forall p t,
      is_unrestricted (Chan un p t).
  Proof.
    intros. unfold is_unrestricted. exists p; exists t; auto.
  Qed. 
  
  Lemma type_remove_un : forall t t1 t2,
      (type_remove (Chan un io t) t1 t2 ->
       ((t1 = (Chan un io t) \/ t1 = (Chan un inp t) \/
         t1 = (Chan un out t) \/ t1 = (Chan un empty t)) /\ t2 = (Chan un io t))) /\
      (type_remove (Chan un inp t) t1 t2 ->
       ((t1 = (Chan un inp t) \/ t1 = (Chan un empty t)) /\ t2 = (Chan un inp t))) /\
      (type_remove (Chan un out t) t1 t2 ->
       ((t1 = (Chan un out t) \/ t1 = (Chan un empty t)) /\ t2 = (Chan un out t))) /\
      (type_remove (Chan un empty t) t1 t2 ->
       (t1 = (Chan un empty t) /\ t2 = (Chan un empty t))).
  Proof.
    intros. split. 
    - intros. inversion H. destruct H1 as [H2 H3].
      inversion H0.
      subst t0 t1. specialize un_is_unrestricted with io t. intros.
      apply H3 in H1. tauto.
      subst t0 t1. specialize un_is_unrestricted with io t. intros.
      apply H3 in H1. tauto.
      subst t0 t1. specialize un_is_unrestricted with io t. intros.
      apply H3 in H1. tauto.
      subst t0 t1. specialize un_is_unrestricted with io t. intros.
      apply H3 in H1. tauto.
    - split. intros.
      inversion H. destruct H1 as [H2 H3].
      inversion H0.
      subst t0 t1. specialize un_is_unrestricted with inp t. intros.
      apply H3 in H1. tauto.
      subst t0 t1. specialize un_is_unrestricted with inp t. intros.
      apply H3 in H1. tauto.
      split. intros.
      inversion H. destruct H1 as [H2 H3].
      inversion H0.
      subst t0 t1. specialize un_is_unrestricted with out t. intros.
      apply H3 in H1. tauto.
      subst t0 t1. specialize un_is_unrestricted with out t. intros.
      apply H3 in H1. tauto.
      intros.
      inversion H. destruct H1 as [H2 H3].
      inversion H0.
      subst t0 t1. specialize un_is_unrestricted with empty t. intros.
      apply H3 in H1. tauto.
      subst t0 t1. specialize un_is_unrestricted with empty t. intros.
      apply H3 in H1. tauto.
  Qed.

  Lemma type_remove_un_2 : forall t t1 t2,
      ((((t1 = (Chan un io t) \/ t1 = (Chan un inp t) \/
          t1 = (Chan un out t) \/ t1 = (Chan un empty t)) /\ t2 = (Chan un io t)))
       -> type_remove (Chan un io t) t1 t2) /\
      ((((t1 = (Chan un inp t) \/ t1 = (Chan un empty t)) /\ t2 = (Chan un inp t)))
       -> (type_remove (Chan un inp t) t1 t2)) /\
      ((((t1 = (Chan un out t) \/ t1 = (Chan un empty t)) /\ t2 = (Chan un out t)))
       -> type_remove (Chan un out t) t1 t2) /\
      (((t1 = (Chan un out t) \/ t1 = (Chan un empty t)) /\ t2 = (Chan un out t)) -> type_remove (Chan un out t) t1 t2)  /\
      (((t1 = (Chan un empty t) /\ t2 = (Chan un empty t)))
       -> type_remove (Chan un empty t) t1 t2).
  Proof.
    intros. split. 
    - intro. intuition.
      + subst t1 t2. unfold type_remove. split. 
        * apply Ts_id.
        * split. apply Tp_UnPlus. intro. tauto. 
      + subst t1 t2. unfold type_remove. split. 
        * apply Ts_inp.
        * split. assert (pol_cup inp io = io) by auto.
          rewrite <-H at 2. 
          apply Tp_UnPlus. intro. tauto. 
      + subst t1 t2. unfold type_remove. split. 
        * apply Ts_out.
        * split. assert (pol_cup out io = io) by auto.
          rewrite <-H at 2. 
          apply Tp_UnPlus. intro. tauto.
      + subst t1 t2. unfold type_remove. split. 
        * apply Ts_empty.
        * split. assert (pol_cup empty io = io) by auto.
          rewrite <-H at 2. 
          apply Tp_UnPlus. intro. tauto.       
    -  split. intro. intuition.
       + subst t1 t2. unfold type_remove. split. 
         * apply Ts_id.
         * split. apply Tp_UnPlus. intro. tauto. 
       + subst t1 t2. unfold type_remove. split. 
         * apply Ts_empty.
         * split. assert (pol_cup empty inp = inp) by auto.
           rewrite <-H at 2. 
           apply Tp_UnPlus. intro. tauto.  
       + split. intros. intuition. subst t1 t2. unfold type_remove. split. 
         * apply Ts_id.
         * split. assert (pol_cup out out = out) by auto.
           rewrite <-H at 2. 
           apply Tp_UnPlus. intro. tauto.
         * subst t1 t2. unfold type_remove. split. 
           apply Ts_empty.
           split. assert (pol_cup empty out = out) by auto.
           rewrite <-H at 2. 
           apply Tp_UnPlus. intro. tauto.
         * intros. intuition. subst t1 t2.
           unfold type_remove. split. apply Ts_id. 
           split. assert (pol_cup out out = out) by auto.
           rewrite <-H at 2. 
           apply Tp_UnPlus. intro. tauto.
           subst t1 t2.
           unfold type_remove. split. apply Ts_empty. 
           split. assert (pol_cup empty out = out) by auto.
           rewrite <-H at 2. 
           apply Tp_UnPlus. intro. tauto.
           subst t1 t2.
           unfold type_remove. split. apply Ts_empty. 
           split. assert (pol_cup empty empty = empty) by auto.
           rewrite <-H at 2. 
           apply Tp_UnPlus. intro. tauto.
  Qed.
  
  Inductive flag_plus : flag -> flag -> flag -> Prop :=
  | Fp_hi : flag_plus hid ill hid
  | Fp_ih : flag_plus ill hid hid
  | Fp_vv : flag_plus vis vis vis
  | Fp_ii : flag_plus ill ill ill.

  Inductive tEnv_split (g1 : typeEnv) (g2 : typeEnv) (g3 : typeEnv)
            (pf1 : isMap g1) (pf2 : isMap g2) (pf3 : isMap g3) : Prop :=
  | SpNil : g1 = nil -> g2 = nil -> g3 = nil ->
            tEnv_split g1 g2 g3 pf1 pf2 pf3
  | SpLin : forall n f f' g p q p' t g''' pf' pf'' pf''',
      flag_plus f g f'->
      pol_plus p q p' ->
      In (n, f, Chan lin p t) g1 ->
      In (n, g, Chan lin q t) g2 ->
      tEnv_split (removeEntry n g1) (removeEntry n g2) g''' pf' pf'' pf''' ->
      removeEntry n g3 = g''' ->
      flagOf g3 n f' ->
      typeOf g3 n (Chan lin p' t) ->
      tEnv_split g1 g2 g3 pf1 pf2 pf3
  | SpUn : forall n f f' g p t g''' pf' pf'' pf''',
      flag_plus f g f'->
      In (n, f, Chan un p t) g1 ->
      In (n, g, Chan un p t) g2 ->
      tEnv_split (removeEntry n g1) (removeEntry n g2) g''' pf' pf'' pf''' ->
      removeEntry n g3 = g''' ->
      flagOf g3 n f' ->
      typeOf g3 n (Chan un p t) ->
      tEnv_split g1 g2 g3 pf1 pf2 pf3
  | SpTop :  forall n f f' g g''' pf' pf'' pf''',
      flag_plus f g f'->
      In (n, f, Top) g1 ->
      In (n, g, Top) g2 ->
      tEnv_split (removeEntry n g1) (removeEntry n g2) g''' pf' pf'' pf''' ->
      removeEntry n g3 = g''' ->
      flagOf g3 n f' ->
      typeOf g3 n Top ->
      tEnv_split g1 g2 g3 pf1 pf2 pf3.
  
  
  Fixpoint domain (g: typeEnv) : list (nat * nat) :=
    match g with
    | (x, _, _) :: t => x :: domain t
    | nil => nil
    end.

  Fixpoint hid_proj (g : typeEnv) : typeEnv:=
    match g with
    | nil => nil
    | (a1, a2, hid, t) :: m =>
      (a1, a2, hid, t) :: hid_proj m
    |  (a1, a2, f, t) :: m =>
       hid_proj m
    end.

  Fixpoint vis_proj (g : typeEnv) : typeEnv:=
    match g with
    | nil => nil
    | (a1, a2, vis, t) :: m =>
      (a1, a2, vis, t) :: vis_proj m
    |  (a1, a2, f, t) :: m =>
       vis_proj m
    end.

  Fixpoint ill_proj (g : typeEnv) : typeEnv:=
    match g with
    | nil => nil
    | (a1, a2, ill, t) :: m =>
      (a1, a2, ill, t) :: ill_proj m
    |  (a1, a2, f, t) :: m =>
       ill_proj m
    end.

  
End TypeSystem.
