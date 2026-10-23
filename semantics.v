Require Import
        Bool List Lia PeanoNat
        header operations pi_syntax 
        pairEq type_system.

Require Import CpdtTactics LibTactics.


(********************** Semantics ****************************)
Section Semantics.

  
  
  


  Lemma bv_pmap  p n1 n2 n3 n4 :
    bv (pmap p n1 n2 n3 n4) = bv p.
  Proof with eauto.
    induction p; simpl;
      try rewrite IHp;
      try rewrite IHp1;
      try rewrite IHp2...
  Qed.  

  Lemma bv_dep_relabel: forall p g nd_pf,
      bv (dep_relabel p (domain g) nd_pf) = bv p.
  Proof with eauto using bv_pmap.
    intros; induction p; simpl;
      try rewrite IHp;
      try rewrite IHp1;try rewrite IHp2...
    rewrite <-IHp...
  Qed.
  
  Inductive action : Set :=
  | aIn : nat -> nat -> nat -> nat -> action
  | aOut : nat -> nat -> nat -> nat -> action
  | aTau : nat -> nat -> action.


  Fixpoint InB a g : ((flag * piType) * bool) :=
    match g with
    | nil => ((ill, Top), false) (* Never used *)
    | (b, f, t) :: m =>
      if pair_eq a b then ((f, t), true) else InB a m
    end.

  Lemma inB_implies_In_2 : forall a g p,
      InB a g = (p, true) ->
      In (a, fst p, snd p) g.
  Proof with eauto.
    introv INB; induction g; simpl in *;
      try inv INB;
      try destruct a0 as [[[a1 a2] f]t];
      case_eq (pair_eq a (a1,a2)); intros PEQ;
        try rewrite <-pairEq_eq in PEQ; subst;
          try rewrite pairEq_eq_true in *;
          inv H0;
          try rewrite PEQ in *...
  Qed.

  
  Lemma  inB_removeEntry: forall a1 a2 b1 b2 f1 t1 g1,
      (a1, a2) <> (b1, b2) ->
      InB (a1, a2) ((b1, b2, f1, t1) :: removeEntry (b1, b2) g1) = InB (a1, a2) g1.
  Proof with eauto.
    intros.  simpl. rewrite pairEq_neq in H. rewrite H.
    induction g1...
    destruct a as (((c1 & c2) &f) &t).
    case_eq (pair_eq (c1, c2) (b1, b2)). intros EQ. rewrite <-pairEq_eq in EQ; inversion EQ; subst.
    unfold removeEntry; fold removeEntry; rewrite pairEq_eq_true.
    simpl. rewrite H...
    intros NEQ.  unfold removeEntry; fold removeEntry; rewrite NEQ.
    case_eq (pair_eq (a1, a2) (c1, c2)). intros EQ. rewrite <-pairEq_eq in EQ; inversion EQ; subst.
    simpl; rewrite pairEq_eq_true...
    intros NEQ2; simpl; rewrite NEQ2...
  Qed.
  
  Fixpoint newEntries (g : typeEnv) (l : list (name * name)) (max : nat) : typeEnv :=
    match l with
    | (a1, a2) :: tail =>
      let (_, notNew) := InB (a1, a2) g in
      if notNew
      then newEntries g tail max
      else
        let (pair, _) := InB (a1, a2 - max) g in
        ((a1, a2), fst pair, snd pair) :: newEntries g tail max
    | nil => nil
    end.

  Definition notHidden c1 c2 act :=
    match act with
    | aIn a1 a2 b1 b2
    | aOut a1 a2 b1 b2 =>
      (a1, a2)<> (c1, c2) /\ (b1, b2) <> (c1, c2)
    | aTau _ _ => True
    end.

  
  
  (* The distinction among names and variables is enforced in the input rules *)
  (** Right rules are omitted *)
  Inductive lts (g : typeEnv) :
    dproc ->  action -> typeEnv -> dproc -> NoDup (domain g) -> Prop :=
  | parL : forall p1 a g' q p2 pf,
      lts g p1 a g' p2 pf ->
      lts g (dPar p1 q) a g' (dPar p2 q) pf
  | lOut : forall p a1 a2 b1 b2 pf t t1 t2,
      type_remove t1 t t2 ->
      In ((a1, a2), vis, Chan lin out t) g ->
      In ((b1, b2), vis, t1) g ->
      lts g (dOut a1 a2 b1 b2 p) (aOut a1 a2 b1 b2)
          (((a1, a2), vis, Chan lin empty t)
             :: ((b1, b2), vis, t2)
             :: (removeEntry (a1, a2) (removeEntry (b1, b2) g))) p pf
  | uOut : forall pol p a1 a2 b1 b2 pf t t1 t2,
      pol = out \/ pol = io ->
      type_remove t1 t t2 ->
      In ((a1, a2), vis, Chan un pol t) g ->
      In ((b1, b2), vis, t1) g ->
      lts g (dOut a1 a2 b1 b2 p) (aOut a1 a2 b1 b2)
          (((b1, b2), vis, t2) :: removeEntry (b1, b2) g) p pf
  | lIn : forall p a1 a2 x1 x2 b1 b2 pf f t t1 t2,
      type_plus t1 t t2->
      f <> hid ->
      In ((a1, a2), vis, Chan lin inp t) g ->
      In ((b1, b2), f, t1) g ->
      lts g (dInp a1 a2 x1 x2 p) (aIn a1 a2 b1 b2)
          (((a1, a2), vis, Chan lin empty t)
             :: ((b1, b2), vis, t2)
             :: (removeEntry (a1, a2) (removeEntry (b1, b2) g)))
          (pmap p x1 x2 b1 b2) pf
  | uIn : forall pol p a1 a2 x1 x2 b1 b2 pf f t t1 t2,
      pol = inp \/ pol = io ->
      type_plus t1 t t2 ->
      f <> hid ->
      In ((a1, a2), vis, Chan un pol t) g ->
      In ((b1, b2), f, t1) g ->
      lts g (dInp a1 a2 x1 x2 p) (aIn a1 a2 b1 b2)
          (((b1, b2), vis, t2) :: removeEntry (b1, b2) g) 
          (pmap p x1 x2 b1 b2) pf
  | uRin : forall pol p a1 a2 x1 x2 b1 b2 pf f t t1 t2,
      pol = inp \/ pol = io ->
      type_plus t1 t t2 ->
      f <> hid ->
      In ((a1, a2), vis, Chan un pol t) g ->
      In ((b1, b2), f, t1) g ->
      let q := dep_relabel p (domain g) pf in
      lts g (dBang a1 a2 x1 x2 p) (aIn a1 a2 b1 b2)
          ((newEntries g (secLabs q) (max (domain g)))
             ++ (((b1, b2), vis, t2) :: removeEntry (b1, b2) g))
          (dPar (pmap p x1 x2 b1 b2) (dBang a1 a2 x1 x2 q)) pf
  | lcomL : forall p1 p2 q1 q2 a1 a2 b1 b2 s s1 t
                   pf pf1 pf2,
      let g0 := removeEntry (a1, a2) (removeEntry (b1, b2) g) in
      type_remove s t s1 ->
      In ((a1, a2), vis, Chan lin io t) g ->
      In ((b1, b2), vis, s) g ->
      lts
        (((a1, a2), vis, Chan lin out t)
           :: ((b1, b2), vis, s)
           :: g0)
        p1
        (aOut a1 a2 b1 b2)
        (((a1, a2), vis, Chan lin empty t)
           :: ((b1, b2), vis, s1)
           :: g0)
        p2
        pf1 ->
      lts
        (((a1, a2), vis, Chan lin inp t)
           :: ((b1, b2), vis, s1)
           :: g0)
        q1
        (aIn a1 a2 b1 b2)
        (((a1, a2), vis, Chan lin empty t)
           :: ((b1, b2), vis, s)
           :: g0)
        q2
        pf2 ->
      lts g (dPar p1 q1) (aTau a1 a2)
          (((a1, a2), vis, Chan lin empty t)
             :: ((b1, b2), vis, s)
             :: g0) (dPar p2 q2) pf
  | lclsL : forall p1 p2 q1 q2 a1 a2 b1 b2 s s1 t
                   pf pf1 pf2,
      let g0 := removeEntry (a1, a2) (removeEntry (b1, b2) g) in
      let g3 := (((a1, a2), vis, Chan lin empty t)
                   :: ((b1, b2), hid, s)
                   :: g0) in
      type_remove s t s1 ->
      In ((a1, a2), vis, Chan lin io t) g ->
      In ((b1, b2), hid, s) g ->
      lts
        (((a1, a2), vis, Chan lin out t)
           :: ((b1, b2), hid, s)
           :: g0)
        p1
        (aOut a1 a2 b1 b2)
        (((a1, a2), vis, Chan lin empty t)
           :: ((b1, b2), vis, s1)
           :: g0)
        p2
        pf1 ->
      lts
        (((a1, a2), vis, Chan lin inp t)
           :: ((b1, b2), ill, s1)
           :: g0)
        q1
        (aIn a1 a2 b1 b2)
        (((a1, a2), vis, Chan lin empty t)
           :: ((b1, b2), vis, s)
           :: g0)
        q2
        pf2 ->
      lts g (dPar p1 q1) (aTau a1 a2) g3 (dNu b1 b2 (dPar p2 q2)) pf
  | ucomL : forall g3 p1 p2 q1 q2 a1 a2 b1 b2 s s1 t
                   pf pf1 pf2,
      let g0 := removeEntry (b1, b2) g in
      let g' := ((b1, b2), vis, s1) :: g0 in
      type_remove s t s1 ->
      In ((a1, a2), vis, Chan un io t) g ->
      In ((b1, b2), vis, s) g ->
      lts
        g
        p1
        (aOut a1 a2 b1 b2)
        (((b1, b2), vis, s1) :: g0)
        p2
        pf1 ->
      lts
        g'
        q1
        (aIn a1 a2 b1 b2)
        g3
        q2
        pf2 ->
      In ((a1, a2), vis, Chan un io t) g3 ->
      In ((b1, b2), vis, s) g3 ->
      lts g (dPar p1 q1) (aTau a1 a2) g3 (dPar p2 q2) pf
  | uclsL : forall g3 p1 p2 q1 q2 a1 a2 b1 b2 s s1 t
                   pf pf1 pf2,
      let g0 := removeEntry (b1, b2) g in
      let g' := ((b1, b2), ill, s1) :: g0 in
      type_remove s t s1 ->
      In ((a1, a2), vis, Chan un io t) g ->
      In ((b1, b2), hid, s) g ->
      lts
        g
        p1
        (aOut a1 a2 b1 b2)
        (((b1, b2), vis, s1) :: g0)
        p2
        pf1 ->
      lts
        g'
        q1
        (aIn a1 a2 b1 b2)
        g3
        q2
        pf2 ->
      In ((a1, a2), vis, Chan un io t) g3 ->
      In ((b1, b2), vis, s) g3 ->
      lts g (dPar p1 q1) (aTau a1 a2)
          (((b1, b2), hid, s) :: removeEntry (b1, b2) g3)
          (dNu b1 b2 (dPar p2 q2)) pf
  | open : forall p a1 a2 b1 b2 g' p' t pf pf1,
      In ((b1, b2), hid, t) g ->
      lts (((b1, b2), vis, t) :: removeEntry (b1, b2) g)
          p (aOut a1 a2 b1 b2)
          g' p' pf1 ->
      lts g (dNu b1 b2 p)
          (aOut a1 a2 b1 b2)
          g' p' pf
  | hide : forall b1 b2 t p a  h1 h2 h' h'' t' p' pf pf1,
      lts (h1 ++ (b1, b2, vis, t) :: h2) p a
          (h' ++ (b1, b2, vis, t') :: h'') p' pf1 ->
      notHidden b1 b2 a ->
      g = h1 ++ (b1, b2, hid, t) :: h2 ->
      lts g (dNu b1 b2 p) a (h' ++ (b1, b2, hid, t') :: h'') (dNu b1 b2 p') pf.


(*Theorem app_eq_app X (x1 x2 y1 y2: list X) : x1++x2 = y1++y2 ->
                                             exists l, (x1 = y1++l /\ y2 = l++x2) \/ (y1 = x1++l /\ x2 = l++y2).
Proof.
  revert y1. induction x1 as [|a x1 IH].
  - cbn. intros y1 ->. exists y1. now right.
  - intros [|b y1]; cbn.
    + intros <-. exists (a :: x1). now left.
    + intros [=-> [l Hl] %IH]. exists l.
      now destruct Hl as [[-> ->]|[-> ->]]; [left|right].
Qed.

  Example test_hide a a1 a2 x1 x2 b1 b2 c1 c2 g g1 (pf1 : NoDup(domain g1)) g2 pf k1 p p1 q:
    g1 = (a1, a2, vis, Chan lin inp Top)
           :: (b1, b2, vis, Top) :: (c1, c2, vis, Top) :: g2 ->
    a1 = 1 -> a2 =2 -> b1 = 3 -> b2 = 4 -> c1 = 5 -> c2 = 6->
    a = aIn a1 a2 b1 b2 ->
    g = (turnHid c1 c2 g1) ->
    p = dInp a1 a2 x1 x2 p1 ->
    q = pmap p1 x1 x2 b1 b2 ->
    k1 = (a1, a2, vis, Chan lin empty Top)
          :: (b1, b2, vis, Top) :: (c1, c2, vis, Top) :: g2 ->
    lts g (dNu c1 c2 p) a (turnHid c1 c2 k1)
        (dNu c1 c2 q) pf.  
  Proof with eauto.
    intros.
    eapply hide with (pf1 := pf1)(t := Top)...
    subst g1; right; right; left...
    subst p a.
    assert (k1 =
            (((a1, a2), vis, Chan lin empty Top)
             :: ((b1, b2), vis, Top)
             :: (removeEntry (a1, a2) (removeEntry (b1, b2) g1)))).
    subst k1 g1; subst; repeat simpl...
    rewrite H6,H9; eapply lIn with (f := vis) (t1 := Top);
      try eapply   Tp_Base;
      try discriminate;
      subst g1...
    left...
    right...
    left...

    intros. subst a; inversion H11; subst a0 a3 c0 c3.
    subst k1.
    intuition.
    eapply app_eq_app with (x1 := (a1, a2, vis, Chan lin empty Top) :: (b1, b2, vis, Top) :: nil) in H6 as (m &ABS); intuition.
    rewrite H in H13; rewrite H0,H1,H2,H3,H4,H5 in H13; unfold pair_eq in H13; simpl in H13.
    eapply app_inv_tail with (l1 := (3, 4, vis, t) :: (1, 2, vis, Chan lin inp Top) :: nil) in H13;
      rewrite <-H13 in H10;
      repeat rewrite <-H0,<-H1,<-H2,<-H3,<-H4,<-H5
        in H10.    
    assert (ABS:
              ((a1, a2, vis, Chan lin empty Top) :: nil) ++ (b1, b2, vis, Top) :: nil =
              (newEntries g1 l (max (domain g1)) ++ (3, 4, vis, t) :: nil) ++ (1, 2, vis, Chan lin inp Top) :: nil).
    erewrite <-app_assoc...
    eapply app_inj_tail in ABS as (_&ABS).
    inversion ABS...

    destruct m; inversion H13.
    subst; try discriminate...
    subst p0; clear H13.
    

    subst; compute...
    intuition; inversion H.
Qed.
 *)
  
  (* RIGHT RULES OMITTED *)
(* | parR : forall p1 a g' q p2 pf,
      lts g p1 a g' p2 pf ->
      lts g (dPar q p1) a g' (dPar q p2) pf
  | lcomR : forall g1 g2 p1 p2 q1 q2 a1 a2 b1 b2 s s1 t
                   pf pf1 pf2,
      let g0 := removeEntry (a1, a2) (removeEntry (b1, b2) g) in
      let g3 := (((a1, a2), vis, Chan lin empty t)
                   :: ((b1, b2), vis, s)
                   :: g2) in
      type_remove s t s1 ->
      In ((a1, a2), vis, Chan lin io t) g ->
      In ((b1, b2), vis, s) g ->
      lts
        (((a1, a2), vis, Chan lin out t)
           :: ((b1, b2), vis, s)
           :: g0)
        p1
        (aOut a1 a2 b1 b2)
        g1
        p2
        pf1 ->
      lts
        (((a1, a2), vis, Chan lin inp t)
           :: ((b1, b2), vis, s1)
           :: g0)
        q1
        (aIn a1 a2 b1 b2)
        g3
        q2
        pf2 ->
      lts g (dPar q1 p1) (aTau a1 a2) g3 (dPar q2 p2) pf
  | lclsR : forall g1 g2 p1 p2 q1 q2 a1 a2 b1 b2 s s1 t
                   pf pf1 pf2,
      let g0 := removeEntry (a1, a2) (removeEntry (b1, b2) g) in
      let g3 := (((a1, a2), vis, Chan lin empty t)
                   :: ((b1, b2), hid, s)
                   :: g2) in
      type_remove s t s1 ->
      In ((a1, a2), vis, Chan lin io t) g ->
      In ((b1, b2), hid, s) g ->
      lts
        (((a1, a2), vis, Chan lin out t)
           :: ((b1, b2), hid, t)
           :: g0)
        p1
        (aOut a1 a2 b1 b2)
        g1
        p2
        pf1 ->
      lts
        (((a1, a2), vis, Chan lin inp t)
           :: ((b1, b2), ill, s1)
           :: g0)
        q1
        (aIn a1 a2 b1 b2)
        g3
        q2
        pf2 ->
      lts g (dPar q1 p1) (aTau a1 a2) g3 (dNu b1 b2 (dPar q2 p2)) pf
  | ucomR : forall g1 g3 p1 p2 q1 q2 a1 a2 b1 b2 s s1 t
                   pf pf1 pf2,
      let g0 := removeEntry (b1, b2) g in
      let g' := ((b1, b2), vis, s1) :: g0 in
      type_remove s t s1 ->
      In ((a1, a2), vis, Chan un io t) g ->
      In ((b1, b2), vis, s) g ->
      lts
        g
        p1
        (aOut a1 a2 b1 b2)
        g1
        p2
        pf1 ->
      lts
        g'
        q1
        (aIn a1 a2 b1 b2)
        g3
        q2
        pf2 ->
      In ((a1, a2), vis, Chan un io t) g3 ->
      In ((b1, b2), vis, s) g3 ->
      lts g (dPar q1 p1) (aTau a1 a2) g3 (dPar q2 p2) pf
  | uclsR : forall g1 g3 mode p1 p2 q1 q2 a1 a2 b1 b2 s s1 t
                   pf pf1 pf2,
      let g0 := removeEntry (b1, b2) g in
      let g' := ((b1, b2), ill, s1) :: g0 in
      type_remove s t s1 ->
      In ((a1, a2), vis, Chan mode io t) g ->
      In ((b1, b2), hid, s) g ->
      lts
        g
        p1
        (aOut a1 a2 b1 b2)
        g1
        p2
        pf1 ->
      lts
        g'
        q1
        (aIn a1 a2 b1 b2)
        g3
        q2
        pf2 ->
      In ((a1, a2), vis, Chan un io t) g3 ->
      In ((b1, b2), hid, s) g3 ->
      lts g (dPar q1 p1) (aTau a1 a2) g3 (dNu b1 b2 (dPar q2 p2)) pf.*)


End Semantics.

Parameter nonRecTypes:
  (forall m p t,
      t = Chan m p t -> False) /\
  (forall m m1 m2 p p1 p2 t,
      Chan m1 p1 t = Chan m p (Chan m2 p2 t) ->
      False).



