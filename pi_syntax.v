Require Import
        Bool List Omega PeanoNat
        ListAddOns
        header operations.

Require Import CpdtTactics LibTactics.

(**************** Static System ************************)

Notation name  := nat.

Section ProcessDefinitions.


  Inductive dproc : Set := 
  | dZero : dproc
  | dBang : name -> name -> name -> name ->dproc -> dproc
  | dPar : dproc -> dproc -> dproc 
  | dNu : name -> name -> dproc -> dproc 
  | dInp : name -> name -> name -> name -> dproc -> dproc
  | dOut : name -> name -> name -> name -> dproc -> dproc.
  
  Fixpoint secLabs (p : dproc)  :=
    match p with 
    | dZero  => nil
    | dBang _ _ _ _ p | dInp _ _ _ _ p | dOut _ _ _ _ p => secLabs p
    | dPar p q => secLabs q ++ secLabs p 
    | dNu h i  p =>  secLabs p ++ (h, i) :: nil
    end.

  Fixpoint fn (p : dproc) : list (nat * nat) :=
    match p with
    | dZero  => nil
    | dBang x1 x2 y1 y2 p
    | dInp x1 x2 y1 y2  p =>
      List.remove nat_pair_eq_dec (y1, y2) ((x1, x2) :: fn p) 
    | dPar p1 p2 =>
      fn p1 ++  fn p2 
    | dNu a1 a2 p =>
      List.remove nat_pair_eq_dec (a1, a2) (fn p) 
    | dOut x1 x2 y1 y2 p =>
      (x1, x2) :: (y1, y2) :: fn p
    end.

  Fixpoint bv (p : dproc) : list (nat * nat) :=
    match p with
    | dZero  =>
      nil
    | dBang x1 x2 y1 y2 p
    | dInp x1 x2 y1 y2  p =>
      (y1, y2) :: bv p
    | dPar p1 p2 =>
      bv p1 ++  bv p2 
    | dNu a1 a2 p =>
      bv p
    | dOut x1 x2 y1 y2 p =>
      bv p
    end.


  Definition wf (p : dproc) : Prop :=
    NoDup (secLabs p) /\ disjoint (fn p) (secLabs p).

  

  Definition pos l := forall x1 x2 : nat,
      In (x1, x2) l-> x2 > 0.

  
  Lemma pos_cons : forall a l,
      pos (a :: l) -> pos l.
  Proof with eauto.
    intros; destruct a; unfold pos in *; try inverts H; intros;
      try specialize H with (x1, x2); intuition;
        eapply H; try right...
  Qed.
  
  Lemma incl_pos: forall l1 l2,
      incl l1 l2 ->
      pos l2 ->
      pos l1.
  Proof with eauto.
    introv INCL POS; unfold incl, pos in *; intros;
      specialize INCL with (x1, x2); intuition...
  Qed.

  Lemma pos_remove: forall a1 a2 l,
      pos l ->
      pos (remove nat_pair_eq_dec  (a1, a2) l).
  Proof with eauto.
    introv POS; unfold pos; intros...
    try eapply in_remove in H; intuition...
  Qed.
  
  Definition sl_pos p := pos (secLabs p).

  Lemma sl_pos_par_l: forall p q,
      sl_pos (dPar p q) ->
      sl_pos p.
  Proof.
    intuition. unfold sl_pos in H. unfold pos in H.
    unfold secLabs in H. fold secLabs in H.
    unfold sl_pos; unfold pos.
    intuition. 
    specialize in_or_app with
        (l := secLabs q) (m := secLabs p) (a := (x1, x2))
      as IOA; eauto...
  Qed.

  Lemma sl_pos_par_r: forall p q,
      sl_pos (dPar p q) ->
      sl_pos q.
  Proof.
    intuition. unfold sl_pos in H. unfold pos in H.
    unfold secLabs in H. fold secLabs in H.
    unfold sl_pos; unfold pos.
    intuition. 
    specialize in_or_app with
        (l := secLabs q) (m := secLabs p) (a := (x1, x2))
      as IOA; eauto...
  Qed.

  Lemma sl_pos_inp: forall a1 a2 x1 x2 p,
      sl_pos (dInp a1 a2 x1 x2 p) -> sl_pos p.
  Proof with eauto.
    introv SLP. simpl in *...
  Qed.
  Lemma sl_pos_out: forall a1 a2 x1 x2 p,
      sl_pos (dOut a1 a2 x1 x2 p) -> sl_pos p.
  Proof with eauto.
    introv SLP. simpl in *...
  Qed.

  Lemma sl_pos_bang: forall a1 a2 x1 x2 p,
      sl_pos (dBang a1 a2 x1 x2 p) -> sl_pos p.
  Proof with eauto.
    introv SLP. simpl in *...
  Qed.

  
  Lemma sl_pos_nu : forall a1 a2 p,
      sl_pos (dNu a1 a2 p) -> sl_pos p.
  Proof with eauto.
    intros. 
    unfold sl_pos,pos in *; intros.
    specialize H with x1 x2; simpl in *.
    assert (In (x1, x2) (secLabs p ++ (a1, a2) :: nil)).
    eapply in_app_iff; left...
    intuition.
  Qed.


  Hint Resolve sl_pos_par_l sl_pos_par_r sl_pos_nu
       sl_pos_inp sl_pos_out sl_pos_bang.

  

  (* Substitution of free names *)
  Definition mv (py pz pv : name * name)  :=
    let (y1, y2) := (fst py, snd py) in
    let (z1, z2) := (fst pz, snd pz) in
    let (v1, v2) := (fst pv, snd pv) in
    if (y1 =? z1) && (y2 =? z2)
    then (v1, v2)
    else (y1, y2).

  Fixpoint pmap p z1 z2 v1 v2 :=
    match p with
    | dZero  =>  p
    | dBang x1 x2 y1 y2 q =>
      let r := mv (x1, x2) (z1, z2) (v1, v2) in
      dBang (fst r) (snd r) y1 y2 (pmap q z1 z2 v1 v2)
    | dInp x1 x2 y1 y2  q =>
      let r := mv (x1, x2) (z1, z2) (v1, v2) in
      dInp (fst r) (snd r) y1 y2  (pmap q z1 z2 v1 v2)
    | dOut x1 x2 y1 y2 p =>
      let r1 := mv (x1, x2) (z1, z2) (v1, v2) in
      let r2 := mv (y1, y2) (z1, z2) (v1, v2) in
      dOut  (fst r1) (snd r1) (fst r2) (snd r2) (pmap p z1 z2 v1 v2)
    | dPar p q =>
      dPar (pmap p z1 z2 v1 v2) (pmap q z1 z2 v1 v2)
    | dNu h i q =>
      dNu h i (pmap q z1 z2 v1 v2)
    end.

  (* Relabeling - version using a Dictionary *)
  (* Similar to Coq.FSets.FMapList, but simpler *)
  Definition map_nat_nat := list (nat * nat).
  
  Fixpoint  domain_projection (m : map_nat_nat) :=
    match m with
    | nil => nil
    | (k, _) :: t => k :: (domain_projection t)
    end.

  Fixpoint  codomain_projection (m : map_nat_nat) :=
    match m with
    | nil => nil
    | (_, v) :: t => v :: (codomain_projection t)
    end.

  Definition structure_is_map (m : map_nat_nat) := 
    NoDup (domain_projection m).

  Fixpoint max (l :list (nat*nat)) : nat :=
    match l with 
    | nil => 0
    | (_, x) :: t => let m := max t in
                     if x <? m then m else x
    end.

  (* Dependent relabeling *)
  Notation dp := domain_projection.
  Notation cp := codomain_projection.

  Lemma dp_cons : forall  (x y : nat) (t : list (nat*nat)),
      dp ((x, y) :: t) = x :: (dp t).
  Proof.
    intros. unfold dp at 1. fold dp. tauto.
  Qed.

  Lemma cp_cons : forall  (x y : nat) (t : list (nat*nat)),
      cp ((x, y) :: t) = y :: (cp t).
  Proof.
    intros. unfold cp at 1. fold cp. tauto.
  Qed.
  
  Theorem no_dup_cont : forall  (h : nat*nat) (t : list (nat*nat)),
      NoDup (h ::t) -> NoDup t.
  Proof.
    intros. assert (S := surjective_pairing).
    specialize S with name name h.
    rewrite S in H. apply NoDup_cons_iff in H. intuition.
  Qed.
  
  Fixpoint dep_map_gen_r (l :list (name * name)) (m : nat) : NoDup l -> map_nat_nat :=
    match l with
    | nil => fun _ => nil
    | h :: t =>
      fun pf : NoDup (h :: t)  =>
        (fst h, snd h + m) :: (dep_map_gen_r t m (no_dup_cont h t pf))
    end.

  Definition dep_map_gen (l :list (name * name)) : NoDup l -> map_nat_nat :=
    dep_map_gen_r l (max l).


  Fixpoint dep_relabel (p : dproc) (s : list (name*name)) : NoDup s -> dproc :=
    match p with 
    | dZero   => fun _  => p
    | dBang x1 x2 y1 y2 p  =>
      fun pf : NoDup s => dBang  x1 x2 y1 y2 (dep_relabel p s pf)
    | dInp x1 x2 y1 y2 p =>
      fun pf : NoDup  s => dInp  x1 x2 y1 y2 (dep_relabel p s pf)
    | dOut x1 x2 y1 y2 p  =>
      fun pf : NoDup s => dOut x1 x2 y1 y2  (dep_relabel p s pf )
    | dPar p q =>
      fun pf : NoDup s =>
        dPar (dep_relabel p s pf) (dep_relabel q s pf)
    | dNu h i p =>
      fun pf : NoDup s =>
        dNu h (i + max s) (pmap (dep_relabel p s pf) h i h (i + max s))  
    end.
  
(*Fixpoint subProc (p : dproc) : list dproc :=  
    match p with 
    | dZero => nil
    | dBang x1 x2 y1 y2 p => (dBang x1 x2 y1 y2 p) :: (subProc p)  
    | dInp x1 x2 y1 y2  p => (dInp x1 x2 y1 y2 p) :: (subProc p) 
    | dOut x1 x2 y1 y2  p => (dOut x1 x2 y1 y2 p) :: (subProc p) 
    | dPar p q =>  (subProc p) ++ (subProc q)  
    | dNu h i p => (dNu h i p) :: (subProc p) 
    end.
 *)
End ProcessDefinitions.


(****************** Facts about the static system ***********************)

Section Facts.

  

  Lemma wf_rewrite : forall p,
      wf p -> NoDup (secLabs p).
  Proof.
    introv; unfold wf in *;
    destruct p; simpl; auto; intuition.
  Qed.

  Lemma disjoint_remove A eq_dec (x : A) l1 l2 l3:
    disjoint (List.remove eq_dec x l1) (l2 ++l3) ->
    ~In x l2 ->
    disjoint l1 l2.
  Proof with eauto.
    introv DIS NIN.
    induction l1...
    case_eq (eq_dec x a); introv EQ; subst; simpl in *; rewrite EQ in *; intuition.
    eapply disjoint_l_cons in DIS; intuition.
    eapply IHl1...
    eapply disjoint_l_cons in DIS; intuition.
  Qed.

  Hint Resolve in_eq.

  Lemma disjoint_absurd {A}: forall x (l m : list A) P,
    disjoint l m  -> In x l -> In x m -> P.
Proof with eauto.
  intros. apply ex_falso.
  eapply in_split in H0 as (l1 &l2 &ABS1).
  eapply in_split in H1 as (m1 &m2 &ABS2).
  subst. 
  eapply disjoint_app_r,disjoint_l_cons in H as [_ ABS].
  assert ( In x (m1 ++ x :: m2)).
  eapply in_app_iff; right...
  contradiction.
Qed.


  
  
  Lemma wf_par : forall p q,
      wf(dPar p q) -> wf p /\ wf q.
  Proof with eauto.
    intros. unfold wf in H. unfold secLabs in H. fold secLabs in H.
    intuition.
    apply no_dup_distr in H0. destruct H0 as [H2 H3].
    unfold wf; split...
    simpl in H1.
    eapply disjoint_app_l,disjoint_commute,disjoint_app_r,disjoint_commute in H1...
    simpl in H0; eapply no_dup_iff in H0; intuition; split...
    simpl in H1.
    eapply disjoint_app_r,disjoint_commute,disjoint_app_l,disjoint_commute in H1...
  Qed.

  Lemma wf_res : forall h i p,
      wf(dNu h i p) -> wf p.
  Proof with eauto.
    intros. unfold wf in H. unfold secLabs in H. fold secLabs in H.
    intuition.
    assert (ND  := H0).
    apply no_dup_distr in H0. destruct H0 as [H2 H3].
    unfold wf; split...
    simpl in H1; eapply disjoint_remove; try introv ABS...
    eapply no_dup_iff in ND; intuition;
    eapply disjoint_absurd...
  Qed.

(*
  Lemma wf_bang : forall x1 x2 y1 y2 p,
      wf(dBang x1 x2 y1 y2 p) -> wf p.
  Proof.
    intros. unfold wf in H. unfold secLabs in H. fold secLabs in H.
    apply rewrite_wf in H. tauto.
  Qed.

  Lemma wf_inp : forall x1 x2 y1 y2 p,
      wf(dInp x1 x2 y1 y2 p) -> wf p.
  Proof.
    intros. unfold wf in H. unfold secLabs in H. fold secLabs in H.
    apply rewrite_wf in H. tauto.
  Qed.
*)


End Facts.
