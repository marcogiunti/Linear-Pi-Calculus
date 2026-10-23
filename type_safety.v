From Stdlib Require Import
  Lia
  List
  Program.Equality
  Relations
  ProofIrrelevance.

Require Import
  header
  operations
  ListAddOns
  Domain
  RemoveEntry
  pi_syntax
  type_system
  type_system_rules
  semantics
  linear_pi
  sne_premises
  pairEq
  lts_no_dup
  type_checking_1
  proposition27
  type_operations_1
  LibTactics.

Import List.ListNotations.

(* Channels (as name pairs) used in input / replicated-input position. *)
Fixpoint input_channels (p : dproc) : list (name * name) :=
  match p with
  | dBang x1 x2 _ _ _
  | dInp x1 x2 _ _ _ =>
      [(x1, x2)]
  | dNu _ _ p =>
      input_channels p
  | dPar p q =>
      input_channels p ++ input_channels q
  | _ =>
      []
  end.

(* Channels (as name pairs) used in output position. *)
Fixpoint output_channels (p : dproc) : list (name * name) :=
  match p with
  | dOut x1 x2 _ _ _ =>
      [(x1, x2)]
  | dNu _ _ p =>
      output_channels p
  | dPar p q =>
      output_channels p ++ output_channels q
  | _ =>
      []
  end.

(*
Definition error (g : typeEnv) (p : dproc) :=
  exists a pol t,
    In (Chan lin pol t) g /\ 
      count_occ a (input_channels p) > 1 \/
      count_occ a (output_channels p) > 1.
 *)

Definition notError (g : typeEnv) (p : dproc) :=
  forall a f t,
    (count_occ nat_pair_eq_dec (input_channels p) a > 1  \/
       count_occ nat_pair_eq_dec (output_channels p) a > 1) ->
    In (a, f, t) g ->
    is_unrestricted t.

(* Number of input (resp. output) prefixes on a channel that a linear
   polarity allows at top level. *)
Definition in_cap (q : pol) : nat :=
  match q with
  | inp | io => 1
  | _ => 0
  end.

Definition out_cap (q : pol) : nat :=
  match q with
  | out | io => 1
  | _ => 0
  end.

(* [n] top-level uses of a channel of type [t] respect capability [cap]:
   none for Top, at most [cap q] for a linear channel, and none for an
   unrestricted channel whose polarity forbids the action. *)
Definition count_ok (cap : pol -> nat) (t : piType) (n : nat) : Prop :=
  match t with
  | Top => n = 0
  | Chan lin q _ => n <= cap q
  | Chan un q _ => cap q = 0 -> n = 0
  end.

Lemma count_ok_zero : forall cap t,
    count_ok cap t 0.
Proof.
  intros cap t; destruct t as [[|] q s|]; simpl; auto; lia.
Qed.

Lemma count_ok_plus : forall cap t1 t2 t n1 n2,
    (cap = in_cap \/ cap = out_cap) ->
    type_plus t1 t2 t ->
    count_ok cap t1 n1 ->
    count_ok cap t2 n2 ->
    count_ok cap t (n1 + n2).
Proof.
  introv CAP TP C1 C2.
  inversion TP; subst; simpl in *.
  - lia.
  - match goal with H : pol_plus _ _ _ |- _ => inversion H end;
    subst; destruct CAP; subst; simpl in *; lia.
  - intros Z; destruct CAP; subst;
      destruct p1, p2; simpl in *;
      try discriminate; rewrite C1, C2 by reflexivity; reflexivity.
Qed.

(* Every entry of the result of a split is the type_plus of entries of
   the two components. *)
Lemma split_entry : forall g1 g2 g pf1 pf2 pf,
    tEnv_split g1 g2 g pf1 pf2 pf ->
    forall a f t,
      In (a, f, t) g ->
      exists f1 f2 t1 t2,
        In (a, f1, t1) g1 /\ In (a, f2, t2) g2 /\ type_plus t1 t2 t.
Proof.
  introv TS.
  induction TS; intros a f0 t0 IN.
  - subst; inversion IN.
  - destruct (nat_pair_eq_dec a n) as [EQ | NEQ].
    + subst.
      match goal with
        H : typeOf g3 n _ |- _ => inversion H; subst end.
      match goal with
        H : In (n, _, Chan lin p' t) g3 |- _ =>
          destruct (pf3 n f0 t0 _ _ (conj IN H)) as [_ EQT] end.
      subst; exists f g (Chan lin p t) (Chan lin q t).
      repeat split; auto; constructor; auto.
    + edestruct IHTS as (f1 & f2 & t1 & t2 & IN1 & IN2 & TP).
      { subst; apply removeEntry_in; eauto. }
      exists f1 f2 t1 t2.
      repeat split; eauto using in_removeEntry.
  - destruct (nat_pair_eq_dec a n) as [EQ | NEQ].
    + subst.
      match goal with
        H : typeOf g3 n _ |- _ => inversion H; subst end.
      match goal with
        H : In (n, _, Chan un p t) g3 |- _ =>
          destruct (pf3 n f0 t0 _ _ (conj IN H)) as [_ EQT] end.
      subst; exists f g (Chan un p t) (Chan un p t).
      repeat split; auto.
      rewrite <- (pol_cup_id p) at 3; constructor.
    + edestruct IHTS as (f1 & f2 & t1 & t2 & IN1 & IN2 & TP).
      { subst; apply removeEntry_in; eauto. }
      exists f1 f2 t1 t2.
      repeat split; eauto using in_removeEntry.
  - destruct (nat_pair_eq_dec a n) as [EQ | NEQ].
    + subst.
      match goal with
        H : typeOf g3 n _ |- _ => inversion H; subst end.
      match goal with
        H : In (n, _, Top) g3 |- _ =>
          destruct (pf3 n f0 t0 _ _ (conj IN H)) as [_ EQT] end.
      subst; exists f g Top Top.
      repeat split; auto; constructor.
    + edestruct IHTS as (f1 & f2 & t1 & t2 & IN1 & IN2 & TP).
      { subst; apply removeEntry_in; eauto. }
      exists f1 f2 t1 t2.
      repeat split; eauto using in_removeEntry.
Qed.

(* A single top-level prefix on [u], where [u] has polarity [q] in [g]. *)
Lemma count_ok_prefix : forall cap g (pf : isMap g) u f m q t a f0 t0,
    In (u, f, Chan m q t) g ->
    (m = lin -> cap q = 1) ->
    (m = un -> cap q <> 0) ->
    In (a, f0, t0) g ->
    count_ok cap t0 (count_occ nat_pair_eq_dec [u] a).
Proof.
  intros cap g pf u f m q t a f0 t0 IN LIN UN IN0; simpl.
  destruct (nat_pair_eq_dec u a) as [EQ | NEQ].
  - subst; destruct (pf a f0 t0 _ _ (conj IN0 IN)) as [_ EQT]; subst.
    destruct m; simpl.
    + rewrite LIN; auto.
    + intros Z; exfalso; apply UN; auto.
  - apply count_ok_zero.
Qed.

Lemma type_remove_inp : forall p t t1,
    type_remove (Chan lin p t) (Chan lin inp t) t1 ->
    in_cap p = 1.
Proof.
  introv [SUB _]; inversion SUB; subst; reflexivity.
Qed.

Lemma type_remove_out : forall p t t1,
    type_remove (Chan lin p t) (Chan lin out t) t1 ->
    out_cap p = 1.
Proof.
  introv [SUB _]; inversion SUB; subst; reflexivity.
Qed.

Lemma typeCheck_counts (g : typeEnv) (pf : isMap g) (p : dproc) :
  typeCheck g pf p ->
  forall a f t,
    In (a, f, t) g ->
    count_ok in_cap t (count_occ nat_pair_eq_dec (input_channels p) a) /\
      count_ok out_cap t (count_occ nat_pair_eq_dec (output_channels p) a).
Proof.
  intros TC.
  induction TC; intros a f0 t0 IN; simpl input_channels; simpl output_channels;
    try (destruct u as [u1 u2]; simpl fst; simpl snd).
  - split; apply count_ok_zero.
  - destruct (nat_pair_eq_dec a n) as [EQ | NEQ].
    + subst; destruct (pf n f0 t0 hid t (conj IN H)) as [_ EQT]; subst.
      apply IHTC with vis; left; reflexivity.
    + apply IHTC with f0; right; apply removeEntry_in; auto.
  - destruct (split_entry _ _ _ _ _ _ H _ _ _ IN)
      as (f1 & f2 & t1 & t2 & IN1 & IN2 & TP).
    destruct (IHTC1 _ _ _ IN1) as [I1 O1].
    destruct (IHTC2 _ _ _ IN2) as [I2 O2].
    rewrite !count_occ_app.
    split; eapply count_ok_plus; eauto.
  - split; [apply count_ok_zero |].
    eapply (count_ok_prefix _ g pf); [eassumption | | | exact IN]; intros; try discriminate.
    eapply type_remove_out; eauto.
  - split; [apply count_ok_zero |].
    eapply (count_ok_prefix _ g pf); [eassumption | | | exact IN]; intros; try discriminate.
    destruct H as [-> | ->]; simpl; discriminate.
  - split; [| apply count_ok_zero].
    eapply (count_ok_prefix _ g pf); [eassumption | | | exact IN]; intros; try discriminate.
    eapply type_remove_inp; eauto.
  - split; [| apply count_ok_zero].
    eapply (count_ok_prefix _ g pf); [eassumption | | | exact IN]; intros; try discriminate.
    destruct H as [-> | ->]; simpl; discriminate.
  - split; [| apply count_ok_zero].
    eapply (count_ok_prefix _ g pf); [eassumption | | | exact IN]; intros; try discriminate.
    destruct H as [-> | ->]; simpl; discriminate.
Qed.

Lemma type_soundness (g : typeEnv) (pf : isMap g) (p : dproc) :
  typeCheck g pf p->
  notError g p.
Proof.
  intros TC; unfold notError; intros a f t GT IN.
  destruct (typeCheck_counts _ _ _ TC _ _ _ IN) as [I O].
  destruct t as [[|] q s|]; simpl in *.
  - exfalso; destruct q; simpl in *; lia.
  - unfold is_unrestricted; eauto.
  - exfalso; lia.
Qed.




(* LTS transitions as a relation on configurations (g, p), indexed by
   the action. The NoDup (domain g) proof carried by lts is hidden. *)
Definition config : Set := (typeEnv * dproc)%type.

Definition lts_rel (act : action) (c c' : config) : Prop :=
  match c, c' with
  | (g, p), (g', p') =>
      exists pf : NoDup (domain g), lts g p act g' p' pf
  end.

Definition lts_rel_tau : relation config :=
  fun c c' => exists a1 a2, lts_rel (aTau a1 a2) c c'.


Definition wlts (c1 c2 : config) : Prop :=
  clos_refl_trans_1n config lts_rel_tau c1 c2.

(* sl_pos is preserved by transitions. *)
Lemma sl_pos_par_intro : forall p q,
    sl_pos p -> sl_pos q -> sl_pos (dPar p q).
Proof.
  unfold sl_pos, pos; simpl; intros p q SLP SLQ x1 x2 IN.
  apply List.in_app_or in IN; destruct IN; eauto.
Qed.

Lemma sl_pos_nu_intro : forall b1 b2 p,
    sl_pos p -> b2 > 0 -> sl_pos (dNu b1 b2 p).
Proof.
  unfold sl_pos, pos; simpl; intros b1 b2 p SLP POS x1 x2 IN.
  apply List.in_app_or in IN; destruct IN as [IN | [EQ | []]]; eauto.
  inversion EQ; subst; auto.
Qed.

Lemma sl_pos_nu_pos : forall b1 b2 p,
    sl_pos (dNu b1 b2 p) -> b2 > 0.
Proof.
  unfold sl_pos, pos; simpl; intros b1 b2 p SLP.
  apply (SLP b1); apply List.in_or_app; right; left; reflexivity.
Qed.

Lemma sl_pos_pmap : forall p x1 x2 v1 v2,
    sl_pos p -> sl_pos (pmap p x1 x2 v1 v2).
Proof.
  unfold sl_pos; intros; rewrite seclabs_of_pmap; auto.
Qed.

Lemma sl_pos_dep_relabel : forall p s pf,
    sl_pos p -> sl_pos (dep_relabel p s pf).
Proof.
  induction p; intros s pf SLP; simpl.
  - auto.
  - apply IHp; eauto using sl_pos_bang.
  - apply sl_pos_par_intro;
      [apply IHp1; eapply sl_pos_par_l | apply IHp2; eapply sl_pos_par_r]; eauto.
  - apply sl_pos_nu_intro.
    + apply sl_pos_pmap, IHp; eauto using sl_pos_nu.
    + apply sl_pos_nu_pos in SLP; lia.
  - apply IHp; eauto using sl_pos_inp.
  - apply IHp; eauto using sl_pos_out.
Qed.

(* A name that is hidden in g but output by p must be bound in p. *)
Lemma lts_out_hid_secLabs : forall g p a g' p' pf,
    lts g p a g' p' pf ->
    forall c1 c2 d1 d2 s,
      a = aOut c1 c2 d1 d2 ->
      In ((d1, d2), hid, s) g ->
      In (d1, d2) (secLabs p).
Proof.
  introv LTS.
  induction LTS; intros c1 c2 d1 d2 s0 EQA IN; try discriminate.
  - simpl; apply List.in_or_app; right; eauto.
  - inversion EQA; subst.
    destruct (no_dup_isMap _ pf _ _ _ _ _ (conj IN H1)) as [F _];
      discriminate.
  - inversion EQA; subst.
    destruct (no_dup_isMap _ pf _ _ _ _ _ (conj IN H2)) as [F _];
      discriminate.
  - inversion EQA; subst.
    simpl; apply List.in_or_app; right; left; reflexivity.
  - simpl; apply List.in_or_app.
    destruct (nat_pair_eq_dec (d1, d2) (b1, b2)) as [EQ | NEQ].
    + right; left; auto.
    + left; apply (IHLTS c1 c2 d1 d2 s0 EQA).
      subst g; apply List.in_app_or in IN; apply List.in_or_app.
      destruct IN as [IN | [EQ | IN]];
        [left; exact IN | inversion EQ; subst; contradiction
        | right; right; exact IN].
Qed.

Lemma lts_sl_pos : forall g p a g' p' pf,
    lts g p a g' p' pf ->
    sl_pos p ->
    sl_pos p'.
Proof.
  introv LTS.
  induction LTS; intros SLP.
  - apply sl_pos_par_intro; eauto using sl_pos_par_l, sl_pos_par_r.
  - eauto using sl_pos_out.
  - eauto using sl_pos_out.
  - apply sl_pos_pmap; eauto using sl_pos_inp.
  - apply sl_pos_pmap; eauto using sl_pos_inp.
  - apply sl_pos_par_intro.
    + apply sl_pos_pmap; eauto using sl_pos_bang.
    + unfold q; unfold sl_pos; simpl; fold (sl_pos (dep_relabel p (domain g) pf)).
      apply sl_pos_dep_relabel; eauto using sl_pos_bang.
  - apply sl_pos_par_intro; eauto using sl_pos_par_l, sl_pos_par_r.
  - apply sl_pos_nu_intro.
    + apply sl_pos_par_intro; eauto using sl_pos_par_l, sl_pos_par_r.
    + apply sl_pos_par_l in SLP.
      eapply SLP, lts_out_hid_secLabs; eauto.
  - apply sl_pos_par_intro; eauto using sl_pos_par_l, sl_pos_par_r.
  - apply sl_pos_nu_intro.
    + apply sl_pos_par_intro; eauto using sl_pos_par_l, sl_pos_par_r.
    + apply sl_pos_par_l in SLP.
      eapply SLP, lts_out_hid_secLabs; eauto.
  - eauto using sl_pos_nu.
  - apply sl_pos_nu_intro; eauto using sl_pos_nu, sl_pos_nu_pos.
Qed.

(* Subject reduction lifted to weak (multi-step tau) transitions. As in sr,
   the conclusion holds for every isMap proof of the final environment. *)
Lemma subject_reduction_wlts :
  forall g p g' p' pf,
    sl_pos p ->
    typeCheck g pf p ->
    wlts (g, p) (g', p') ->
    forall pf',
      typeCheck g' pf' p'.
Proof.
  intros g p g' p' pf SLP TC W.
  assert (TCALL : forall pf0, typeCheck g pf0 p).
  { intros pf0; rewrite (proof_irrelevance _ pf0 pf); exact TC. }
  clear TC pf.
  unfold wlts in W.
  remember (g, p) as c eqn:EQC.
  remember (g', p') as c' eqn:EQC'.
  revert g p SLP TCALL EQC.
  induction W as [c | c c1 c2 STEP W IH];
    intros g p SLP TCALL EQC; subst.
  - inversion EQC; subst; auto.
  - destruct c1 as [g1 p1].
    destruct STEP as (a1 & a2 & nd_pf & LTS).
    apply (IH eq_refl g1 p1); [eapply lts_sl_pos; eauto | | reflexivity].
    intros pf1.
    eapply sr with (pf := no_dup_isMap _ nd_pf); eauto.
Qed.

(* NoDup of the environment is preserved along weak transitions of a
   well-typed process: typeCheck_no_dup supplies the secLabs invariants
   required by lts_no_dup, and sr re-establishes typeCheck after each step. *)
Lemma wlts_no_dup g p g' p' (pf : NoDup (domain g)) :
  sl_pos p ->
  typeCheck g (no_dup_isMap _ pf) p ->
  wlts (g, p) (g', p') ->
  NoDup (domain g').
Proof.
  intros SLP TC W.
  unfold wlts in W.
  remember (g, p) as c eqn:EQC.
  remember (g', p') as c' eqn:EQC'.
  revert g p pf SLP TC EQC.
  induction W as [c | c c1 c2 STEP W IH];
    intros g p pf SLP TC EQC; subst.
  - inversion EQC; subst; auto.
  - destruct c1 as [g1 p1].
    destruct STEP as (a1 & a2 & nd_pf & LTS).
    destruct (typeCheck_no_dup _ _ _ pf TC) as [INCL NDSL].
    assert (ND1 : NoDup (domain g1)).
    { eapply lts_no_dup with (pf_incl := incl_incl2 _ _ NDSL pf INCL); eauto.
      apply incl_preserves_max; auto. }
    apply (IH eq_refl g1 p1 ND1); [eapply lts_sl_pos; eauto | | reflexivity].
    eapply sr; eauto.
Qed.

(* Type safety: well-typed processes never reach an error under weak
   transitions. *)
Theorem type_safety :
  forall (g g' : typeEnv) (p p' : dproc) (pf : NoDup (domain g)),
    sl_pos p ->
    typeCheck g (no_dup_isMap _ pf) p ->
    wlts (g, p) (g', p') ->
    notError g' p'.
Proof.
  intros g g' p p' pf SLP TC W.
  apply type_soundness with
    (pf := no_dup_isMap _ (wlts_no_dup g p g' p' pf SLP TC W)).
  eapply subject_reduction_wlts; eauto.
Qed.
