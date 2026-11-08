(* Relation between the full transition relation [lts] and its left-only
   fragment [ltsL]: every [lts] step is an [ltsL] step up to swapping parallel
   components along the spine of the process. *)

From Stdlib Require Import List Lia Permutation.
Require Import
        pi_syntax type_system semantics Domain
        proposition27 lts_no_dup.
Import ListNotations.

Inductive par_equiv : dproc -> dproc -> Prop :=
| pe_refl : forall p, par_equiv p p
| pe_par : forall p p' q q',
    par_equiv p p' -> par_equiv q q' -> par_equiv (dPar p q) (dPar p' q')
| pe_swap : forall p p' q q',
    par_equiv p p' -> par_equiv q q' -> par_equiv (dPar p q) (dPar q' p')
| pe_nu : forall b c p p',
    par_equiv p p' -> par_equiv (dNu b c p) (dNu b c p').

Lemma par_equiv_sym : forall p q, par_equiv p q -> par_equiv q p.
Proof.
  induction 1.
  - apply pe_refl.
  - apply pe_par; assumption.
  - apply pe_swap; assumption.
  - apply pe_nu; assumption.
Qed.

Lemma secLabs_perm : forall p q,
    par_equiv p q -> Permutation (secLabs p) (secLabs q).
Proof.
  induction 1; simpl.
  - apply Permutation_refl.
  - apply Permutation_app; assumption.
  - rewrite Permutation_app_comm. apply Permutation_app; assumption.
  - apply Permutation_app_tail; assumption.
Qed.

Lemma secLabs_par_equiv : forall p q,
    par_equiv p q -> forall x, In x (secLabs p) <-> In x (secLabs q).
Proof.
  induction 1; intro x; simpl; rewrite ?in_app_iff; try tauto;
    repeat match goal with
           | H : forall y, In y (secLabs _) <-> In y (secLabs _) |- _ =>
             specialize (H x)
           end; tauto.
Qed.

Lemma sl_pos_par_equiv : forall p q, par_equiv p q -> sl_pos p -> sl_pos q.
Proof.
  unfold sl_pos, pos; intros p q E SLP x1 x2 IN.
  apply (SLP x1), (secLabs_par_equiv _ _ E); assumption.
Qed.

(* Every step of the full relation is a left-only step up to swapping. *)
Theorem lts_to_left : forall g p a g' q pf,
    lts g p a g' q pf ->
    exists L L', par_equiv p L /\ par_equiv q L' /\ ltsL g L a g' L' pf.
Proof.
  induction 1;
    repeat match goal with
           | H : exists _ _, _ |- _ =>
             let A := fresh "A" in let A' := fresh "A'" in
             let E := fresh "E" in let E' := fresh "E'" in
             let S := fresh "S" in
             destruct H as (A & A' & E & E' & S)
           end.
  - do 2 eexists; split; [|split];
      [eapply pe_par; [eassumption | apply pe_refl]
      | eapply pe_par; [eassumption | apply pe_refl]
      | eapply L_parL; eassumption].
  - do 2 eexists; split; [apply pe_refl | split; [apply pe_refl | eapply L_lOut; eassumption]].
  - do 2 eexists; split; [apply pe_refl | split; [apply pe_refl | eapply L_uOut; eassumption]].
  - do 2 eexists; split; [apply pe_refl | split; [apply pe_refl | eapply L_lIn; eassumption]].
  - do 2 eexists; split; [apply pe_refl | split; [apply pe_refl | eapply L_uIn; eassumption]].
  - do 2 eexists; split; [apply pe_refl | split; [apply pe_refl | eapply L_uRin; eassumption]].
  - do 2 eexists; split; [|split]; [eapply pe_par; eassumption | eapply pe_par; eassumption | eapply L_lcomL; eassumption].
  - do 2 eexists; split; [|split]; [eapply pe_par; eassumption | eapply pe_nu; eapply pe_par; eassumption | eapply L_lclsL; eassumption].
  - do 2 eexists; split; [|split]; [eapply pe_par; eassumption | eapply pe_par; eassumption | eapply L_ucomL; eassumption].
  - do 2 eexists; split; [|split]; [eapply pe_par; eassumption | eapply pe_nu; eapply pe_par; eassumption | eapply L_uclsL; eassumption].
  - do 2 eexists; split; [|split];
      [eapply pe_nu; eassumption | eassumption | eapply L_open; eassumption].
  - do 2 eexists; split; [|split];
      [eapply pe_nu; eassumption | eapply pe_nu; eassumption | eapply L_hide; eassumption].
  - do 2 eexists; split; [|split];
      [eapply pe_swap; [apply pe_refl | eassumption]
      | eapply pe_swap; [apply pe_refl | eassumption]
      | eapply L_parL; eassumption].
  - do 2 eexists; split; [|split]; [eapply pe_swap; eassumption | eapply pe_swap; eassumption | eapply L_lcomL; eassumption].
  - do 2 eexists; split; [|split]; [eapply pe_swap; eassumption | eapply pe_nu; eapply pe_swap; eassumption | eapply L_lclsL; eassumption].
  - do 2 eexists; split; [|split]; [eapply pe_swap; eassumption | eapply pe_swap; eassumption | eapply L_ucomL; eassumption].
  - do 2 eexists; split; [|split]; [eapply pe_swap; eassumption | eapply pe_nu; eapply pe_swap; eassumption | eapply L_uclsL; eassumption].
Qed.

(* The left-only fragment embeds in the full relation. *)
Theorem ltsL_lts : forall g p a g' q pf,
    ltsL g p a g' q pf -> lts g p a g' q pf.
Proof.
  induction 1.
  - eapply parL; eassumption.
  - eapply lOut; eassumption.
  - eapply uOut; eassumption.
  - eapply lIn; eassumption.
  - eapply uIn; eassumption.
  - eapply uRin; eassumption.
  - eapply lcomL; eassumption.
  - eapply lclsL; eassumption.
  - eapply ucomL; eassumption.
  - eapply uclsL; eassumption.
  - eapply open; eassumption.
  - eapply hide; eassumption.
Qed.

(* [lts_no_dup] for the full relation. *)
Lemma lts_no_dup_full :
  forall g p a g' p' nd_pf,
    incl_ (secLabs p) (domain g) ->
    lts g p a g' p' nd_pf ->
    sl_pos p ->
    NoDup (secLabs p) ->
    NoDup (domain g').
Proof.
  intros g p a g' p' nd_pf INC LTS SLP NDSL.
  destruct (lts_to_left _ _ _ _ _ _ LTS) as (L & L' & E & _ & LEFT).
  assert (NDL : NoDup (secLabs L))
    by (eapply Permutation_NoDup; [apply secLabs_perm; exact E | exact NDSL]).
  assert (INL : incl (secLabs L) (domain g)).
  { intros x IN.
    exact (proj1 (INC x (proj2 (secLabs_par_equiv _ _ E x) IN))). }
  eapply lts_no_dup with (pf_incl := incl_incl2 _ _ NDL nd_pf INL);
    try eassumption.
  - eapply sl_pos_par_equiv; eassumption.
  - apply incl_preserves_max; exact INL.
Qed.
