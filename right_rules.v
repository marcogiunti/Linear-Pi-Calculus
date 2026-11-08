(* The full transition relation [lts] has left rules and right rules.
   This file relates it to the left-only fragment [ltsL], on which the
   development is carried out:

   - [lts_to_left]: every [lts] step is an [ltsL] step up to swapping
     parallel components along the spine of the process;
   - [typeCheck_par_equiv]: swapping preserves typing, so [sr] holds for [lts];
   - [lts_par_symmetric]: machine check that the rules for [dPar] are closed
     under exchanging the two components, i.e. no right rule is missing. *)

From Stdlib Require Import List Lia.
Require Import
        header operations pi_syntax pairEq type_system
        semantics type_system_rules
        split_cons_remove
        par_equiv
        lts_payload_un_inp
        type_checking_1
        lts_no_dup
        proposition27
        linear_pi.
Import ListNotations.

Lemma typeCheck_par_equiv : forall p q,
    par_equiv p q -> forall g pf, typeCheck g pf p -> typeCheck g pf q.
Proof.
  intros p q E.
  induction E as [p | p p' q q' E1 IH1 E2 IH2 | p p' q q' E1 IH1 E2 IH2 | b c p p' E IH];
    intros g pf T.
  - exact T.
  - inversion T; subst.
    eapply TPar; [eassumption | apply IH1; eassumption | apply IH2; eassumption].
  - inversion T; subst.
    eapply TPar; [apply split_comm; eassumption
                 | apply IH2; eassumption | apply IH1; eassumption].
  - inversion T; subst. eapply TNew; [eassumption | apply IH; eassumption].
Qed.

(* Subject reduction for the full relation. *)
Theorem sr :
  forall g p a g' p' nd_pf pf pf',
    sl_pos p ->
    typeCheck g pf p ->
    lts g p a g' p' nd_pf ->
    typeCheck g' pf' p'.
Proof.
  intros g p a g' p' nd_pf pf pf' SLP TC LTS.
  destruct (lts_to_left _ _ _ _ _ _ LTS) as (L & L' & E & E' & LEFT).
  apply (typeCheck_par_equiv L' p' (par_equiv_sym _ _ E')).
  apply (sr_left g L a g' L' nd_pf pf pf').
  - eapply sl_pos_par_equiv; eassumption.
  - eapply typeCheck_par_equiv; eassumption.
  - exact LEFT.
Qed.

(* The environment stays duplicate-free along steps of well-typed processes. *)
Lemma lts_no_dup_typed :
  forall g p a g' p' nd_pf pf,
    sl_pos p ->
    typeCheck g pf p ->
    lts g p a g' p' nd_pf ->
    NoDup (domain g').
Proof.
  intros g p a g' p' nd_pf pf SLP TC LTS.
  destruct (lts_to_left _ _ _ _ _ _ LTS) as (L & L' & E & _ & LEFT).
  assert (TCL : typeCheck g pf L) by (eapply typeCheck_par_equiv; eassumption).
  assert (SLL : sl_pos L) by (eapply sl_pos_par_equiv; eassumption).
  destruct (typeCheck_no_dup _ _ _ nd_pf TCL) as [INCL NDSL].
  eapply lts_no_dup with (pf_incl := incl_incl2 _ _ NDSL nd_pf INCL);
    try eassumption.
  apply incl_preserves_max; assumption.
Qed.

(* No right rule is missing: exchanging the components of a parallel
   composition yields a transition with the same label and environment. *)
Definition swap_result (r : dproc) : dproc :=
  match r with
  | dPar x y => dPar y x
  | dNu b c (dPar x y) => dNu b c (dPar y x)
  | _ => r
  end.

Theorem lts_par_symmetric : forall g p q a g' r pf,
    lts g (dPar p q) a g' r pf ->
    lts g (dPar q p) a g' (swap_result r) pf.
Proof.
  intros g p q a g' r pf H.
  inversion H; subst; simpl;
    first
      [ eapply parL; eassumption
      | eapply parR; eassumption
      | solve [eapply lcomL; eassumption]
      | solve [eapply lcomR; eassumption]
      | solve [eapply lclsL; eassumption]
      | solve [eapply lclsR; eassumption]
      | solve [eapply ucomL; eassumption]
      | solve [eapply ucomR; eassumption]
      | solve [eapply uclsL; eassumption]
      | solve [eapply uclsR; eassumption] ].
Qed.

(* Non-divergence for the full relation. *)
Lemma no_nu_wrapped_step_full :
  forall g p a g' q pf, lts g p a g' q pf -> nu_wrap p q -> False.
Proof.
  induction 1; intro W;
    repeat match goal with
           | H : nu_wrap (dPar _ _) (dPar _ _) |- _ => inversion H; clear H; subst
           | H : nu_wrap (dPar _ _) (dNu _ _ _) |- _ => inversion H; clear H; subst
           | H : nu_wrap (dBang _ _ _ _ _) (dPar _ _) |- _ => inversion H; clear H; subst
           end;
    try (eauto using nu_wrap_0; fail);
    try (apply nu_wrap_size in W; simpl in W; rewrite ?dproc_size_pmap in W; lia).
  all: try (match goal with
            | H : nu_wrap (dNu ?b ?c ?r) _ |- _ => eauto using nu_wrap_strip
            end; fail).
  all: try (inversion W; subst; eauto using nu_wrap_0, nu_wrap_strip; fail).
Qed.

Theorem nonDivergentProcesses_lts :
  forall g p a g' nd_pf, ~ lts g p a g' p nd_pf.
Proof.
  intros; intro H; eapply no_nu_wrapped_step_full; [exact H | constructor].
Qed.
