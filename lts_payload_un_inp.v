Require Import
        Bool List Lia PeanoNat Program.Equality
        ListAddOns Max RemoveEntry Domain
        ListAddOns Max RemoveEntry Domain
        header
        operations pi_syntax 
        pairEq type_system
        semantics
        type_operations_1
        split_existential
        no_dup_split_no_dup
        proposition27
        disjoint_newEntries
        type_system_rules
        lts_no_dup
        split_operations_4.
        

Require Import CpdtTactics LibTactics.
Import ListNotations.

(* A step can never produce its source wrapped in zero or more restrictions.
   Zero restrictions is non-divergence; the general form is what makes the
   induction go through the [open] and [hide] rules. *)
Fixpoint dproc_size (p : dproc) : nat :=
  match p with
  | dZero => 1
  | dBang _ _ _ _ q | dInp _ _ _ _ q | dOut _ _ _ _ q | dNu _ _ q => S (dproc_size q)
  | dPar q r => S (dproc_size q + dproc_size r)
  end.

Lemma dproc_size_pmap : forall p a b c d, dproc_size (pmap p a b c d) = dproc_size p.
Proof. induction p; intros; simpl; rewrite ?IHp, ?IHp1, ?IHp2; reflexivity. Qed.

Inductive nu_wrap (p : dproc) : dproc -> Prop :=
| nu_wrap_0 : nu_wrap p p
| nu_wrap_S : forall b c q, nu_wrap p q -> nu_wrap p (dNu b c q).

Lemma nu_wrap_size : forall p q, nu_wrap p q -> dproc_size p <= dproc_size q.
Proof. induction 1; simpl; lia. Qed.

Lemma nu_wrap_strip : forall b c r q, nu_wrap (dNu b c r) q -> nu_wrap r q.
Proof. induction 1; constructor; auto; constructor. Qed.

Lemma no_nu_wrapped_step :
  forall g p a g' q pf, ltsL g p a g' q pf -> nu_wrap p q -> False.
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

Theorem nonDivergentProcesses :
    forall g p a g' nd_pf,
      ~ ltsL g p a g' p nd_pf.
Proof. intros; intro H; eapply no_nu_wrapped_step; [exact H | constructor]. Qed.

 #[global] Hint Resolve nonDivergentProcesses length_zero_iff_nil.



 

  
Lemma notIn_false: forall b0 b3 b1 b2 k f s g,
    In (b0, b3) (domain g) ->
    ~ In (b0, b3) (domain (k ++ (b1, b2, f, s) :: removeEntry (b1, b2) g)) ->
    False.
Proof with eauto.
  intros c1 c2 b1 b2 k f s g IN NIN.
  dependent induction g.
  inversion IN...
  unfold domain in IN; fold domain in IN;  destruct a as [[[a1 a2] ff]t].
   case_eq (pair_eq (a1,a2)(b1,b2)). intros PEQ.
   unfold removeEntry in NIN; rewrite PEQ in NIN; fold removeEntry in NIN...
   inversion IN. inversion H. subst.
   rewrite <-pairEq_eq in PEQ; inversion PEQ; subst.
   assert (In (b1, b2) (domain (k ++ (b1, b2, f, s) :: g))).
           erewrite domain_distr,in_app_iff; right.
   unfold domain; fold domain...
   contradiction.
   eapply IHg...
   (*~ In (c1, c2) (domain (k ++ (b1, b2, f, s) :: removeEntry (b1, b2) g))*)
   intros ABS.  rewrite domain_distr,in_app_iff in ABS.
   destruct ABS as [ABS1 | ABS3].
   assert (In (c1, c2) (domain (k ++ (b1, b2, f, s) :: g))).
   rewrite domain_distr,in_app_iff. left...
   contradiction.
   unfold domain in ABS3; fold domain in ABS3.
   destruct ABS3 as [ABS1 | ABS3]. inversion ABS1; subst.
   assert (In (c1, c2) (domain (k ++ (c1, c2, f, s) :: g))).
   rewrite domain_distr,in_app_iff. right...
   contradiction.
   eapply in_domain_in_g in ABS3 as [ff2 [tt2 ABS3]].
   eapply in_removeEntry,in_g_in_domain in ABS3.
   assert (In (c1, c2) (domain (k ++ (b1, b2, f, s) :: g))).
   rewrite domain_distr,in_app_iff. right...
   unfold domain; fold domain; right...
   contradiction.
   
   intros PNEQ.
   unfold removeEntry in NIN; rewrite PNEQ in NIN; fold removeEntry in NIN...
   inversion IN. inversion H. subst.
   assert ( In (c1, c2)
               (domain (k ++ (b1, b2, f, s) :: (c1, c2, ff, t) :: removeEntry (b1, b2) g))).
   erewrite domain_distr,in_app_iff; right.
   unfold domain; fold domain; right...
   contradiction.
   eapply IHg...
   intros ABS.
   rewrite domain_distr,in_app_iff in ABS.
   destruct ABS as [ABS1 | ABS3].
   assert (In (c1, c2) ((domain (k ++ (b1, b2, f, s) :: (a1, a2, ff, t) :: removeEntry (b1, b2) g)))).
   rewrite domain_distr,in_app_iff. left...
   contradiction.
   unfold domain in ABS3; fold domain in ABS3.
   destruct ABS3 as [ABS1 | ABS3]. inversion ABS1; subst.
   assert (In (c1, c2) (((domain (k ++ (c1, c2, f, s) :: (a1, a2, ff, t) :: removeEntry (c1, c2) g))))).
   rewrite domain_distr,in_app_iff. right...
   contradiction.
   eapply in_domain_in_g in ABS3 as [ff2 [tt2 ABS3]].
   eapply in_removeEntry,in_g_in_domain in ABS3.
   assert (In (c1, c2) ((domain (k ++ (b1, b2, f, s) :: (a1, a2, ff, t) :: removeEntry (b1, b2) g)))).
   rewrite domain_distr,in_app_iff. right...
   unfold domain; fold domain; right; right.
   case_eq (pair_eq (b1, b2) (c1, c2)). intros PEQ.
   rewrite <-pairEq_eq in PEQ; inversion PEQ; subst.
   assert (In (c1, c2)
              (domain (k ++ (c1, c2, f, s) :: (a1, a2, ff, t) :: removeEntry (c1, c2) g))).
   rewrite domain_distr,in_app_iff. right...
   contradiction.
   intros PNEQ1. rewrite <-pairEq_neq in PNEQ1. 
   eapply in_domain_in_g in ABS3 as [ff3 [tt3 ABS3]]...
   eapply in_g_in_domain,removeEntry_in...
   contradiction.
Qed.




  #[global] Hint Resolve
       length_inv removeEntry_length
       max_app_l max_app_r.



  
  

  #[global] Remove Hints in_g_in_domain.


 
 
