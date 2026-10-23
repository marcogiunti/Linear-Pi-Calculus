Require Import
        Bool List Lia PeanoNat Program.Equality
        pairEq type_system pi_syntax semantics.

  Require Import CpdtTactics LibTactics.

Lemma in_g_in_domain: forall  a f t g,
    In (a,f,t) g -> In a (domain g).
Proof.
  intros a f t g IN.
  dependent induction g.
  inversion IN.
  apply in_inv in IN.
  destruct IN as [EQ | IN].
  all:subst; unfold domain; fold domain; intuition.
Qed.

Lemma in_domain_in_g: forall a g,
    In a (domain g) -> exists f t, In (a,f,t) g.
Proof with eauto.
  intros a g IN.
  dependent induction g.
  inversion IN. destruct a0. destruct p.
  unfold domain in IN; fold domain in IN; apply in_inv in IN.
  destruct IN as [EQ | IN]; subst.
  exists  f; exists p0; apply in_eq.
  intuition.
  destruct H as [f1 [t1 H]].
  exists f1; exists t1. intuition.
Qed.


Lemma incl_hid_proj: forall g,
    incl (hid_proj g) g.
Proof with eauto.
  induction g; simpl; intuition;
    try destruct b0; intuition.
Qed. 


Lemma hid_proj_incl  : forall g,
    incl (domain (hid_proj g)) (domain g).
Proof.
  intros. induction g.
  unfold hid_proj. intuition. 
  unfold hid_proj. fold hid_proj.
  induction a. induction a. induction b0. intuition. 
  unfold domain. fold domain. intuition.      
  unfold domain. fold domain. intuition.
  unfold domain. fold domain. intuition.
Qed.

Lemma vis_proj_incl  : forall g,
    incl (domain (vis_proj g)) (domain g).
Proof.
  intros. induction g.
  unfold vis_proj. intuition. 
  unfold vis_proj. fold vis_proj.
  induction a. induction a. induction b0. intuition. 
  unfold domain. fold domain. intuition.      
  unfold domain. fold domain. intuition.
  unfold domain. fold domain. intuition.
  unfold domain. fold domain. intuition.
Qed.


Lemma hid_proj_app g1 g2:
  hid_proj (g1 ++ g2) = hid_proj g1 ++ hid_proj g2.
Proof with eauto.
  intros; dependent induction g1; simpl;
    try destruct a as [[[a1 a2] f]t];
    try destruct f;
    try rewrite IHg1...
Qed.

Lemma hid_proj_flagOf: forall b1 b2 g (nd_pf : NoDup (domain g)),
    In (b1, b2) (domain (hid_proj g)) ->
    flagOf g (b1, b2) hid.
Proof with eauto.
  intros; induction g. simpl in *; try contradiction...
  destruct a as (((c1 & c2) &f) &t); simpl in nd_pf.
  inversion nd_pf; subst.
  destruct f; simpl in H; intuition.
  inversion H0; subst; econstructor...
  all: try inversion H1; subst;econstructor; try right...
Qed.



           
Lemma InB_false a1 a2 f t g:
  InB (a1,a2) g = (f, t, false) ->
  f = ill /\ t = Top.
Proof with eauto.
  introv INB;
    induction g;
    try destruct a as [[[c1 c2]f1]t1];
     unfold InB in *; fold InB in *;
    try inv INB; intuition;
    try destruct (pair_eq (a1, a2) (c1, c2));
    try discriminate;
    intuition.
Qed.   
