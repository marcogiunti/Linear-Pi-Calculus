Require Import
  Bool List Lia PeanoNat 
  Domain RemoveEntry
  header operations pi_syntax 
  pairEq type_system
  semantics
  type_system_rules
  proposition27
  tc_dep_relabel_premises
  type_checking_1
  type_operations_1
  lts_no_dup
  linear_pi.

Require Import CpdtTactics LibTactics.

Corollary wf_preservation g1 p1 a g2 p2 pf nd_pf:
    sl_pos p1 ->
    typeCheck g1 pf p1 -> 
    lts g1 p1 a g2 p2 nd_pf ->
    wf p2.
Proof with eauto using typeCheck_no_dup.
  introv SLP TC LTS.
  assert (NDSL: NoDup (secLabs p1))...
  eapply typeCheck_no_dup...
  assert (nd_pf2: NoDup (domain g2)).
  eapply lts_no_dup in LTS; try tauto.
  eapply incl_incl2...
  eapply typeCheck_no_dup...
  eapply incl_preserves_max, typeCheck_no_dup...  
  assert (LTS2 := LTS).
  eapply sr with (pf := pf) in LTS2; try tauto.
  split.
  - eapply typeCheck_no_dup...
  - eapply fn_disjoint_sl in LTS2...
  Unshelve.
  eapply no_dup_isMap...
Qed.  