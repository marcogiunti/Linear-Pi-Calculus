Require Import
        Bool List Omega PeanoNat Program.Equality
        ListAddOns Max RemoveEntry Domain NewEntries
        header
        operations pi_syntax semantics type_system.

Require Import CpdtTactics LibTactics.

Inductive replication : dproc -> dproc -> dproc -> Prop  :=
| replInp: forall a1 a2 x1 x2 b1 b2 p g pf,
    replication (dBang a1 a2 x1 x2 p)
                (dPar (pmap p x1 x2 b1 b2) (dBang a1 a2 x1 x2 (dep_relabel p (domain g) pf))) p
| replParL: forall p p' q r,
    replication p p' r -> 
    replication (dPar p q) (dPar p' q) r
| replCom: forall p p' q q' r,
    replication q q' r -> 
    replication (dPar p q) (dPar p' q') r
| replClose:forall b1 b2 p p' q q' r,
    replication q q' r -> 
    replication (dPar p q) (dNu b1 b2 (dPar p' q')) r
| replHide: forall b1 b2 q q' r,
    replication q q' r ->
    replication (dNu b1 b2 q) (dNu b1 b2 q') r.

Lemma secLabs_of_repl p q r:
  replication p q r ->
  incl (secLabs r) (secLabs p).
Proof with eauto using incl_refl,incl_appr,incl_appl.
  introv REPL; dependent induction REPL; try simpl...
Qed.

Lemma sl_pos_repl p q r:
  sl_pos p ->
  replication p q r ->
  sl_pos r.
Proof with eauto.
  introv SLP REPL; unfold sl_pos, pos in *; introv IN;
    specialize SLP with x1 x2; intuition;
      eapply secLabs_of_repl in IN...
Qed.

Lemma replication_diff: forall q q1,
    replication q q q1 -> False.
Proof with eauto.  intros. induction q; inversion H...
Qed.

Hint Resolve replication_diff.

Lemma replication_unique: forall g p a g1 p1 nd_pf q1 q2,
    lts g p a g1 p1 nd_pf ->
    replication p p1 q1 ->
    replication p p1 q2 ->
    q1 = q2.
Proof with eauto using no_dup_not_in_removeEntry.
  intros g p a g1 p1 nd_pf q1 q2 LTS R1 R2.
  generalize dependent q1.
  generalize dependent q2.
  dependent induction LTS.
  11:{
    clear IHLTS.
    intros; inv R1; inv R2; inv LTS; try inv H5;
      try inv H10; try inv H0; intuition.
    assert (~In (b1, b2, hid, t0) (removeEntry (b1, b2) g));try
                                                              contradiction...
    all:try inv H7. all: try inv H11; try contradiction.
  }
  intros. specialize IHLTS with q2 q1; intuition.
  inversion R1; inversion R2; intuition.
  all: try intros; inversion R1; subst...
  all: try inversion R1; inversion R2; subst...
  all:assert (False); try eapply replication_diff;eauto; try contradiction...
Qed.