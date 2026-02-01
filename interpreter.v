Require Import
  Bool List Omega PeanoNat 
  Domain RemoveEntry
  header operations pi_syntax 
  pairEq type_system
  semantics
  split_operations_4
  lts_no_dup
  proposition27
  operations.

Require Extraction.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlZInt.
Require Import CpdtTactics LibTactics.
Require Import FunInd.
Require Import Coq.Program.Equality.

Import ListNotations.
Import Notations.

(** Partial functions *)
Definition t  (A : Type) := option A.
Definition _return {a : Set} (x_value : a) : t a := Some x_value.
Definition raise {a : Set} : t a := None.
Definition partial_fun A B := A -> t B. 

Lemma pol_eq_eq p1 p2:
  pol_eq p1 p2 = true <-> p1 = p2.
Proof with eauto.
  split; introv EQ.
  induction p1, p2;
    simpl in EQ;
    try discriminate...
  subst; destruct p2...
Qed.

Lemma flag_eq_eq: forall f1 f2,
    flag_eq f1 f2 = true <-> f1 =f2.
Proof with eauto.
  split; introv EQ.
  induction f1, f2;
    simpl in EQ;
    try discriminate...
  subst; destruct f2...
Qed.

Lemma flag_eq_false: forall f1 f2,
    flag_eq f1 f2 = false -> f1 <> f2.
Proof with eauto using flag_eq_eq.
  intuition;
    try rewrite <-flag_eq_eq, H in *;
    try discriminate...
Qed.

Lemma mode_eq_eq p1 p2:
  mode_eq p1 p2 = true <-> p1 = p2.
Proof with eauto.
  split; introv EQ.
  induction p1, p2;
    simpl in EQ;
    try discriminate...
  subst; destruct p2...
Qed.

Lemma mode_eq_true m:
  mode_eq m m = true.
Proof with eauto.
  eapply mode_eq_eq...
Qed.

Lemma pol_eq_true m:
  pol_eq m m = true.
Proof with eauto.
  eapply pol_eq_eq...
Qed.

Lemma type_eq_eq t1 t2:
  type_eq t1 t2 = true <-> t1 = t2.
Proof with eauto.
  split; introv EQ.
  dependent induction t1;
    dependent induction t2;
    simpl in EQ;
    try discriminate...
  case_eq (mode_eq m m0); try introv MEQ;
    try rewrite mode_eq_eq in MEQ; subst.
  rewrite  mode_eq_true in EQ.
  case_eq (pol_eq p p0); try introv PEQ;
    try rewrite pol_eq_eq in PEQ; subst.
  rewrite pol_eq_true in EQ.
  erewrite IHt1...
  rewrite PEQ in EQ; discriminate.
  rewrite MEQ in EQ; discriminate.

  subst; induction t2;
    repeat simpl;
    try rewrite mode_eq_true;
    try rewrite pol_eq_true...
Qed.

Lemma type_eq_true m:
  type_eq m m = true.
Proof with eauto.
  eapply type_eq_eq...
Qed.

Function  tplus  (t1 t2 : piType) : option piType :=
  match t1, t2 with
  | Top, Top => Some Top
  | Chan un p1 r1, Chan un p2 r2 =>
      if type_eq r1 r2
      then
        Some (Chan un (pol_cup p1 p2) r1)
      else
        raise
  | Chan lin p1 r1, Chan lin p2 r2 =>
      if type_eq r1 r2
      then
        match p1, p2 with
        | empty, _ => 
            Some t2
        | _, empty =>
            Some t1
        | inp, out
        | out, inp =>
            Some (Chan lin io r1)
        | _, _ =>
            raise
        end      
      else
        raise
  | _, _ => raise
  end.

Hint Constructors type_plus.

Lemma tplus_type_plus t1 t2 t :
  tplus t1 t2 = Some t ->
  type_plus t1 t2 t.
Proof with eauto.
  introv TP.
  dependent induction t1;
    dependent induction t2...
  - assert (m = m0).
    destruct m, m0;
      inv TP...
    subst m0.
    destruct m.
    + inv TP...
      case_eq (type_eq t1 t2); introv EQ;
        rewrite EQ in *;
        try rewrite type_eq_eq in EQ; subst.
      destruct p,p0; inv H0...
      discriminate.
    + inv TP...
      case_eq (type_eq t1 t2); introv EQ;
        rewrite EQ in *;
        try rewrite type_eq_eq in EQ; subst.
      inv H0...
      discriminate.
  - inv TP; destruct m; try discriminate...
  - inv TP; destruct m; try discriminate...
  - inv TP...
Qed.

Function  tremove  (t1 t2 : piType) : option piType :=
  match t1, t2 with
  | Top, Top => Some Top
  | Chan un p1 r1, Chan un p2 r2 =>
      if type_eq r1 r2
      then
        match p1, p2 with
        | io, _ =>
            Some t1
        |_, empty =>
           Some t1
        | inp, inp
        | out, out =>
            Some t1
        | _, _ => raise
        end
      else
        raise
  | Chan lin p1 r1, Chan lin p2 r2 =>
      if type_eq r1 r2
      then
        match p1, p2 with
        | _, empty =>
            Some t1
        | io, inp =>
            Some (Chan lin out r1)
        | io, out =>
            Some (Chan lin inp r1)
        | io, io 
        | inp, inp
        | out, out =>
            Some (Chan lin empty r1)
        | _, _ =>
            raise
        end      
      else
        raise
  | _, _ => raise
  end.

Lemma tremove_type_remove t1 t2 t :
  tremove t1 t2 = Some t ->
  type_remove t1 t2 t.
Proof with eauto using type_remove_un_2, type_remove_lin_2.
  introv TP.
  dependent induction t1;
    dependent induction t2...
  - assert (m = m0).
    destruct m, m0; inv TP...
    subst m0.
    destruct m.
    + inv TP.
      case_eq (type_eq t1 t2); introv EQ;
        rewrite EQ in *;
        try rewrite type_eq_eq in EQ; subst.
      destruct p,p0; inv H0;
        try eapply type_remove_lin_2...
      discriminate.
    +  inv TP.
       case_eq (type_eq t1 t2); introv EQ;
         rewrite EQ in *;
         try rewrite type_eq_eq in EQ; subst.
       destruct p,p0; inv H0;
         try eapply type_remove_un_2...
       discriminate.
  - inv TP; destruct m; try discriminate...
  - inv TP; destruct m; try discriminate...
  - inv TP; try discriminate;
      try eapply type_remove_top_2...
Qed.

Function typeEnv_eq g1 g2 :=
  match g1, g2 with
  | [], [] =>
      true
  | (a1, a2, f1, t1) :: d1, (b1, b2, f2, t2) :: d2 =>
      pair_eq (a1, a2) (b1, b2) && flag_eq f1 f2
      && type_eq t1 t2 && typeEnv_eq d1 d2
  | _, _ =>
      false
  end.

Lemma typeEnv_eq_eq g1 g2 :
  typeEnv_eq g1 g2 = true <-> g1 = g2.
Proof with eauto.
  split; introv EQ.
  dependent induction g1;
    dependent induction g2...
  inv EQ.
  induction g1; destruct a as ([[b1 b2] f1] &t1);
    try inv EQ...
  assert (a = a0 /\ g1 = g2).
  destruct a as ([[b1 b2] f1] &t1);
    destruct a0 as ([[c1 c2] f2] &t2);
    inv EQ...
  eapply andb_true_iff in H0 as (EQ1 &EQ4).
  eapply andb_true_iff in EQ1 as (EQ1 &EQ3).
  eapply andb_true_iff in EQ1 as (EQ1 &EQ2).
  rewrite type_eq_eq in *;
    rewrite flag_eq_eq in *;
    subst.
  rewrite <-pairEq_eq in EQ1;
    inv EQ1...
  destruct H; subst...
  subst; induction g2;
    try destruct a as ([[b1 b2] f1] &t1);
    repeat simpl;
    repeat rewrite andb_true_iff;
    intuition.
  eapply flag_eq_eq...
  eapply type_eq_true...
Qed.

Function nodupB g  :=
  match g with
  | [] =>
      true
  | (a, _, _) :: tl =>
      match InB a tl with
      | (_, _, true) =>
          false
      | _ => 
          nodupB tl
      end
  end.

Lemma inB_false_not_In a g f t:
  InB a g = (f, t, false) ->
  In a (domain g) ->
  False.
Proof with eauto.
  introv INB ABS.
  induction g; simpl in *...
  destruct a0 as ([b f1] &t1).
  case_eq (pair_eq a b); introv ABS2;
    rewrite ABS2 in *; inv INB...
  inversion ABS...
  rewrite <-pairEq_neq in ABS2...
Qed.

Hint Constructors NoDup.

Lemma gen_pf g :
  nodupB g = true -> NoDup (domain g).
Proof with eauto using NoDup_nil, inB_false_not_In.
  introv ND.
  functional induction (nodupB g); simpl;
    try discriminate...
  case_eq (snd (InB a tl)); introv EQ.
  destruct ( InB a tl) as ([f t] &b);
    simpl in EQ; subst; contradiction...
  assert (exists f t, InB a tl = (f, t, false))...
  destruct ( InB a tl) as ([f t] &b)...
  exists f, t; simpl in EQ; subst...
  unpack.
  assert (NIN: ~(In a (domain tl)))...
Qed.

Lemma pf_gen g :
  NoDup (domain g) -> nodupB g = true.
Proof with eauto.
  introv ND.
  dependent induction ND...
  assert (g = nil).
  destruct g...
  simpl in *; try destruct p as ([f t] &b);
    try discriminate...
  subst...
  destruct g; try destruct p as ([a f] &t);
    simpl in *; try inv x...
  case_eq (snd (InB a g)); introv EQ.
  assert (exists f1 t1, InB a g = (f1, t1, true))...
  destruct ( InB a g) as ([f2 t2] &b2)...
  exists f2, t2; simpl in EQ; subst...
  unpack; rewrite H0...
  eapply inB_implies_In_2 in H0;
    simpl in H0;
    eapply in_g_in_domain in H0...
  assert (exists f1 t1, InB a g = (f1, t1, false))...
  destruct ( InB a g) as ([f2 t2] &b2)...
  exists f2, t2; simpl in EQ; subst...
  unpack; rewrite H0...
Qed.

Lemma ndb_sng g a fa ta:
  nodupB g = true ->
  nodupB ((a, fa, ta) :: removeEntry a g) = true.
Proof with eauto using pf_gen, gen_pf.
  introv NDB.
  eapply pf_gen,
    no_dup_split_no_dup.no_dup_cons_removeEntry...
Qed.    

Lemma ndb_dbl g a fa ta b fb tb:
  nodupB g = true ->
  a <> b ->
  nodupB ((a, fa, ta)
            :: (b, fb, tb)
            :: removeEntry a
            (removeEntry b g)) = true.
Proof with eauto using pf_gen, gen_pf.
  introv NDB DIFF.
  eapply pf_gen,
    no_dup_split_no_dup.no_dup_cons_removeEntry_app...
Qed.

Function changeVis a (g : typeEnv) :=
  match g with
  | [] => []
  | (b, f, t) :: tl =>
      if pair_eq a b
      then
        (b, vis, t) :: tl
      else
        (b, f, t) :: changeVis a tl
  end.

Lemma changeVis_domain a g:
  domain (changeVis a g) = domain g.
Proof with eauto.
  gen a.
  induction g; intros...
  destruct a as ([b f] &t).
  simpl;
    case_eq (pair_eq a0 b); introv EQ;
    try rewrite EQ; simpl;
    try erewrite IHg...
Qed.  


Lemma ndb_changeVis a g:
  nodupB g = true ->
  nodupB (changeVis a g) = true.
Proof with eauto  using pf_gen, gen_pf, changeVis_domain.
  introv NDB.
  induction g...
  destruct a0 as ([b f] &t).
  case_eq (pair_eq a b); introv EQ;
    simpl;
    try rewrite EQ...
  eapply pf_gen; simpl...
  eapply gen_pf in NDB; simpl in NDB.
  econstructor...
  introv ABS.
  rewrite changeVis_domain in *...
  inv NDB...
  eapply gen_pf, IHg, pf_gen, NoDup_cons_iff...
Qed.

Function changeHid a (g : typeEnv) :=
  match g with
  | [] => []
  | (b, f, t) :: tl =>
      if pair_eq a b
      then
        (b, hid, t) :: tl
      else
        (b, f, t) :: changeHid a tl
  end.

Lemma changeHid_domain a g:
  domain (changeHid a g) = domain g.
Proof with eauto.
  gen a.
  induction g; intros...
  destruct a as ([b f] &t).
  simpl;
    case_eq (pair_eq a0 b); introv EQ;
    try rewrite EQ; simpl;
    try erewrite IHg...
Qed.  

Lemma ndb_changeHid a g:
  nodupB g = true ->
  nodupB (changeHid a g) = true.
Proof with eauto  using pf_gen, gen_pf, changeHid_domain.
  introv NDB.
  induction g...
  destruct a0 as ([b f] &t).
  case_eq (pair_eq a b); introv EQ;
    simpl;
    try rewrite EQ...
  eapply pf_gen; simpl...
  eapply gen_pf in NDB; simpl in NDB.
  econstructor...
  introv ABS.
  rewrite changeHid_domain in *...
  inv NDB...
  eapply gen_pf, IHg, pf_gen, NoDup_cons_iff...
Qed.

Function posB (l : list (name * name)) :=
  match l with
  | [] => true
  | (_, n) :: tl =>
      (0 <? n) && (posB tl)
  end.

Lemma posB_pos s:
  posB s = true ->
  pos s.
Proof with eauto.
  introv POS; unfold pos; introv IN.
  induction s; inv IN...
  simpl in POS; try eapply andb_prop in POS as [K _].
  eapply Nat.leb_le...
  eapply IHs...
  simpl in POS;
    destruct a;
    try eapply andb_prop in POS as [_ K]...
Qed.

Function inB n l :=
  match l with
  | [] => false
  | h :: tl =>
      pair_eq n h || inB n tl
  end.

Lemma inB_In n l :
  inB n l = true ->
  In n l.
Proof with eauto.
  introv INB;
    induction l;
    simpl in *;
    try discriminate;
    eapply orb_true_iff in INB as [K1 | K2];
    try rewrite <-pairEq_eq in *;
    subst...
Qed.

Function inclB l1 l2 :=
  match l1 with
  | [] => true
  | h :: tl =>
      inB h l2 && inclB tl l2
  end.

Lemma inclB_incl l1 l2:
  inclB l1 l2 = true ->
  incl l1 l2.
Proof with eauto using inB_In.
  introv INCL IN;
  induction l1;
    try inv IN;
    simpl in *;
    try eapply andb_prop in INCL as [K1 K2];
  try discriminate...
Qed.

Function nodupb (s : list (name * name))  :=
  match s with
  | [] =>
      true
  | a :: tl =>
      negb(inB a tl) && nodupb tl
  end.

Lemma in_inB:
  forall (n : name * name) (l : list (name * name)),
  In n l -> inB n l = true.
Proof with eauto.
  introv IN;
    induction l;
    try inv IN;
    simpl;
    try eapply orb_true_intro...
  try left;
    try rewrite <-pairEq_eq...
Qed.

Lemma inB_false_nIn:
  forall (n : name * name) (l : list (name * name)),
  inB n l = false -> In n l -> False.
Proof with eauto.
  introv INB ABS.
  eapply in_inB in ABS.
  rewrite ABS in *.
  discriminate.
Qed.

Lemma nodupb_NoDup s:
  nodupb s = true ->
  NoDup s.
Proof with eauto using  inB_false_nIn.
  introv ND.
  induction s; simpl in ND;
    try eapply andb_prop in ND as [K1 K2]...
  rewrite negb_true_iff in *;
  eapply NoDup_cons_iff;
    split...
Qed.  

Definition bothRedexesChange := bool.
(** [elts] is the interpreter of semantics.lts *)
(** [tau_arg] is the payload of the tau *)
(** [b] indicates whether we chose to change both redexes in a comm or close *)
(** or to fire a parallel execution and change only one redex *)
(** [pf] is a dependent proof and is elided in the extraction *)
(** Extraction: interpreter.ml *)
(** Extraction types: interpreter.ml.types *)
Function elts
  (g : typeEnv)
  (p : dproc)
  (act : action)
  (tau_arg : option (name * name))
  (b : bothRedexesChange)
  (pf : nodupB g = true)
  : option (typeEnv * dproc) :=
  match p, act with
    
  | dPar q1 q2, aTau a1 a2 =>
      
      if b
      then
        
        (match tau_arg with
         | Some (b1, b2) =>


             (match nat_pair_eq_dec (a1, a2) (b1, b2) with
              | right diff =>

                  (match InB (a1, a2) g, InB (b1, b2) g with

                   (* lcomL *)
                   | (vis, Chan lin io t, true),
                     (vis, s, true) =>
                       (match tremove s t with
                        | Some r =>
                            let g0 :=
                              removeEntry (a1, a2) (removeEntry (b1, b2) g)
                            in
                            let act1 := aOut a1 a2 b1 b2
                            in
                            let d1 :=
                              (a1, a2, vis, Chan lin out t)
                                :: (b1, b2, vis, s) :: g0
                            in
                            let pf1 :=
                              ndb_dbl g 
                                (a1, a2) vis (Chan lin out t)
                                (b1, b2) vis s pf diff
                            in
                            let act2 := aIn a1 a2 b1 b2
                            in
                            let d2 :=
                              (a1, a2, vis, Chan lin inp t)
                                :: (b1, b2, vis, r) :: g0
                            in
                            let pf2 :=
                              ndb_dbl g 
                                (a1, a2) vis (Chan lin inp t)
                                (b1, b2) vis r pf diff 
                            in
                            (match
                                elts d1 q1 act1 None false pf1,
                                elts d2 q2 act2 None false pf2
                              with
                              | Some (d', q'),
                                Some (d'', q'') =>
                                  if typeEnv_eq
                                       d'
                                       ((a1, a2, vis, Chan lin empty t)
                                          :: (b1, b2, vis, r) :: g0)
                                     &&
                                       typeEnv_eq
                                         d''
                                         ((a1, a2, vis, Chan lin empty t)
                                            :: (b1, b2, vis, s)  :: g0) 
                                  then
                                    Some (d'', dPar q' q'')
                                  else
                                    raise
                              | _, _ => raise
                              end)
                        | _ => raise
                        end)
                         


                   (* lclsL *)
                   | (vis, Chan lin io t, true),
                     (hid, s, true) =>
                       (match tremove s t with
                        | Some r =>
                            let g0 :=
                              removeEntry (a1, a2) (removeEntry (b1, b2) g)
                            in
                            let act1 := aOut a1 a2 b1 b2
                            in
                            let d1 :=
                              (a1, a2, vis, Chan lin out t)
                                :: (b1, b2, hid, s) :: g0
                            in
                            let pf1 :=
                              ndb_dbl g 
                                (a1, a2) vis (Chan lin out t)
                                (b1, b2) hid s pf diff
                            in
                            let act2 := aIn a1 a2 b1 b2
                            in
                            let d2 :=
                              (a1, a2, vis, Chan lin inp t)
                                :: (b1, b2, ill, r) :: g0
                            in
                            let pf2 :=
                              ndb_dbl g 
                                (a1, a2) vis (Chan lin inp t)
                                (b1, b2) ill r pf diff
                            in
                            (match
                                elts d1 q1 act1 None false pf1,
                                elts d2 q2 act2 None false pf2
                              with
                              | Some (d', q'),
                                Some (d'', q'') =>
                                  if typeEnv_eq
                                       d'
                                       ((a1, a2, vis, Chan lin empty t)
                                          :: (b1, b2, vis, r) :: g0)
                                     &&
                                       typeEnv_eq
                                         d''
                                         ((a1, a2, vis, Chan lin empty t)
                                            :: (b1, b2, vis, s)  :: g0) 
                                  then
                                    let d''' :=
                                      ((a1, a2, vis, Chan lin empty t)
                                         :: (b1, b2, hid, s)  :: g0)
                                    in
                                    Some (d''', (dNu b1 b2 (dPar q' q'')))
                                  else
                                    raise
                              | _, _ => raise
                              end)
                        | _ => raise
                        end)


                   (* ucomL *)
                   | (vis, Chan un io t, true),
                     (vis, s, true) =>
                       (match tremove s t with
                        | Some r =>
                            let g0 :=
                              removeEntry (b1, b2) g
                            in
                            let act1 := aOut a1 a2 b1 b2
                            in
                            let pf1 :=
                              ndb_sng g (b1, b2) vis s pf
                            in
                            let act2 := aIn a1 a2 b1 b2
                            in
                            let d2 :=
                              (b1, b2, vis, r) :: g0
                            in
                            let pf2 :=
                              ndb_sng g (b1, b2) vis r pf
                            in
                            (match
                                elts g q1 act1 None false pf,
                                elts d2 q2 act2 None false pf2
                              with
                              | Some (d', q'),
                                Some (d'', q'') =>
                                  (match InB (a1, a2) d'',
                                     InB (b1, b2) d'' with
                                   | (vis, ta, true), (vis, tb, true) =>       
                                       if typeEnv_eq
                                            d'
                                            ((b1, b2, vis, r) :: g0)
                                          && type_eq ta (Chan un io t)
                                          && type_eq tb s
                                       then
                                         Some (d'', dPar q' q'')
                                       else
                                         raise
                                   | _, _ =>
                                       raise
                                   end)
                              | _, _ =>
                                  raise
                              end)
                        | _ => raise
                        end)


                   (* uclsL *)
                   | (vis, Chan un io t, true),
                     (hid, s, true) =>
                       (match tremove s t with
                        | Some r =>
                            let g0 :=
                              removeEntry (b1, b2) g
                            in
                            let act1 := aOut a1 a2 b1 b2
                            in
                            let act2 := aIn a1 a2 b1 b2
                            in
                            let d2 :=
                              (b1, b2, ill, r) :: g0
                            in
                            let pf2 :=
                              ndb_sng g (b1, b2) ill r pf
                            in
                            (match
                                elts g q1 act1 None false pf,
                                elts d2 q2 act2 None false pf2
                              with
                              | Some (d', q'),
                                Some (d'', q'') =>
                                  (match InB (a1, a2) d'',
                                     InB (b1, b2) d'' with
                                   | (vis, ta, true), (vis, tb, true) =>       
                                       if typeEnv_eq
                                            d'
                                            ((b1, b2, vis, r) :: g0)
                                          && type_eq ta (Chan un io t)
                                          && type_eq tb s
                                       then
                                         let d''' :=
                                           (b1, b2, hid, tb)
                                             :: removeEntry (b1, b2) d''
                                         in
                                         Some (d''', dNu b1 b2 (dPar q' q''))
                                       else
                                         raise
                                   | _, _ =>
                                       raise
                                   end)
                              | _, _ =>
                                  raise
                              end)
                        | _ => raise
                        end)
                   |_, _ => raise
                   end)


              | left _ =>
                  raise
              end)
         (* sumbool *)
               
         | _ => raise
         end)
      else
        raise
          
  | dPar q1 q2, _ =>
      match elts g q1 act tau_arg false pf with
      | Some (d', q') =>
          Some (d', dPar q' q2)
      | _ => raise
      end
        
  | dOut a1 a2 b1 b2 q,
    aOut c1 c2 d1 d2 =>
      if pair_eq (a1, a2) (c1, c2) &&
           pair_eq (b1, b2) (d1, d2)
      then
        match InB (a1, a2) g, InB (b1, b2) g with

        (* lOut *)
        | (vis, Chan lin out t, true),
          (vis, s, true) =>
            match tremove s t with
            | Some r =>
                let d :=
                  (a1, a2, vis, Chan lin empty t)
                    :: (b1, b2, vis, r)
                    :: removeEntry (a1, a2)
                    (removeEntry (b1, b2) g)
                in
                Some (d, q)
            | _ => raise
            end


        (* uOut *)
        | (vis, Chan un pl t, true),
          (vis, s, true) =>
            if  pol_eq pl out || pol_eq pl io
            then
              match tremove s t with
              | Some r =>
                  let d :=
                    (b1, b2, vis, r)
                      :: removeEntry (b1, b2) g
                  in
                  Some (d, q)
              | _ => raise
              end
            else
              raise
        | _, _ => raise
        end
      else
        raise
  | dInp a1 a2 x1 x2 q,
    aIn c1 c2 b1 b2 =>
      if pair_eq (a1, a2) (c1, c2)
      then
        match InB (a1, a2) g, InB (b1, b2) g with

        (* lIn *)  
        | (vis, Chan lin inp t, true),
          (f, s, true) =>
            if negb (flag_eq f hid)
            then
              match tplus s t with
              | Some r =>
                  let d :=
                    (a1, a2, vis, Chan lin empty t)
                      :: (b1, b2, vis, r)
                      :: removeEntry (a1, a2)
                      (removeEntry (b1, b2) g)
                  in
                  Some (d, pmap q x1 x2 b1 b2)
              | _ => raise
              end
            else
              raise


        (* uIn *)  
        | (vis, Chan un pl t, true),
          (f, s, true) =>
            if  (pol_eq pl inp || pol_eq pl io)
                && negb (flag_eq f hid)
            then
              match tplus s t with
              | Some r =>
                  let d :=
                    ((b1, b2, vis, r)
                       :: removeEntry (b1, b2) g)
                  in
                  Some (d, pmap q x1 x2 b1 b2)
              | _ => raise
              end
            else
              raise
        | _, _ => raise
        end
      else
        raise

  | dBang a1 a2 x1 x2 q,
    aIn c1 c2 b1 b2 =>
      if pair_eq (a1, a2) (c1, c2)
      then
        match InB (a1, a2) g, InB (b1, b2) g with
        | (vis, Chan un pl t, true),
          (f, s, true) =>
            if  (pol_eq pl inp || pol_eq pl io)
                && negb (flag_eq f hid)
            then
              match tplus s t with
              | Some r =>
                  let pfg := gen_pf g pf
                  in
                  let rq := dep_relabel q (domain g) pfg
                  in
                  let d :=
                    (newEntries g (secLabs rq) (max (domain g)))
                      ++ ((b1, b2, vis, r)
                            :: removeEntry (b1, b2) g)
                  in
                  Some (d, dPar
                             (pmap q x1 x2 b1 b2)
                             (dBang a1 a2 x1 x2 rq))
              | _ => raise
              end
            else
              raise
        | _, _ => raise
        end
      else
        raise

  | dNu b1 b2 q, aOut a1 a2 c1 c2 =>
      if pair_eq (b1, b2) (a1, a2)
      then
        raise
      else
        if pair_eq (b1, b2) (c1, c2)
        then

          (* open *)
          match InB (b1, b2) g with
          | (hid, t, true) =>
              let d1 :=
                ((b1, b2, vis, t)
                   :: removeEntry (b1, b2) g)
              in
              let pf1 :=
                ndb_sng g (b1, b2) vis t pf 
              in
              
              elts d1 q act None false pf1
          | _ => raise
          end

        else
          
          (* hide *)
          match InB (b1, b2) g with
          | (hid, _, true)=>

              let sl := secLabs p
              in
              let dg := domain g
              in
              if inclB sl dg &&
                   posB sl &&
                   nodupb sl &&
                   (max sl <=? max dg)
              then
                let pf1 := ndb_changeVis (b1, b2) g pf
                  in
                  match 
                    elts (changeVis (b1, b2) g) q act None false pf1
                  with
                  | Some (g2, q') =>
                      match InB (b1, b2) g2 with
                      |(vis, _, true) =>
                         Some (changeHid (b1, b2) g2, dNu b1 b2 q')
                      | _ => raise
                      end
                  | _ => raise
                  end

              else
                raise
                  
              | _ => raise
                end
            
            
            
  | _, _ => raise
  end.


Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Constant app  => "(@)".
Extract Constant andb  => "(&&)".
Extract Constant negb => "not".
Extract Constant Nat.ltb  => "(<)".
Extract Constant pair_eq => "(=)".
Extract Constant nodup => "fun l -> match l with | [] -> [] | h :: tl -> let l' = nodup tl in if not @@ List.mem h l' then h :: l' else l'".
Extract Inductive prod => "(*)"  [ "(,)" ].
Set Extraction Optimize.
Extraction Implicit elts [6].
Unset Extraction SafeImplicits.

(** Output of extraction: interpreter.ml *)
(** Types of extraction: interpreter.ml.types *)
Recursive Extraction elts.

Functional Scheme elts_ind := Induction for elts Sort Prop.      
Hint Constructors lts.

Lemma changeVis_app g h1 h2 b1 b2 t:
  NoDup (domain g) ->
  g = h1 ++ (b1, b2, hid, t) :: h2 ->
  changeVis (b1, b2) g =
    h1 ++ (b1, b2, vis, t) :: h2.
Proof with eauto.
  introv ND EQ. subst.
  induction h1; simpl;
    try rewrite pairEq_eq_true;
    try destruct a as  ([c f1] &t1)...
  case_eq (pair_eq (b1, b2) c); introv EQ;
    try rewrite <-pairEq_eq in EQ; subst.
  simpl in ND; rewrite domain_distr in ND;
    simpl in ND;
    eapply NoDup_cons_iff in ND; intuition.
  rewrite IHh1...
Qed.

Lemma changeHid_app g h1 h2 b1 b2 t:
  NoDup (domain g) ->
  g = h1 ++ (b1, b2, vis, t) :: h2 ->
  changeHid (b1, b2) g =
    h1 ++ (b1, b2, hid, t) :: h2.
Proof with eauto.
  introv ND EQ. subst.
  induction h1; simpl;
    try rewrite pairEq_eq_true;
    try destruct a as  ([c f1] &t1)...
  case_eq (pair_eq (b1, b2) c); introv EQ;
    try rewrite <-pairEq_eq in EQ; subst.
  simpl in ND; rewrite domain_distr in ND;
    simpl in ND;
    eapply NoDup_cons_iff in ND; intuition.
  rewrite IHh1...
Qed.                                

(** Soundness of the interpreter *)
Theorem elts_sound g p act tau_arg b d q pfb pf:
  elts g p act tau_arg b pfb = Some (d, q) ->
  lts g p act d q pf.
Proof
  with
  eauto
  using
  tplus_type_plus,
    tremove_type_remove,
    pol_eq_eq,
    type_eq_eq,
    flag_eq_eq,
    typeEnv_eq_eq,
    ndb_changeVis,
    ndb_changeHid,
    pf_gen,
    gen_pf.
    
  
  introv EL.
  gen d q.
  functional induction
    (elts g p act tau_arg b pfb)
    using elts_ind;
    intros;
    try inv EL;
    try rewrite <-pairEq_eq in e1;
    try rewrite negb_true_iff in *;
    try inv e1;
    try eapply inB_implies_In_2 in e2;
    try eapply inB_implies_In_2 in e3;
    try eapply inB_implies_In_2 in e4;
    try eapply inB_implies_In_2 in e5;
    try eapply inB_implies_In_2 in e8;
    try eapply inB_implies_In_2 in e9;
     try eapply inB_implies_In_2 in e10;
    try eapply inB_implies_In_2 in e11;
    try eapply inB_implies_In_2 in e12;
    try eapply inB_implies_In_2 in e20;
    try eapply inB_implies_In_2 in e24;
    simpl in *;
    try eapply andb_prop in e20 as (K1 &K2);
    try eapply typeEnv_eq_eq in K1;
    try eapply typeEnv_eq_eq in K2;
    subst;
    try eapply andb_prop in e21 as (K1 &K2);
    try eapply typeEnv_eq_eq in K1;
    try eapply typeEnv_eq_eq in K2;
    subst;
    try eapply andb_prop in e28 as (K1 &K2);
    try eapply andb_prop in K1 as (K1 &K3);
    try eapply typeEnv_eq_eq in K1;
    try eapply type_eq_eq in K2;
    try eapply type_eq_eq in K3;
    subst;
    try eapply andb_prop in e29 as (K1 &K2);
    try eapply andb_prop in K1 as (K1 &K3);
    try eapply typeEnv_eq_eq in K1;
    try eapply type_eq_eq in K2;
    try eapply type_eq_eq in K3;
    subst;
    try discriminate...
  - eapply andb_prop in e11 as (K1 &K2).
    eapply negb_true_iff, flag_eq_false in K2.
    eapply orb_true_iff in K1.
    remember (gen_pf g pf0) as pf1.
    erewrite dep_relabel_rewrite_pf with (pf := pf1) (pf1 := pf)...
    eapply uRin with (pol0 := pl)...
    destruct K1 as [K0 | K1].
    left; try eapply pol_eq_eq...
    right; try eapply pol_eq_eq...
  - eapply uclsL...
    eapply inB_implies_In_2 in e21...
    eapply inB_implies_In_2 in e25...
  - eapply IHo in e17 as K...
    eapply ucomL...
    eapply inB_implies_In_2 in e21...
    eapply inB_implies_In_2 in e25...    
  - rewrite <-pairEq_eq in e2; inv e2...
  - assert (pff := pf0).
    eapply in_split in e3 as (h1 &h2 &EQ).
    assert (ndcv :
             nodupB (changeVis (b1, b2) g) = true)...
    assert (ndcv_pf :
             NoDup (domain  (changeVis (b1, b2) g)))...
    eapply IHo with (pf := ndcv_pf) in e8 as IH.
    clear IHo.
    eapply in_split in e10 as (k1 &k2 &EQ2).
    gen ndcv_pf.
    erewrite changeVis_app, EQ2; intros...
    assert (nd_pf := IH).
    subst.
    try eapply andb_prop in e7 as (K1 &K5);
      try eapply andb_prop in K1 as (K1 &K4);
      try eapply andb_prop in K1 as (K1 &K3).
    eapply lts_no_dup in nd_pf.
    erewrite changeHid_app with (h1 := k1); intros...
    eapply hide...
    rewrite <-pairEq_neq in *.
    econstructor...
    eapply inclB_incl, incl_incl2, incl2_distr  in K1 as [K1 _].
    rewrite domain_distr in *; simpl...
    eauto.
    try eapply nodupb_NoDup;
       rewrite domain_distr in *; simpl...          
    simpl...
    eapply posB_pos in K3.
    eapply incl_pos with (l2 := secLabs q ++ [(b1, b2)])...
    eapply incl_appl...
    eapply nodupb_NoDup, no_dup_iff in K4 as [K4 _]...
    eapply Nat.leb_le,Max.max_app_l in K5.
    rewrite domain_distr in *; simpl in *...
  - eapply flag_eq_false in e12...
  -  try eapply andb_prop in e11 as (K1 &K2).
     eapply orb_true_iff in K1.
     try eapply negb_true_iff, flag_eq_false in K2.
     eapply uIn with (pol0 := pl)...
     destruct K1;
     try rewrite pol_eq_eq in *...
  -  try eapply andb_prop in H0 as (K1 &K2);
       rewrite <-pairEq_eq in *;
       inv K1; inv K2...
  - try eapply andb_prop in H0 as (K1 &K2);
      rewrite <-pairEq_eq in *;
      inv K1; inv K2...
    eapply orb_true_iff in e12.
    eapply uOut with (pol0 := pl)...
     destruct e12;
     try rewrite pol_eq_eq in *...
     Unshelve.
     all:
        try eapply no_dup_split_no_dup.no_dup_cons_removeEntry;
       try eapply no_dup_split_no_dup.no_dup_cons_removeEntry_app;
       try tauto.
Qed.
