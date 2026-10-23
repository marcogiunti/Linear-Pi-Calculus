# Soundness of Typed Transitions in the Linear Pi Calculus

## Software prerequisite
The repository compiles with Rocq 9.2 (with the Rocq standard library 9.2).

```
opam switch create rocq-9.2 ocaml-base-compiler.5.3.0
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-core.9.2.0 rocq-stdlib.9.2.0
```

The development was originally written for Coq 8.8.2. [compat.v](compat.v) restores the
Coq 8.8 behaviour that the proofs rely on (the default solver of `intuition`, the hints
registered by the `Omega` library, and a few lemma names removed from the standard library).

A docker artefact of a previous (Coq 8.8.2) version of the repository can be found at [Zenodo](https://doi.org/10.5281/zenodo.13734439);
the artefact does not include the interpreter and [Barendregt's preservation result](barendregt.v).

## Compilation
The compilation is done by executing the command below, and can take up to 45 minutes.

```
make
```

## Evaluation
The repository does not contain axioms or admissions. It does contain two parameters to rule out divergent defining equations of
the form T = p[T]^m and P = u!v.P .
```
Parameter nonRecTypes: (∀ m p t, t = Chan m p t → False) ∧
(∀ m m1 m2 p p1 p2 t, Chan m1 p1 t = Chan m p (Chan m2 p2 t) → False).
Parameter nonDivergentProcesses : ∀ g p a g’ nd_pf, ¬ lts g p a g’ p nd_pf.
```

A successful compilation (`make`) indicates that all Lemmas, Propositions, Theorems and Corollaries are Qed by Rocq 9.2.

In addition, you can execute `make validate`, which should return the following output.

```coq
CONTEXT SUMMARY
===============

* Theory: Set is predicative
  
* Theory: Rewrite rules are not allowed
  
* Axioms:
    SR.LibTactics.skip_axiom
    SR.semantics.nonRecTypes
    Stdlib.Logic.ProofIrrelevance.proof_irrelevance
    SR.LibTactics.inj_pair2
    Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep
    Stdlib.Logic.Eqdep.Eq_rect_eq.eq_rect_eq
    Stdlib.Logic.Classical_Prop.classic
    SR.lts_payload_un_inp.nonDivergentProcesses
  
* Constants/Inductives relying on type-in-type: <none>
  
* Constants/Inductives relying on unsafe (co)fixpoints: <none>
  
* Inductives whose positivity is assumed: <none>
```

## Structure
* [linear_pi.v](linear_pi.v) contains the Subject reduction theorem (Theorem sr)
* [interpreter.v](interpreter.v)  contains the interpreter and the code for its extraction in OCaml
* [interpreter.ml](interpreter.ml) contains the extraction in OCaml
* [interpreter.ml.types](interpreter.ml.types) contains the type and values of [interpreter.ml](interpreter.ml)
* [pi_syntax.v](pi_syntax.v) contains the syntax of the language
* [semantics.v](semantics.v) contains the semantics of the language
* [type_system.v](type_system.v) contains the type algebra of the language
* [type_system_rules.v](type_system_rules.v) contains the type system enforcing linearity
* [compat.v](compat.v) contains the compatibility layer for Rocq 9.2
* [CpdtTactics.v](CpdtTactics.v) contains tactics written by Adam Chlipala
* [LibTactics.v](LibTactics.v) contains tactics written by Arthur Chargueraud
* The remaining `*.v` files contain the preliminary results needed by the Subject reduction theorem (Theorem sr)
