# Soundness of Typed Transitions in the Linear Pi Calculus

## Software prerequisite
The repository compiles with Coq 8.8.2. We discourage attempts to compile the project with versions different from 8.8.2.


```
opam switch create STTLP 4.09.0
opam pin add coq 8.8.2
```

## Hardware prerequisite
The required software configuration cannot be installed in machines using  ARM-based processors (e.g. Apple computers using M-series chips). 

In such situations, we recommend to install a virtual machine (e.g. [VirtualBox](https://www.virtualbox.org/)) with [Ubuntu](https://ubuntu.com/#download-ubuntu), to install [opam](https://opam.ocaml.org/),
and to follow the instructions above.

Alternatively, a docker artefact of a previous version of the repository can be found at  [Zenodo](https://doi.org/10.5281/zenodo.13734439);
the artefact does not include the interpreter and [Barendregt's preservation result](barendregt.v).


## Compilation
The compilation is done by executing the command below, and can take up to 30 minutes.

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

A successful compilation (`make`) indicates that all Lemmas, Propositions, Theorems and Corollaries are Qed by Coq 8.8.2.

In addition, you can execute `make validate`, which should return the following output.

```coq
CONTEXT SUMMARY
===============

* Theory: Set is predicative
  
* Axioms:
    SR.LibTactics.skip_axiom
    SR.semantics.nonRecTypes
    Coq.Logic.ProofIrrelevance.proof_irrelevance
    Coq.Logic.FunctionalExtensionality.functional_extensionality_dep
    SR.LibTactics.inj_pair2
    Coq.Logic.Classical_Prop.classic
    Coq.Logic.JMeq.JMeq_eq
    Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq
    SR.lts_payload_un_inp.nonDivergentProcesses
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
* [CpdtTactics.v](CpdtTactics.v) contains tactics written by Adam Chlipala
* [LibTactics.v](LibTactics.v) contains tactics written by Arthur Chargueraud
* The remaining `*.v` files contain the preliminary results needed by the Subject reduction theorem (Theorem sr)
