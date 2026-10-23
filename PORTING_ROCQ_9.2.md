# Porting the development from Coq 8.8.2 to Rocq 9.2

This report records how the mechanisation of *Soundness of Typed Transitions in the Linear
Pi Calculus* was ported from Coq 8.8.2 to Rocq 9.2. It covers the toolchain set-up, the
causes of breakage, the fixes applied, and how the result was validated.

## Outcome

- All 57 `.v` files compile with Rocq 9.2.0 and rocq-stdlib 9.2.0. A clean `make -j8` takes
  about 40 minutes of wall-clock time, most of it spent on `linear_pi.v`.
- No proof was weakened. Nothing was admitted, and no new axioms or parameters were added.
- `make validate` (`rocqchk`) reports the same assumptions as under Coq 8.8.2, except that
  `JMeq_eq` no longer appears: the Rocq 9.2 standard library derives it instead of assuming it.
- The statements of all lemmas and theorems are unchanged. Only proof scripts, imports and
  hint declarations were edited.
- The diff touches 58 files (899 insertions, 909 deletions). This includes the new file
  `compat.v` (36 lines) and the README.

### Assumptions reported by `make validate`

| Coq 8.8.2 | Rocq 9.2 |
|---|---|
| `SR.LibTactics.skip_axiom` | `SR.LibTactics.skip_axiom` |
| `SR.semantics.nonRecTypes` | `SR.semantics.nonRecTypes` |
| `SR.lts_payload_un_inp.nonDivergentProcesses` | `SR.lts_payload_un_inp.nonDivergentProcesses` |
| `SR.LibTactics.inj_pair2` | `SR.LibTactics.inj_pair2` |
| `Coq.Logic.ProofIrrelevance.proof_irrelevance` | `Stdlib.Logic.ProofIrrelevance.proof_irrelevance` |
| `Coq.Logic.FunctionalExtensionality.functional_extensionality_dep` | `Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep` |
| `Coq.Logic.Classical_Prop.classic` | `Stdlib.Logic.Classical_Prop.classic` |
| `Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq` | `Stdlib.Logic.Eqdep.Eq_rect_eq.eq_rect_eq` |
| `Coq.Logic.JMeq.JMeq_eq` | *(no longer an axiom)* |

The `Coq.` → `Stdlib.` prefix change comes from the renaming of the standard library in
Rocq 9.

## 1. Toolchain

A dedicated opam switch was created, so existing switches are untouched:

```
opam switch create rocq-9.2 ocaml-base-compiler.5.3.0
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-core.9.2.0 rocq-stdlib.9.2.0
```

At first, rocq-core 9.2.0 did not appear in the package list. The locally configured `default`
opam repository has a misspelled URL (`https://opam.ocaml.orG`) and was serving a stale index.
Adding a correctly spelled copy of `https://opam.ocaml.org` to the new switch (only) made 9.2.0
visible. The global repository configuration was left as it was.

Rocq 9 replaces `coq_makefile` with `rocq makefile`, and the `Makefile` was updated accordingly.
`_CoqProject` (`-R . SR`) needed no change.

## 2. Method

1. **Dependency order.** The compile order was computed from `rocq dep`. Files were compiled
   one at a time, stopping at the first error. Fixing errors in dependency order matters,
   because a change of behaviour in an early file (for example, a hint that is no longer
   visible) shows up as failures in many later files.
2. **Find root causes before patching.** For each error, the proof state just before the
   failing sentence was inspected. Where the cause was a systematic change of behaviour
   between versions, it was fixed once, globally (Section 3), rather than at every call site.
   To identify these causes, the Coq 8.8.2 standard library sources were downloaded and
   compared with Rocq 9.2's (hint databases, `Omega.v`, `Tauto.v`).
3. **Scripted mechanical rewrites.** Rewrites that are purely syntactic were done by scripts
   that understand comments and proof boundaries, not by blind search-and-replace
   (Section 4).
4. **Minimal local repairs.** The remaining failures were fixed one by one, choosing fixes that
   do not depend on fragile details. For example, the intended hypothesis is named explicitly
   instead of relying on an auto-generated name (Section 5).
5. **Interactive checking of `linear_pi.v`.** This file is a single proof of about 16,000
   lines, and recompiling it after every fix took 5–10 minutes. A persistent `rocq repl -emacs`
   session was driven from a script. It executes the file sentence by sentence, records the
   proof state after each sentence, and after an edit backtracks (`BackTo`) only to the first
   changed sentence. This reduced the turnaround for each fix to seconds. A sentence that stops
   making progress (an `eauto` search that never ends) can be interrupted with SIGINT, which
   then surfaces as an ordinary error at that sentence.
6. **Validation.** Finally, a clean build with `make` and `make validate` (Section 7).

## 3. Behaviour changes fixed globally: `compat.v`

Most breakage did not come from removed syntax. It came from silent changes to proof
automation that the proofs depend on implicitly. These changes are reverted in one place, the
new file `compat.v`. It is loaded with `Require Export` by `header.v`, `operations.v` and
`ListAddOns.v`, through which every project file reaches it.

### 3.1 The default solver of `intuition`

- **Coq 8.8:** `intuition` meant `intuition (auto with *)`, so it searched *all* hint
  databases.
- **Rocq 9.2:** `Init/Tauto.v` defines `Ltac intuition_solver := auto.`, which uses only the
  `core` database.

Hundreds of `intuition` calls (directly, through `crush`, and inside `Proof with`) had relied on
the wider search. Fix:

```coq
Ltac Tauto.intuition_solver ::= auto with *.
```

### 3.2 The hints registered by `Omega`

The library `Omega` was removed in favour of `Lia`. Besides the tactic, Coq 8.8's
`plugins/omega/Omega.v` registered hints in the `zarith` database:

```coq
Hint Extern 10 (_ = _ :>nat) => abstract omega: zarith.
Hint Extern 10 (_ <= _) => abstract omega: zarith.
...
Hint Extern 10 False => abstract omega: zarith.
```

Through `auto with *` (Section 3.1), every `intuition` therefore silently tried `omega` on
arithmetic goals and on `False`. For instance, it closed goals such as `x < x ⊢ False` and
`x2 < 0 ⊢ 0 = x2`. The same eleven `nat` hints are re-registered in `compat.v`, with
`abstract lia` in place of `abstract omega`.

### 3.3 Libraries that `Omega` used to load

`Omega` did `Require Export ZArith_base`, which in turn exported `Arith_base`. So every file that
imported `Omega` also had these libraries' lemma names and `arith` hints in scope. `Lia` does not
load them. `compat.v` does `Require Export ZArith_base Arith_base`.

### 3.4 Lemma names removed from the standard library

They are re-introduced with their **original statements**, so existing proof steps such as
`rewrite`, `specialize` and hint use behave as before:

```coq
Notation beq_nat := Nat.eqb (only parsing).
Lemma beq_nat_refl : forall n, true = beq_nat n n.     (* note: true on the left *)
Lemma beq_nat_true : forall n m, beq_nat n m = true -> n = m.
Notation le_trans := Nat.le_trans (only parsing).
```

### 3.5 Default locality of hints

- **Coq 8.8:** a `Hint` command outside a section, with no locality attribute, was *global*: it
  was active in every file that loaded the module, even indirectly.
- **Rocq 9.2:** the default is `#[export]`: the hint is active only where the module is
  imported directly.

Many proofs used hints declared in modules that are only reached indirectly. For example, `incl`
goals could no longer be closed by `eauto`, and `in_g_in_domain` was missing. A script added
`#[global]` to all 357 project `Hint` commands that appear outside sections. Hints inside
sections are section-local in both versions and were left alone.

The same applies to `Remove Hints`. The three top-level occurrences (`LibTactics.v`,
`split_existential.v`, `lts_payload_un_inp.v`) were marked `#[global]`, so that, as in 8.8, the
removal happens when the module is loaded rather than when it is imported. Without this,
`in_g_in_domain` was removed in places where 8.8 still had it, and an `eapply disjoint_absurd...`
in `tc_premises_5.v` failed.

## 4. Mechanical source rewrites

| Change | Reason | Extent |
|---|---|---|
| `omega` → `lia`, `Omega` → `Lia` | `Omega` was removed | 256 tactic calls, 56 imports |
| `...` → `.` in proofs with no `Proof with` | Rocq 9.2 rejects a useless `...`; Coq 8.8 treated it as `.` | 128 sites in 8 files; a script tracked `Proof with` … `Qed` and skipped comments |
| `#[global] Hint …` | Section 3.5 | 357 hints |
| `#[global] Remove Hints …` | Section 3.5 | 3 |
| `Grab Existential Variables` → `Unshelve` | Command removed | 2 |
| `elimtype False` → `exfalso` | Tactic removed | 3 (CpdtTactics, LibTactics) |
| bare `instantiate` → `idtac` | `instantiate` without arguments was removed; it was a no-op | 2 (LibTactics) |
| `Le.le_n_S` → `le_n_S` | Module `Arith.Le` was removed | 1 (Max.v) |
| `FinFun.Injective(_map_NoDup)` → `Finite.Injective(_map_NoDup)` | Moved to `Lists/Finite.v` | 5 sites |
| `(pol0 := …)` → `(pol := …)` | See Section 5.1 | 7 sites |

## 5. Local proof repairs

### 5.1 Binder names

- **Constructor binders.** In `semantics.v`, the constructors `uIn`, `uOut` and `uRin` quantify
  over a variable `pol` whose name clashes with the type `pol`. Coq 8.8 renamed the binder to
  `pol0`; Rocq 9.2 keeps `pol`. The explicit instantiations `with (pol0 := …)` became
  `with (pol := …)` (interpreter.v, split_existential.v, split_existential_2.v).
- **Induction hypotheses from `dependent induction`.** In Coq 8.8, the generalised variables in
  the induction hypothesis were really renamed (`a1` → `a3`, `t` → `t0`, …). In Rocq 9.2 they
  keep their original names; the renamed versions now appear only when printed. Instantiations
  such as `specialize IHLTS with (a3 := a1) (a4 := a2) (t0 := t)` therefore fail with
  *"No such bound variable a3"*.

  These were repaired with a small tool. An Ltac2 probe lists the real names of the dependent
  binders of the hypothesis. They are zipped, in order, with the names Rocq prints (which match
  Coq 8.8's), and the keys are rewritten. This was applied in split_existential.v (4 sites),
  split_existential_2.v (1), and lts_operations.v (2).

### 5.2 Auto-generated hypothesis names

Changes in how `intuition` and `inversion` introduce hypotheses shifted auto-generated names.
Each repair names the intended hypothesis explicitly:

- `split_not_exists.v`: `assert (flagOf g0 (b1, b2) hid). … inversion H7` became
  `assert (FLHID: …). … inversion FLHID`.
- `linear_pi.v:1290`: `inversion H9. inversion H10; subst...` became
  `destruct H6 as [H10|H10]. inversion H10; subst...` (the membership hypothesis is now `H6`).

### 5.3 Proof search picks a different hypothesis

When several hypotheses fit, `eauto` and `eassumption` sometimes choose a different one than in
Coq 8.8. In particular, the more recently introduced `EXSPLITG0 : tEnv_split g0 w2 g …` is now
chosen instead of `TS2 : tEnv_split g0 g3 g1 …`. The proof then continues with the right shape
but the wrong environment (`g` instead of `g1`). The repair states the intended choice:

| File:line | Fix |
|---|---|
| `split_not_exists.v:2064` | `eapply disjoint_absurd with (1 := DIS2)...` |
| `linear_pi.v:1191, 1848, 2425, 2863` | `erewrite split_max with (g := g1) in MAX0...` |
| `linear_pi.v:6640, 6642, 9871, 9873` | `eapply tsub_un/fsub_vis/fsub_hid with (g := g1) in …` |
| `linear_pi.v:10083` | `eapply typeCheck_no_dup with (pf := pf0)...` |

At two of these sites (`linear_pi.v:6645` and `9876`), the wrong choice did not cause an error
right away. Instead, the later `eapply flag_of_map ...` ran an `eauto` search that never
terminated. The stalled sentences were found with the interactive session described in
Section 2.

### 5.4 Goal order

In two places the goals produced by `eapply` / `Unshelve` come in a different order, so a fixed
sequence of one tactic per goal no longer lines up. Each sequence was replaced by an
order-independent block that tries the same tactics on every goal:

- `tc_prelim.v:860`, and the block after `Unshelve` in `tc_substitution.v:2139`:

  ```coq
  all: try solve [ <tactic used for goal 1> | <tactic used for goal 2> | … ].
  ```

### 5.5 Removed or changed syntax

- `Existential 3 := nat_pair_eq_dec.` (removed) in `no_dup_split_no_dup.v` (2 places) and
  `split_operations.v`. The evar is the decidability argument created by
  `rewrite NoDup_count_occ'`, so it is now supplied at that point:
  `rewrite (NoDup_count_occ' nat_pair_eq_dec)`.
- `exists f, t` no longer parses in `interpreter.v`, where LibTactics' `exists` notations are in
  scope. It was replaced by LibTactics' equivalent `exists f t` (3 places).

## 6. Files changed

- **New:** `compat.v`, `PORTING_ROCQ_9.2.md`.
- **Build:** `Makefile` (`rocq makefile`).
- **Documentation:** `README.md`. Updated: prerequisites, a note on `compat.v`, the expected
  `make validate` output, and the build time. Removed: the obsolete statement that the toolchain
  cannot be installed on ARM machines; the port was carried out on an Apple Silicon Mac.
- **Tactic libraries:** `LibTactics.v`, `CpdtTactics.v` (removed tactics, hint locality).
- **Proof files:** every other `.v` file was touched by at least the `omega` → `lia` rewrite.
  The hand-written repairs are confined to the sites listed in Section 5.

## 7. Validation

```
eval $(opam env --switch=rocq-9.2)
make clean && make -j8      # 57/57 files, exit status 0, ~40 min
make validate               # assumption list shown above
```

## 8. Known leftovers

- Rocq 9.2 prints deprecation warnings that do not affect the build. Examples: the `...`
  terminator itself (deprecated since 9.2), hints that name no database, `Notation` used for
  abbreviations, and loading Stdlib modules without the `From Stdlib` prefix. They were left
  alone to keep the diff to the proof scripts small. They are candidates for a later clean-up,
  which would be needed before these features are removed altogether.
- `compat.v` deliberately reproduces 8.8 behaviour (`auto with *` inside `intuition`, `lia`
  hints in `zarith`). Removing it would require repairing the many proofs that depend on it,
  one by one.
