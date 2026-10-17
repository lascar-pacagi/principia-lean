# Course 1 — Natural deduction: propositional and first-order logic

Build formulas, give them Boolean semantics, represent derivations, and prove the rules sound.
Then move from a limited proof search to an executable completeness construction and a total
solver that produces a natural-deduction derivation for every tautology.
Then extend the language to first-order terms and quantifiers, interpret it over arbitrary
models, prove the quantifier rules sound, and build a proof-producing bounded search.

| Lesson | What you learn and build |
|---|---|
| [1.1 Syntax](01-syntax/explainer.qmd) | Formula trees, notation, derived connectives, structural induction. |
| [1.2 Semantics](02-semantics/explainer.qmd) | Valuations, evaluation, entailment, finite tables. |
| [1.3 Deduction](03-deduction/explainer.qmd) | Indexed derivation data and introduction/elimination rules. |
| [1.4 Soundness](04-soundness/explainer.qmd) | Induction proving that the rules preserve truth. |
| [1.5 Initial search](05-prover/explainer.qmd) | Typed optional results, fuel, successful searches and missed proofs. |
| [1.6 Completeness](06-completeness/explainer.qmd) | Executable Kalmár construction and elimination of row assumptions. |
| [1.7 Complete solver](07-complete-solver/explainer.qmd) | Certified finite decision procedure, returned proofs, soundness and completeness. |
| [1.8 First-order syntax](08-first-order-syntax/explainer.qmd) | Terms, binding indices, substitution, capture avoidance. |
| [1.9 First-order semantics](09-first-order-semantics/explainer.qmd) | Domains, models, environments, quantifiers, entailment. |
| [1.10 First-order deduction](10-first-order-deduction/explainer.qmd) | Quantifier rules, fresh variables, arbitrary-model soundness. |
| [1.11 First-order search](11-first-order-search/explainer.qmd) | Typed derivations, finite budgets, intermediate pools, growing stages. |
| [1.12 Henkin extensions](12-henkin/explainer.qmd) | Consistency, fresh witnesses, a complete eventual theory. |
| [1.13 General completeness](13-first-order-completeness/explainer.qmd) | Term model, truth lemma, entailment iff existence of a derivation. |

Each lesson has different teaching examples and exercises, hints before worked corrections,
a conclusion, and separate optional skeletons and solutions. Run commands from `course/`:

```bash
make lab C=01-natural-deduction/01-syntax
make test
make test-solver
make test-first-order
make axioms
make reset C=01-natural-deduction DRY_RUN=1
```

Required work controls the lab result. Pending optional work has its own status. Previewing
reset doesn't change files; an actual reset backs up changed learner files first.

The propositional solver has no arbitrary fuel cutoff. `solve` returns either a derivation or a proof
of invalidity. `proveComplete` offers an `Option` interface whose `none` really means there
is no closed derivation. Lean checks the structural recursion that makes the entire pipeline total.

To run the library in a Lean file in this project:

```lean
import Principia.NatDed.Solver
open Principia
open scoped Principia.Form Principia

#eval (solve ((Form.var 0 ⋏ Form.var 1) ⇒ Form.var 0)).isValid
#eval (solve (Form.var 0 ⇒ Form.var 1)).isValid
#eval (proveComplete (Form.var 0 ⋎ ∼Form.var 0)).isSome
```

These display `true`, `false`, and `true`. The positive result stores an actual derivation,
not just its Boolean tag. The implementation uses exhaustive tables and may build large trees;
it is complete for finite classical propositional formulas. The first-order extension is in `Principia.FirstOrder`. `proveFirstOrder` is a convenient
bounded search; `derivationStage` expands its pools as well as depth. Success carries a
sound derivation; failure means unknown. This extension has no built-in equality, and
general first-order semantic completeness is proved in lessons 1.12–1.13. Eventual success of
the particular bounded search implementations remains a separate, unproved property.
