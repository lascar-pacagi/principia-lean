# Course 1 — A complete propositional prover

Build formulas, give them Boolean semantics, represent derivations, and prove the rules sound.
Then move from a limited proof search to an executable completeness construction and a total
solver that produces a natural-deduction derivation for every tautology.

| Lesson | What you learn and build |
|---|---|
| [1.1 Syntax](01-syntax/explainer.qmd) | Formula trees, notation, derived connectives, structural induction. |
| [1.2 Semantics](02-semantics/explainer.qmd) | Valuations, evaluation, entailment, finite tables. |
| [1.3 Deduction](03-deduction/explainer.qmd) | Indexed derivation data and introduction/elimination rules. |
| [1.4 Soundness](04-soundness/explainer.qmd) | Induction proving that the rules preserve truth. |
| [1.5 Initial search](05-prover/explainer.qmd) | Typed optional results, fuel, successful searches and missed proofs. |
| [1.6 Completeness](06-completeness/explainer.qmd) | Executable Kalmár construction and elimination of row assumptions. |
| [1.7 Complete solver](07-complete-solver/explainer.qmd) | Certified finite decision procedure, returned proofs, soundness and completeness. |

Each lesson has different teaching examples and exercises, hints before worked corrections,
a conclusion, and separate optional skeletons and solutions. Run commands from `course/`:

```bash
make lab C=01-natural-deduction/01-syntax
make test
make test-solver
make axioms
make reset C=01-natural-deduction DRY_RUN=1
```

Required work controls the lab result. Pending optional work has its own status. Previewing
reset doesn't change files; an actual reset backs up changed learner files first.

The final solver has no arbitrary fuel cutoff. `solve` returns either a derivation or a proof
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
it is complete for finite classical propositional formulas. First-order logic is a separate extension.
