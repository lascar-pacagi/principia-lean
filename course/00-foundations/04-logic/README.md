# 04-logic — natural deduction, classical reasoning, and truth tables

**Objective.** Read a natural-deduction rule and a whole proof tree; distinguish building evidence
from using it; practice excluded middle and proof by contradiction. Interpret propositional formulas
under Boolean valuations and understand what soundness and classical completeness relate.

**Prerequisites.** `02-propositions` (logical connectives, `have`, and tactics) and `03-recursion`
(inductive data, recursive functions, and induction).

The teaching examples are different from the required exercises. Read the lesson first,
try the exercises, consult the graduated hints if needed, then read the worked corrections.
The conclusion separates proof-system completeness from the limits of a particular search program.

## Exercises and checks

- `Skeleton.lean`: four required classical proofs and a truth-table exercise with two Lean statements.
- `Solution.lean`: verified answers; explanations in §8.
- `optional/Skeleton.lean`: two additional exercises, reported separately by the lab.
- `optional/Solution.lean`: verified optional answers; explanations in §10.

```bash
make lab C=00-foundations/04-logic
make test
make axioms
make explainer C=00-foundations/04-logic
```

The lab reports required success in green and unfinished optional work in yellow when terminal
colors are available. Required work determines the exit status. `make test` checks all solution
files, including the optional answers. The axiom audit rejects unfinished proofs outside learner
skeletons, ad-hoc axiom declarations, and reported `sorryAx` dependencies.

Preview a reset of this lesson's required and optional exercises:

```bash
make reset C=00-foundations/04-logic DRY_RUN=1
```

Remove `DRY_RUN=1` to reset, saving backups of changed files.

## Definition of done

- [ ] Required lab passes with no remaining `sorry`.
- [ ] Read the proof states and explain where each introduced hypothesis gets its type.
- [ ] Distinguish `Γ ⊢ φ` from `Γ ⊨ φ`, and explain the classical scope of completeness.
- [ ] `make test` and `make axioms` pass.
- [ ] Optional: both additional exercises pass and their axiom reports are understood.

Read `explainer.qmd`, or the rendered `explainer.html` / `explainer.pdf`.
