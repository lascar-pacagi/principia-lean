# Course 2 — Resolution, from propositions to first-order clauses

First study clauses, propositional resolution, saturation, and their semantic guarantees.
Then use Course 1's first-order terms and models to add checked unification, renaming apart,
factoring, and proof-producing first-order resolution.

| Lesson | Focus |
|---|---|
| [2.1 CNF](01-cnf/explainer.qmd) | Connect propositional formulas to clause sets. |
| [2.2 Resolution rule](02-rule/explainer.qmd) | Build resolution derivations and the empty clause. |
| [2.3 Prover](03-prover/explainer.qmd) | Run bounded saturation. |
| [2.4 Soundness](04-soundness/explainer.qmd) | Prove that a refutation rules out a model. |
| [2.5 Completeness](05-completeness/explainer.qmd) | Examine the propositional completeness specification and its scope. |
| [2.6 Unification](06-unification/explainer.qmd) | Compose substitutions and check proposed unifiers. |
| [2.7 First-order resolution](07-first-order-resolution/explainer.qmd) | Freshen variables, factor clauses, and return sound refutations. |
| [2.8 Automatic clausification](08-clausification/explainer.qmd) | NNF, Skolem dependencies, distinct variables, distributive CNF, checked frontend. |
| [2.9 General completeness](09-first-order-completeness/explainer.qmd) | All substitution instances, consistent assignment, canonical term model. |

Before lesson 2.6, complete Course 1 lessons 1.8–1.10. General first-order completeness is
proved for the explicit resolution calculus, including structural weakening and tautologies.
Its finite-budget searches still return unknown on failure. Automatic clausification is
implemented and proved equisatisfiable by same-domain model expansion and recovery, together
with NNF and matrix-CNF correctness. A resolution certificate now directly certifies the original
goal. General ND provability is equivalent to existence of a refutation of the generated clauses.
A most-general-unifier completeness theorem remains separate from these calculus-level results.

Run from `course/`:

```bash
make lab C=02-resolution/06-unification
make test-first-order
make test
make axioms
```

The new lessons include required and optional skeletons, separate solutions, hints, and
worked corrections. Pending optional work does not fail completed required work.
