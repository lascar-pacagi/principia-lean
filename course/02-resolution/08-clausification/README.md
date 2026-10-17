# 2.8 — Automatic clausification and Skolem functions

Read the explainer, work the required skeleton, then consult hints and corrections. Optional
exercises have a separate skeleton, solution, and lab status.

```bash
make lab C=02-resolution/08-clausification
make test-first-order
make test
make axioms
make explainer C=02-resolution/08-clausification
make reset C=02-resolution/08-clausification DRY_RUN=1
```

The complete executable conversion preserves satisfiability: model expansion interprets the fresh symbols, and model recovery reconstructs the original satisfying environment. NNF, Skolemization, variable allocation, and matrix-to-CNF are connected by general proofs. A resolution refutation therefore certifies the original entailment directly. Finite-model regressions provide additional checks of dependency and free-variable behavior.
