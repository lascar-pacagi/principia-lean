# 2.9 — General completeness of first-order resolution

Read the explainer, work the required skeleton, then consult hints and corrections. Optional
exercises have a separate skeleton, solution, and lab status.

```bash
make lab C=02-resolution/09-first-order-completeness
make test-first-order
make test
make axioms
make explainer C=02-resolution/09-first-order-completeness
make reset C=02-resolution/09-first-order-completeness DRY_RUN=1
```

The explicit resolution calculus is sound and refutation-complete for arbitrary finite first-order clause sets. All substitution instances and the canonical term model establish the general result without assuming MGU completeness of the bounded unifier. Completeness of a calculus, completeness of its search strategy, and correctness of a formula-to-clause compiler are separate claims.
