# 1.13 — General completeness of first-order natural deduction

Read the explainer, work the required skeleton, then consult hints and corrections. Optional
exercises have a separate skeleton, solution, and lab status.

```bash
make lab C=01-natural-deduction/13-first-order-completeness
make test-first-order
make test
make axioms
make explainer C=01-natural-deduction/13-first-order-completeness
make reset C=01-natural-deduction/13-first-order-completeness DRY_RUN=1
```

Every semantic consequence of a finite context has a finite natural-deduction derivation, and every derivation is semantically sound. Henkin extensions and the truth lemma establish the missing general direction. This mathematical existence theorem is distinct from completeness or termination of a particular proof-search implementation.
