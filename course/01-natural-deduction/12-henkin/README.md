# 1.12 — Consistency, fresh witnesses, and Henkin extensions

Read the explainer, work the required skeleton, then consult hints and corrections. Optional
exercises have a separate skeleton, solution, and lab status.

```bash
make lab C=01-natural-deduction/12-henkin
make test-first-order
make test
make axioms
make explainer C=01-natural-deduction/12-henkin
make reset C=01-natural-deduction/12-henkin DRY_RUN=1
```

A Henkin extension preserves consistency, decides every formula eventually, and supplies witnesses. Its stages are finite; its eventual theory is not produced by an executable consistency decider. Freshness and a common finite stage justify the proof manipulations used in the construction.
