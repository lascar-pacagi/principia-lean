# 1.5 — A first proof search, and its limits

Read the explainer for step-by-step examples and proof states. Teaching examples have different
statements from the exercises. Supporting definitions are supplied in `Skeleton.lean`; full
corrections appear after the hints and in the verified answer keys.

```bash
make lab C=01-natural-deduction/05-prover
make test
make axioms
make explainer C=01-natural-deduction/05-prover
make reset C=01-natural-deduction/05-prover DRY_RUN=1
```

Required exercises determine the lab exit status. Optional exercises have their own skeleton
and solution under `optional/` and a separate pending status. Reset supports both sets and
saves backups before replacing completed bodies.

## Definition of done

- [ ] Required exercises pass without placeholders.
- [ ] Read the correction after trying, and explain each intermediate goal and hypothesis.
- [ ] `make test` and `make axioms` pass.
- [ ] Optional: complete the additional exercises.

Course 1 progresses from formulas and valuations to derivations, soundness, limited search,
executable completeness, and a complete terminating propositional solver in lesson 1.7.
