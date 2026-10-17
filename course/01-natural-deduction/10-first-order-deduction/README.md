# 1.10 — First-order natural deduction and fresh variables

Read the explainer for concrete examples, proof states, and the exact guarantees of this
first-order component. Required exercises differ from the teaching examples; hints precede
worked corrections. Optional exercises have separate skeletons and solutions.

```bash
make lab C=01-natural-deduction/10-first-order-deduction
make test-first-order
make test
make axioms
make explainer C=01-natural-deduction/10-first-order-deduction
make reset C=01-natural-deduction/10-first-order-deduction DRY_RUN=1
```

Required work determines the lab exit status. Optional placeholders are reported separately.
Actual reset saves backups of changed files. HTML and PDF are rendered beside the source.

## Definition of done

- [ ] Required declarations have no placeholders and the lab passes.
- [ ] Explain the variables, premises, and goal of each inference used.
- [ ] `make test-first-order`, `make test`, and `make axioms` pass.
- [ ] Optional: complete the two additional exercises.

This extension uses first-order predicate logic without built-in equality. Finite search
failure means unknown. Both proof systems now have general completeness theorems (1.12–1.13 and 2.9).
Automatic clausification and its general model-expansion/recovery proofs are in 2.8.
