# 00-setup — your first proofs, and the loop

**Objective.** Confirm your Lean toolchain works and experience the full learn-by-doing loop: take a
`Skeleton.lean` full of `sorry`s to a kernel-checked green, and see the honesty audit run.

**Prerequisites.** None. This is the very first concept.

**The rung.** Single rung — three tiny proofs (a logic one, an arithmetic one, a first induction).
The lab applies the lesson to new goals: rearranging a nested conjunction (`and_reorder`), comparing
two concrete sums (`sum_lt`), and proving `1 + n = n + 1` (`one_add'`).

**Optional practice.** `optional/Skeleton.lean` contains the three exercises from §11. Their answer
key is `optional/Solution.lean`. They cover swapping an "or," addition by zero on the right, and
proving associativity of addition by induction. The same `make lab` command checks both sets: required failures are
red, unfinished optional exercises are yellow, and completed sets are green. Optional work never
changes whether the required lab passes. `make test` checks both solution files, and `make axioms`
audits their proofs.

## Definition of done

- [ ] `make lab C=00-foundations/00-setup` is **red** on the untouched skeleton, **green** once you
      replace all three `sorry`s.
- [ ] `make test` is green (the solutions kernel-check).
- [ ] `make axioms` is clean (the keystones depend on no forbidden axioms).

## Run

```bash
make setup                              # build the toolchain + library (once)
make test                               # should be GREEN
make lab C=00-foundations/00-setup      # RED → GREEN as you prove the three goals
make axioms                             # honesty audit
```

Read `explainer.qmd` first if anything is unfamiliar.
