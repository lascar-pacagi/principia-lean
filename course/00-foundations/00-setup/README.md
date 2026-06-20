# 00-setup — your first proofs, and the loop

**Objective.** Confirm your Lean toolchain works and experience the full learn-by-doing loop: take a
`Skeleton.lean` full of `sorry`s to a kernel-checked green, and see the honesty audit run.

**Prerequisites.** None. This is the very first concept.

**The rung.** Single rung — three tiny proofs (a logic one, an arithmetic one, a first induction).

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
