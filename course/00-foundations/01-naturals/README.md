# 01-naturals — build ℕ from Peano, prove its addition laws

**Objective.** Build the natural numbers from *nothing* — two constructors — define addition, and prove
its core laws (`succ_add`, `add_comm`, `add_assoc`) by **induction**, after a worked proof of `zero_add`. This is our local
mirror of the Natural Number Game's *Addition World*, and it drills the four workhorse tactics: `rfl`,
`rw`, `induction`, `simp`.

**Prerequisites.** `00-setup` (the loop; `rfl`, `rw`, a first `induction`).

**The rung.** Single rung — `MyNat`, `add`, and the three worked results are *given*; you prove
`succ_add`, `add_comm`, and `add_assoc`. Their full corrections appear after the exercises and hints.

**Why build our own `MyNat`?** It lets us follow the proofs from the definition of addition, practice
induction, and see how later laws reuse earlier ones. Lean's built-in `Nat` already provides these
theorems, which are useful when working with arithmetic in other projects.

**Optional practice.** `optional/Skeleton.lean` supplies the definitions and established laws for
two further exercises; `optional/Solution.lean` is the answer key. The same `make lab` command
reports their progress separately, in yellow while unfinished. They do not prevent the required
lab from passing. `make reset C=00-foundations/01-naturals` resets both exercise sets.

## Definition of done

- [ ] `make lab C=00-foundations/01-naturals` goes red → green (all three `sorry`s discharged).
- [ ] `make test` stays green.
- [ ] `make axioms` clean (`add_comm`, `add_assoc` depend on no axioms).

## Run

```bash
make lab C=00-foundations/01-naturals      # RED → GREEN as you prove the three laws
make explainer C=00-foundations/01-naturals
```

Read `explainer.qmd` (or `explainer.html` / `explainer.pdf`) first.
