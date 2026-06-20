# 01-naturals — build ℕ from Peano, prove its addition laws

**Objective.** Build the natural numbers from *nothing* — two constructors — define addition, and prove
its core laws (`zero_add`, `succ_add`, `add_comm`, `add_assoc`) by **induction**. This is our local
mirror of the Natural Number Game's *Addition World*, and it drills the four workhorse tactics: `rfl`,
`rw`, `induction`, `simp`.

**Prerequisites.** `00-setup` (the loop; `rfl`, `rw`, a first `induction`).

**The rung.** Single rung — the `MyNat` type and `add` are *given*; you prove six theorems.

**Why build our own `MyNat`?** If we used Lean's built-in `Nat`, every law below would already be in
the library and `simp`/`omega` would close them instantly — you'd learn nothing. Building the numbers
from scratch means the laws are genuinely *unproved*, and you earn each one.

## Definition of done

- [ ] `make lab C=00-foundations/01-naturals` goes red → green (all six `sorry`s discharged).
- [ ] `make test` stays green.
- [ ] `make axioms` clean (`add_comm`, `add_assoc` depend on no axioms).

## Run

```bash
make lab C=00-foundations/01-naturals      # RED → GREEN as you prove the six laws
make explainer C=00-foundations/01-naturals
```

Read `explainer.qmd` (or `explainer.html` / `explainer.pdf`) first.
