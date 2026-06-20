# 02-rule — the resolution rule and refutations

**Objective.** Define the **resolution rule** — from a clause with literal `l` and another with `∼l`,
derive the **resolvent** — and **refutations** (`Refut S c`): resolution derivations of a clause from a
clause set, the empty clause `□` being the goal. You'll build two refutations by hand (echoing the
hand-built `Deriv`s of slice 1.3). This is **slice 2.2**; code graduates into `Principia.Resolution.Rule`.

**Prerequisites.** Slice 2.1 (`Lit`/`Clause`/`Cnf`); slice 1.3 (building derivations by hand).

**The rung.** Single rung — `Lit.neg`, `resolvent`, and the `Refut` type are *given*; you construct two
refutations.

## Definition of done

- [ ] `make lab C=02-resolution/02-rule` goes red → green.
- [ ] `make test` stays green; `make axioms` clean.

## Run

```bash
make lab C=02-resolution/02-rule
make explainer C=02-resolution/02-rule
```

Next slice: **2.3 — the resolution prover** (saturation search for `□`).
