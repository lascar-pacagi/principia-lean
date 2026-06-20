# 03-deduction — natural deduction as a data type

**Objective.** Define the provability relation `Γ ⊢ φ` as an **inductive type whose constructors are the
inference rules** of `04-logic §2` — so a *proof* becomes a *value*, a tree you build with the rules.
The `raa` rule makes the system **classical**. You'll hand-build four derivations, culminating in
**Peirce's law**. This is **slice 1.3**; `Deriv` graduates into `Principia.NatDed.Basic`.

**Prerequisites.** Slice 1.1 (`Form`), and `04-logic` (the inference rules on paper).

**The rung.** Single rung — the `Deriv` type is *given*; you construct four derivations.

## Definition of done

- [ ] `make lab C=01-natural-deduction/03-deduction` goes red → green.
- [ ] `make test` stays green; `make axioms` clean.

## A note on difficulty

Building derivation *terms* by hand is fiddly — you must name the formula each `ax` (assumption) proves,
and the formula each *elimination* discards. That friction is the whole reason **slice 1.5 builds a
prover** to do this search for us. Embrace the struggle here; you're feeling the problem the prover solves.

## Run

```bash
make lab C=01-natural-deduction/03-deduction
make explainer C=01-natural-deduction/03-deduction
```
