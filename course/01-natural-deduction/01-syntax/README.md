# 01-syntax — the language of formulas

**Objective.** Begin the prover by defining its raw material: **propositional formulas** as an inductive
type `Form`, with readable notation and a `size` measure. You'll prove two small structural facts by
induction over the new type — the same method as `03-recursion`, now on the syntax we'll prove things
about all course. This is **slice 1.1** of Course 1; its code graduates into `Principia.Logic.Syntax`.

**Prerequisites.** All of Course 0 — especially `03-recursion` (inductive types, structural induction)
and `04-logic` (what these connectives *mean*).

**The rung.** Single rung — the type, notation, derived connectives, and `size` are *given*; you prove
`size_pos` and `size_neg`.

## Definition of done

- [ ] `make lab C=01-natural-deduction/01-syntax` goes red → green.
- [ ] `make test` stays green; `make axioms` clean.

## Run

```bash
make lab C=01-natural-deduction/01-syntax
make explainer C=01-natural-deduction/01-syntax
```

Read `explainer.qmd` first. Next slice: **1.2 — semantics** (`eval`, `⊨`, a truth-table checker).
