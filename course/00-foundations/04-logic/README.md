# 04-logic — natural deduction, classical vs constructive, and propositional semantics

**Objective.** Name and understand the system you've been using: **natural deduction** (inference rules
↔ Lean tactics), see the **constructive/classical** boundary (and pay for crossing it, in axioms), and
meet **propositional semantics from zero** — valuations, truth tables, and validity `⊨`. This is the
conceptual ground for Course 1, where we *formalize* a natural-deduction prover and prove it **sound and
complete** with respect to exactly these semantics.

**Prerequisites.** `02-propositions` (the connectives & tactics) and `03-recursion` (syntax/semantics by
induction). 

**The rung.** Single rung — four **classical** theorems (they genuinely need classical logic, so their
`#print axioms` includes `Classical.choice`).

## Definition of done

- [ ] `make lab C=00-foundations/04-logic` goes red → green (all four `sorry`s discharged).
- [ ] `make test` stays green.
- [ ] `make axioms` clean — note these keystones *do* depend on `Classical.choice` (by design; that's the
      lesson). The audit forbids only `sorryAx`, not the accepted classical axioms.

## Run

```bash
make lab C=00-foundations/04-logic
make explainer C=00-foundations/04-logic
```

Read `explainer.qmd` (or `explainer.html` / `explainer.pdf`) first.
