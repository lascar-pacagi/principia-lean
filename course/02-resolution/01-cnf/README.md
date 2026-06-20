# 01-cnf — clauses, CNF, and conversion

**Objective.** Lay resolution's groundwork: **literals**, **clauses** (disjunctions), and **CNF** (clause
sets / conjunctions), with their semantics; a `toCnf` conversion from `Form`; and the proof that it
**preserves meaning**. The payoff is the bridge `Tautology φ ↔ (toCnf false φ).Unsat` — *to prove `φ`,
refute the clauses of `∼φ`* — which is what resolution will do. This is **slice 2.1** of Course 2; code
graduates into `Principia.Resolution.Cnf`.

**Prerequisites.** Course 1's `Logic` (`Form`, `eval`, `Tautology`); and `03-recursion` (induction over
formulas), `02-semantics` (truth tables).

**The rung.** Single rung — the structures, semantics, plumbing lemmas, `distribute` (+ `distribute_eval`),
and `toCnf` are *given*; you prove `toCnf_eval` (conversion preserves truth) and `taut_iff_cnf_unsat`
(the bridge).

## Definition of done

- [ ] `make lab C=02-resolution/01-cnf` goes red → green.
- [ ] `make test` stays green; `make axioms` clean.

## Run

```bash
make lab C=02-resolution/01-cnf
make explainer C=02-resolution/01-cnf
```

Next slice: **2.2 — the resolution rule** (refutations as derivations of the empty clause).
