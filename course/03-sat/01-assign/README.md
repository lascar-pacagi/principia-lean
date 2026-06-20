# 01-assign — assignments and the `assign` operation

**Objective.** Lay the groundwork for a SAT solver: the operation `assign cnf l` that commits to making a
literal `l` true and simplifies the clause set, plus the invariant that makes search work — `assign`
**preserves satisfiability** (`sat_of_assign`). This is **slice 3.1** of Course 3; it reuses Course 2's
clause representation (`Resolution.Cnf`) and graduates into `Principia.Sat.Basic`.

**Prerequisites.** Course 2's `Resolution.Cnf`/`Rule` (`Lit`, `Clause`, `Cnf`, `eval`, `Lit.neg`).

**The rung.** Single rung — `assign` is *given*; you prove `eval_of_erase` and `sat_of_assign`.

## Definition of done

- [ ] `make lab C=03-sat/01-assign` goes red → green.
- [ ] `make test` stays green; `make axioms` clean.

## Run

```bash
make lab C=03-sat/01-assign
make explainer C=03-sat/01-assign
```

Next slice: **3.2 — DPLL** (a real solver: simplify-and-branch, returning a model).
