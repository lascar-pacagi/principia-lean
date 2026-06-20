# 02-dpll — the DPLL solver, and model soundness

**Objective.** Build **DPLL**, the classic SAT search (simplify-and-branch), and prove **model
soundness**: the literal list it returns satisfies the clause set (`dpll_sound`). The engine is
`satBy_of_assign` — the `satBy` analogue of slice 3.1's `sat_of_assign`. This is **slices 3.2–3.3**; code
graduates into `Principia.Sat.Dpll`.

**Prerequisites.** Slice 3.1 (`assign`, `sat_of_assign`).

**The rung.** Single rung — `dpll` and `satBy` are *given*; you prove `satBy_of_assign` (the key invariant,
mirroring 3.1) and `dpll_sound` (induction following the solver's branches; hinted in full).

## Definition of done

- [ ] `make lab C=03-sat/02-dpll` goes red → green.
- [ ] `make test` stays green; `make axioms` clean.

## Run

```bash
make lab C=03-sat/02-dpll
make explainer C=03-sat/02-dpll
```

Next: the verified **LRAT certificate checker** — the achievable keystone, for the UNSAT side.
