# 04-cdcl — a CDCL solver: clause learning and backjumping

**Objective.** Build the modern SAT algorithm — **Conflict-Driven Clause Learning** — on top of DPLL.
Where DPLL backtracks *chronologically*, CDCL, on a conflict, **learns a new clause** (by resolving the
conflict back to a *unique implication point*) and **backjumps** non-chronologically to where that clause
becomes unit. The learned clause stops the solver from ever repeating the conflict. This is **slice 3.5**;
code graduates into `Principia.Sat.Cdcl`.

**This solver is UNVERIFIED** — no machine-checked soundness (the 1-UIP analysis is intricate). We justify
it two ways, both honest: (1) **differential testing** — its SAT/UNSAT verdicts must agree with the
*verified* `dpll` on a battery of instances (the `#guard`s below; a wrong implementation fails the build),
and (2) in practice its UNSAT answers would be emitted as a certificate and validated by the **verified**
`Sat.Lrat.check` (slice 3.6). Fast untrusted solver + small verified checker — the Course-3 thesis.

**Prerequisites.** Slices 3.2 (DPLL, `dpll`), 3.6 if done (the LRAT framing); Course 2's `resolvent`.

**The rung.** Single rung — the whole CDCL engine is *given* except `clauseStatus` (classify a clause
under the trail), which you implement; the differential `#guard`s check that your implementation makes the
solver agree with `dpll`.

## Definition of done

- [ ] `make lab C=03-sat/04-cdcl` goes red → green (and the differential `#guard`s pass).
- [ ] `make test` stays green; `make axioms` clean.

## Run

```bash
make lab C=03-sat/04-cdcl
make explainer C=03-sat/04-cdcl
```
