# 03-lrat — a verified UNSAT-certificate checker  (Course 3 keystone)

**Objective.** Build the trustworthy-UNSAT side of a SAT pipeline: a small **verified checker** that
validates a refutation *certificate*. A certificate is a flat, hint-carrying resolution proof (the core
of the LRAT format): each line names two earlier clauses + a literal and claims their resolvent. The
checker replays it and confirms the empty clause `□` was derived; **`check_unsat`** proves that
acceptance implies the CNF is unsatisfiable. This is **slice 3.6**, the keystone of Course 3; it mirrors
Lean core's own LRAT checker behind `bv_decide`. Code graduates into `Principia.Sat.Lrat`.

**Why a checker?** Verifying a fast solver is a multi-year effort. Instead, let an *untrusted* solver
emit a certificate and trust only the *checker* (plus the kernel). That's how real verified UNSAT works.

**Prerequisites.** Course 2's `resolvent` and `resolvent_sound` (`Resolution.Soundness`); slice 3.2 (the
SAT side).

**The rung.** Single rung — the checker (`Step`, `checkStep`, `runProof`, `check`, `Entailed`) is *given*;
you prove `runProof_preserves` (the entailment invariant) and `check_unsat` (the keystone).

## Definition of done

- [ ] `make lab C=03-sat/03-lrat` goes red → green.
- [ ] `make test` stays green; `make axioms` clean.

## Run

```bash
make lab C=03-sat/03-lrat
make explainer C=03-sat/03-lrat
```
