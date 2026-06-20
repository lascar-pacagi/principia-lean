# 03-prover — a resolution prover by saturation

**Objective.** Build a **resolution prover**: a *saturation* search that keeps resolving pairs of clauses
until the empty clause `□` appears, returning a **typed** `Refut S []`. As with the slice-1.5 prover, the
return type is the certificate — `refute?_refutable` (a successful search ⟹ `S` is refutable) is a
two-line read-off. This is **slice 2.3**; code graduates into `Principia.Resolution.Prover`.

**Prerequisites.** Slice 2.2 (`Refut`, `resolvent`); slice 1.5 (the sound-by-construction idea).

**The rung.** Single rung — the search (`refute?` and its helpers) is *given*; you prove `refute?_refutable`.

**Honest scope.** The search is naive (no subsumption, keeps everything) and `fuel`-bounded: its **yes is
a real refutation**, but a **no** only means "not found within this many rounds." Refutation-completeness
(slice 2.5) guarantees that an unsatisfiable set *does* have a refutation to find.

## Definition of done

- [ ] `make lab C=02-resolution/03-prover` goes red → green.
- [ ] `make test` stays green; `make axioms` clean.

## Run

```bash
make lab C=02-resolution/03-prover
make explainer C=02-resolution/03-prover
```

Next slice: **2.4 — soundness** (`Refut S [] → S.Unsat`), which gives the prover's "yes" its meaning.
