# 05-completeness — a verified resolution decision procedure, and the hard keystone

**Objective.** Cash out resolution soundness into a **verified decision procedure**: when the prover finds
`□`, the clause set is unsatisfiable (`refute?_unsat`) and — refuting the clauses of `∼φ` — `φ` is a
tautology (`prove_taut_by_resolution`, which even certifies Peirce's law automatically). And close the
achievable half of the **tie to Course 1**: a resolution refutation yields a natural-deduction proof
(`refutable_to_provable`). This is **slice 2.5**, the finale of Course 2; code graduates into
`Principia.Resolution.Completeness`.

**The flagged hard keystone.** Full *refutation-completeness* — `S.Unsat → Refut S []`, that *every*
unsatisfiable set has a refutation — is research-grade with our `List`-based clauses (it needs set-like
clause handling plus a restriction/lifting or semantic-tree induction). We **study** it in the lesson and
treat it as the marked stretch (like FOL completeness). Course 1's natural-deduction prover already has
*full* completeness, so the project's proof↔validity coincidence is established there.

**Prerequisites.** Slices 2.3 (`refute?`), 2.4 (soundness); Course 1's `provable_iff_tautology`.

**The rung.** Single rung — you prove three short compositions of earlier theorems.

## Definition of done

- [ ] `make lab C=02-resolution/05-completeness` goes red → green.
- [ ] `make test` stays green; `make axioms` clean.

## Run

```bash
make lab C=02-resolution/05-completeness
make explainer C=02-resolution/05-completeness
```
