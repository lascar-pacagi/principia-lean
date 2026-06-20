# 05-prover — a proof search that's correct by construction

**Objective.** Write a **prover**: a function that *searches* for natural-deduction derivations, ending
the by-hand misery of slice 1.3. Because it returns a **typed** `Deriv`, anything it finds is correct by
construction — you prove `prove_sound` (success ⟹ valid) in a couple of lines, reading the certificate
off the type. This is **slice 1.5**; code graduates into `Principia.NatDed.Prover`.

**Prerequisites.** Slices 1.3 (`Deriv`) and 1.4 (`soundness`, `tautology_of_proof`).

**The rung.** Single rung — the search (`assumption?`, `prove?`, `prove`) is *given*; you prove the two
correctness theorems `prove_sound` and `prove_tautology`.

**Honest scope.** This prover applies only *introduction* rules + the assumption rule, so it's
**incomplete**: its **yes is always right** (that's `prove_sound`), but a **no** just means this search
gave up — e.g. it misses `(φ ⋏ ψ) ⇒ φ`, which needs ∧-elimination. *Every* valid formula nonetheless has
a derivation — that's **completeness**, slice 1.6.

## Definition of done

- [ ] `make lab C=01-natural-deduction/05-prover` goes red → green.
- [ ] `make test` stays green; `make axioms` clean.

## Run

```bash
make lab C=01-natural-deduction/05-prover
make explainer C=01-natural-deduction/05-prover
```
