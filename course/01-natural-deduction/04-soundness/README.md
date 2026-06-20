# 04-soundness — everything provable is true  (Milestone M1)

**Objective.** Prove **soundness**: `Γ ⊢ φ → Γ ⊨ φ`. Every derivation, however it was built, yields a
formula true under every valuation that satisfies the assumptions. This connects the two turnstiles for
the first time, and it's what lets us *trust* the prover (slice 1.5): if it finds a proof, the formula is
really valid. This is **slice 1.4** — the first **keystone** — and **Milestone M1**. Code graduates into
`Principia.NatDed.Soundness`.

**Prerequisites.** Slices 1.1–1.3 (`Form`, `eval`/`⊨`, `Deriv`/`⊢`), and `03-recursion` (induction over an
inductive type — soundness is `eval_swap` scaled up).

**The rung.** Single rung — the Boolean helper lemmas are *given*; you prove `soundness` (by induction on
the derivation) and the corollary `tautology_of_proof`.

## Definition of done

- [ ] `make lab C=01-natural-deduction/04-soundness` goes red → green.
- [ ] `make test` stays green; `make axioms` clean (`soundness` depends only on `propext`).

## Run

```bash
make lab C=01-natural-deduction/04-soundness
make explainer C=01-natural-deduction/04-soundness
```

Next slice: **1.5 — the prover** (proof search), whose "yes" this theorem makes trustworthy.
