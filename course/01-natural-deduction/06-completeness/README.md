# 06-completeness — everything true is provable  (closes the loop)

**Objective.** Prove **completeness**: `Tautology φ → [] ⊢ φ`. Together with soundness (1.4) this gives
`⊢ ⟺ ⊨` — provability and validity are the *same thing*, so checking truth tables and searching for
proofs are two views of one decision problem. This is **slice 1.6**, the final slice of Course 1 and its
hardest keystone. The heavy machinery (Kalmár's lemma, variable elimination) lives in
`Principia.NatDed.Kalmar`; you **assemble** the final theorem.

**Prerequisites.** Slices 1.1–1.5 — especially 1.4 (`soundness`, `tautology_of_proof`).

**The rung.** Single rung — `kalmar` and `elim` are *given* (imported from the library; read them and the
explainer to understand the construction). You prove `completeness` (a one-line assembly) and
`provable_iff_tautology` (combine with soundness).

## The method (Kalmár), in one breath

For each valuation `v`, the literal context `litCtx v n` (the assumptions `{±atomᵢ}` matching `v`) proves
`φ` exactly when `v ⊨ φ` — that's **`kalmar`**. If `φ` is a tautology, *every* `v` makes it true, so every
literal context proves it; **`elim`** then collapses all `2ⁿ` of them to `[]` by eliminating atoms one at
a time with excluded middle. No maximal consistent sets, no choice — elementary.

## Definition of done

- [ ] `make lab C=01-natural-deduction/06-completeness` goes red → green.
- [ ] `make test` stays green; `make axioms` clean (no `sorryAx` — only `propext`/`Quot.sound`).

## Run

```bash
make lab C=01-natural-deduction/06-completeness
make explainer C=01-natural-deduction/06-completeness
```
