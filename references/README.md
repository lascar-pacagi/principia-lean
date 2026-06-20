# References — vendored, READ-ONLY

The four canonical Lean learning resources, cloned here for offline access. **Do not edit these.** We
*read* them and **mirror** selected exercises into `../course/00-foundations/` as our own
skeleton→solution concepts (so they're checked in our repo). Each was shallow-cloned (`--depth 1`).

| Dir | Upstream | What it is | License | Local build |
|---|---|---|---|---|
| `NNG4/` | github.com/leanprover-community/NNG4 | Natural Number Game — gamified intro to tactics, ℕ from Peano. A Lean *game* (toolchain v4.23.0), normally played in-browser at adam.math.hhu.de. | Apache-2.0 | optional; built on the lean4game engine, not needed to learn from it |
| `logic_and_proof/` | github.com/leanprover-community/logic_and_proof | "Logic and Proof" (Avigad et al.) — a logic textbook (propositional & first-order, natural deduction, semantics, soundness/completeness). | Apache-2.0 | static **Sphinx/RST** site (no Lake project); read the prose, or the live site |
| `theorem_proving_in_lean4/` | github.com/leanprover/theorem_proving_in_lean4 | "Theorem Proving in Lean 4" — the canonical language reference (dependent types, tactics, inductive types). | Apache-2.0 | literate book under `book/`; runnable examples in `examples/` |
| `mathematics_in_lean/` | github.com/leanprover-community/mathematics_in_lean | "Mathematics in Lean" (Avigad & Massot) — doing real math with **Mathlib**; exercises in `MIL/`. (toolchain v4.30.0) | Apache-2.0 (code) / CC-BY-4.0 (text) | a real Lake+Mathlib project — see below |

## Fetching Mathlib for MIL (only when Course 0.5 begins)

`mathematics_in_lean` is the one resource that needs Mathlib. To make it runnable, fetch the prebuilt
Mathlib cache **inside that repo** (a multi-GB download — deferred until we start Course 0.5; our own
`course/Principia` core does **not** depend on Mathlib):

```bash
cd references/mathematics_in_lean
lake exe cache get      # downloads prebuilt Mathlib artifacts (do NOT compile from source)
lake build
```

Work exercises by **copying** a chapter out of `MIL/` before editing, so a later `git pull` stays clean.

## Provenance

Cloned 2026-06-19 at `--depth 1` (no history). To refresh: `git -C references/<dir> pull` (or re-clone).
These mirror upstream as of that date; the live sites may be newer.
