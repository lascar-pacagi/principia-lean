# CLAUDE.md

Operational guide for this repo. Read `PLAN.md` for the full curriculum and `course/GUIDE.md` for the
learner's manual. This file is the day-to-day "how we work."

## What this project is

A learn-by-doing Lean 4 curriculum for a **pro coder with no Lean experience and no formal-logic
training**, modeled on `../Physics`, `../LLM`, and `../Compiler`. We build **`Principia`** — a real
Lean library — one concept at a time, and through building it the user comes to *understand* theorem
proving: **two verified provers (natural deduction and resolution)**, a SAT solver with a verified
certificate checker, Euclid made rigorous, and the logical heart of Gödel's incompleteness.

Two principles shape everything:

1. **Logic & proof are taught gently, just-in-time, in service of the formalization.** When a concept
   needs a quantifier, an inductive predicate, a model, induction-on-derivations, or a fixed point,
   teach the *idea* from zero — concept first, intuition before symbols — and only because the next
   formalization needs it. Never a dry logic lecture; never logic-for-its-own-sake.
   **Be lavishly pedagogical:** the user is new to Lean *and* to logic and explicitly wants depth —
   assume nothing, motivate everything, walk each proof, tactic, and error message step by step, and
   prefer more explanation to less. A terse explainer is a bug, not a feature. (See `00-foundations/
   00-setup/explainer.qmd` for the expected depth and tone.)
2. **Everything is machine-checked**, via the three tiers below. The user learns by red→green, where
   the grader is the Lean kernel.

## The oracle is the kernel — and it is READ-ONLY

We never fudge a proof to pass. Validation comes from:

- **The Lean kernel** — a `sorry`-free `lake build` *is* a machine-checked proof. The primary oracle.
- **The axiom auditor** — `#print axioms <thm>` on every keystone. It must depend only on `propext`,
  `Classical.choice`, `Quot.sound`. A `sorryAx` (or any unexpected `axiom`) dependency = **fail**.
  `make axioms` / `make test` greps the tree for stray `sorry` and ad-hoc `axiom` declarations.
- **Mathlib** — the answer key for mathematical facts.
- **External tools** — **CaDiCaL** (differential-test the SAT solver; consume real LRAT certificates),
  **Z3/CVC5** (Euclid's diagrammatic side-conditions).
- **Reference formalizations** — FFL-Foundation, LeanEuclid, Lean-core's LRAT checker: read-only
  designs we check against, never copy blindly.

If a proof won't close, fix the proof (or the statement) — never weaken it with `sorry`/`axiom` to win.

## How a concept directory is built

Every concept = its own dir under `course/<NN-course>/NN-concept/`:

```
NN-concept/
├── README.md       # objective, prereqs, rung ladder, definition of done
├── explainer.qmd   # THE LESSON (gentle, concept-first, logic built from zero) — make explainer C=<dir>
├── Skeleton.lean   # `set_option warningAsError true` + BARE statements `theorem … := by sorry` — no inline tips (hints go in the explainer's "Hints" §)
├── Solution.lean   # verified answers + a `## Checks` block (#eval/#guard + #print axioms); `make test` builds these
└── figs/           # (optional) diagrams for the explainer
```

**The skeleton↔solution toggle.** `make test`/`lake build` builds `Solution.lean` (green). `make lab
C=<dir>` builds `Skeleton.lean` (red `sorry` → green as the learner discharges it). Copy
`_TEMPLATE-concept/` to author a new one.

## The three testing tiers

- **Tier 1 — Formal proof (the default).** The kernel grades it. skeleton `sorry` → solution proof.
- **Tier 2 — Computational.** `#eval` / `#guard` / `decide` / `native_decide` run the prover/solver on
  concrete inputs and check answers. The computation is the check; no proof needed.
- **Tier 3 — Reference / differential.** Mathlib (math facts), CaDiCaL (SAT verdict parity on DIMACS),
  Z3/CVC5 (Euclid side-conditions), reference formalizations (design checks).

Reach for Tier 1 for genuine theorems, Tier 2 to show code actually runs, Tier 3 to stay honest against
the outside world.

## Graduating code into `Principia`

When a concept's `make lab` is green, its verified definitions/theorems **graduate** into the
`Principia/` library (same code as `Solution.lean`), so the library grows and later concepts import it.
The `Logic/` core (syntax + semantics, Course 1) is the spine reused by `NatDed/` (Course 1),
`Resolution/` (Course 2), `Sat/` (Course 3), and `Goedel/` (Course 5); the README's "definition of
done" says exactly what graduates where.

## Toolchain & layout notes

- **Main library** pins **`leanprover/lean4:v4.31.0`** (current stable) via `course/lean-toolchain`
  and is **pure Lean 4 — no Mathlib** (fast builds, full control). `elan` auto-selects the pinned
  toolchain per directory. Mathlib enters only via self-contained sub-projects (vendored MIL for
  Course 0.5; LeanEuclid for Course 4; FFL-Foundation for Course 5), each with its own
  `lake exe cache get` run lazily when that course starts — never compile Mathlib from source.
- **Course 4 (Euclid)** uses **LeanEuclid**, which pins an older toolchain (**v4.19**) and needs
  **Z3/CVC5** installed. It lives as a **separate Lake sub-project** with its own `lean-toolchain`;
  `elan` handles the per-directory pin, so it coexists with the v4.31 main library.
- **`references/`** holds the four vendored books (NNG4, logic_and_proof, TPIL, MIL) — read-only;
  we mirror exercises into `course/00-foundations/` rather than editing them in place.

## Authoring a new concept (checklist)

1. `cp -r course/_TEMPLATE-concept course/<NN-course>/NN-<name>`.
2. Write `explainer.qmd` (the lesson — be thorough, per principle 1): motivate from a vivid question →
   build the logic/math it needs gently from zero → present the formalization, walking the proofs and
   tactics line by line → "Prove it" (the goals + command, **no method**) → "Hints for the skeleton"
   (graduated, opt-in nudges — this is where aid lives, not the skeleton) → map to the tiers →
   exercises → **worked, explained corrections to those exercises** (verify each compiles first) →
   going further. Renders **in place** to `explainer.html` + `explainer.pdf` beside the source
   (`make explainer C=<dir>`), via Quarto + Typst (no LaTeX). Match `00-setup`'s depth.
3. Write `Solution.lean` (the verified proofs) ending in a `## Checks` block (`#eval`/`#guard` the
   computational behavior + `#print axioms` the keystones); blank the proof bodies into
   `Skeleton.lean` (with `set_option warningAsError true` at the top) as bare `sorry` — no inline tips
   (graduated hints go in the explainer's "Hints for the skeleton" §).
5. Verify: `make test` green, `make lab C=<dir>` red→green, `make axioms` clean, `make explainer C=<dir>`
   renders. Then graduate verified code into `Principia/`.

## Commands

```bash
make setup                   # install elan/lake/Lean (on demand) + lake exe cache get
make build | test            # build the Principia library | build all solutions — GREEN
make lab C=<dir>             # build this concept's Skeleton.lean — red → green
make axioms                  # audit keystones with #print axioms; fail on sorryAx / stray axiom
make explainer C=<dir>       # render a lesson to HTML/PDF
make docs | preview          # render all explainers | live-preview
```

## Working style for the assistant

- Keep the **logic gentle, concept-first, and thorough** (principle 1). Motivate every definition from
  the question it answers; the user is new to formal logic and wants generous, detailed explanations —
  walk proofs/tactics/errors step by step, never terse.
- Prefer **Tier-2 computational** checks to show code runs; reach for **Tier-1 proofs** at genuine
  theorems; stay honest with **Tier-3** differential checks.
- **Never** discharge a goal with `sorry` or an ad-hoc `axiom` in a solution. If stuck, say so and leave
  the `sorry` only in `Skeleton.lean`.
- **Skeletons stay bare** — statement + `sorry` only, no answer-revealing inline tips. The learner should
  meet each goal cold; graduated, opt-in hints belong in the explainer's "Hints for the skeleton" §.
- Keep each concept **self-contained and buildable**; never leave the repo red on `make test`.
- One concept at a time, building the ladder; always leave a working, checked capability.
- Not a git repo (yet). Don't commit unless asked.
