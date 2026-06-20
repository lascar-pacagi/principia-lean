# Principia — learning Lean by building verified logic tools

A learn-by-doing Lean 4 course. We build **`Principia`**, one real library, across six courses:
foundations → a natural-deduction prover → a resolution prover → a SAT solver → Euclid → Gödel. Every
result is **machine-checked by the Lean kernel** — a `sorry`-free build *is* the green test.

New here? Read **`GUIDE.md`**. The full curriculum is in **`../PLAN.md`**; conventions in **`../CLAUDE.md`**.

## Commands

```bash
make            # help
make setup      # build the toolchain + library (run once)
make test       # build the library + kernel-check every Solution.lean — GREEN
make lab C=00-foundations/00-setup   # build a concept's skeleton — RED until you solve it
make axioms     # honesty audit: no stray sorry/axiom, no sorryAx in keystones
make explainer C=00-foundations/00-setup   # render a lesson → explainer.html + .pdf beside the source
make docs                                   # render all lessons in place (HTML + PDF via Typst)
```

## Layout

```
course/
├── Principia/         # THE ARTIFACT — the accumulating Lean library (Logic, NatDed, Resolution, …)
├── tooling/           # the honesty auditor and (later) DIMACS/LRAT + differential-test harness
├── _TEMPLATE-concept/ # copy this to author a new concept
└── NN-course/NN-concept/   # each concept: README · explainer.qmd · Skeleton.lean · Solution.lean
```

Pure Lean 4 (v4.31.0), no Mathlib in the core — fast builds. Mathlib enters only via the vendored MIL
project (Course 0.5) and the LeanEuclid / Foundation sub-projects (Courses 4–5).
