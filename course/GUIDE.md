# GUIDE — the learner's manual

Welcome. You're a strong coder who's new to Lean and to formal logic. This course teaches both, **by
building** — you'll write a theorem prover, a resolution prover, a SAT solver, prove Euclid, and reach
the heart of Gödel's incompleteness, one small checked step at a time.

## The big idea: the computer checks your proofs

In Lean, **a proof is a program, and the kernel type-checks it.** If it compiles, it's correct — there
is no "looks right to me." This is our oracle. You can't fool it, and you never have to wonder whether
a proof is complete: the build is green or it isn't.

## The loop (how you learn each concept)

Each concept lives in `NN-course/NN-concept/` and has four files:

| File | What it is |
|---|---|
| `README.md` | the objective, what you'll prove, and "definition of done" |
| `explainer.qmd` | **the lesson** — the logic/math built gently from zero, then the Lean |
| `Skeleton.lean` | **your file** — theorems stated, proofs left as `sorry` + tips |
| `Solution.lean` | the verified answer key (proofs + a few `#eval`/`#print axioms` checks) |

Your job: open `Skeleton.lean`, replace each `sorry` with a real proof, and get to green:

```bash
make lab C=00-foundations/00-setup   # RED while any sorry remains, GREEN when you're done
```

The skeleton starts with `set_option warningAsError true`, so a leftover `sorry` is a hard **error** —
that's the red. When every goal is proved, the file compiles and you're green. Peek at `Solution.lean`
only when stuck (and try to understand *why* it works, not just copy it).

## The three ways things get checked

1. **Formal proof (the main one).** Does it compile? The kernel is the grader. `make lab` → green.
2. **Computational.** Our provers and solver are real programs — `#eval`/`#guard` run them on concrete
   inputs and check the answer (e.g. "the solver's model really satisfies this formula").
3. **Reference / differential.** Mathlib for math facts; the real solver CaDiCaL and the SMT solver Z3
   as outside answer keys we test against.

## The honesty rule

A proof that "passes" by *assuming what it should prove* is cheating. Two ways that happens in Lean —
leaving a `sorry`, or adding your own `axiom` — are both banned outside skeletons. We audit every
keystone with `#print axioms` (it lists exactly what a theorem depends on) and fail on `sorryAx`:

```bash
make axioms   # no stray sorry, no ad-hoc axiom, no sorryAx in keystones
```

The only axioms we allow are Lean's own three (`propext`, `Classical.choice`, `Quot.sound`).

## Using the vendored books

`../references/` has four classics, read-only. We mirror key exercises into our own concepts, but read
the originals freely:

- **Natural Number Game** — gamified first tactics (best played at adam.math.hhu.de).
- **Theorem Proving in Lean 4** — the language reference.
- **Logic and Proof** — the logic itself (natural deduction, semantics) — pairs with Courses 1–2.
- **Mathematics in Lean** — doing math with Mathlib (Course 0.5; needs `lake exe cache get`).

## Start here

```bash
make setup                            # once
make test                             # everything green?
make lab C=00-foundations/00-setup    # your first proofs
```

Then read `00-foundations/00-setup/explainer.qmd`.
