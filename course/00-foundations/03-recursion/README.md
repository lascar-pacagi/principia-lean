# 03-recursion — inductive types & recursion, the machinery behind syntax trees

**Objective.** Go deep on the two tools that power everything to come: **defining your own data types**
(`inductive`) and **defining functions by recursion** over them, then **proving things by structural
induction**. We build a tiny expression language `Expr`, a recursive evaluator `eval`, and prove that a
syntactic transformation **preserves evaluation** — a baby version of the *soundness* theorems we'll
prove about a real prover in Course 1.

**Prerequisites.** `01-naturals` (induction on `MyNat`) and `02-propositions` (the tactics).

**The rung.** Single rung — the type `Expr` and the functions `eval`, `swap`, `size` are *given*; you
prove three theorems by induction over a **branching** type (two recursive children → two induction
hypotheses — the new wrinkle vs. `MyNat`).

## Definition of done

- [ ] `make lab C=00-foundations/03-recursion` goes red → green (all three `sorry`s discharged).
- [ ] `make test` stays green.
- [ ] `make axioms` clean (keystones depend only on Lean's accepted axioms — `propext`/`Quot.sound` from
      `simp`/`omega` are fine; the audit forbids only `sorryAx`).

## Run

```bash
make lab C=00-foundations/03-recursion
make explainer C=00-foundations/03-recursion
```

Read `explainer.qmd` (or `explainer.html` / `explainer.pdf`) first.
