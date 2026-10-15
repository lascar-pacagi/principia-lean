# 03-recursion — inductive types & recursion, the machinery behind syntax trees

**Objective.** Go deep on the two tools that power everything to come: **defining your own data types**
(`inductive`) and **defining functions by recursion** over them, then **proving things by structural
induction**. We build a small expression language `Expr`, an evaluator `eval`, and a transformation
`swap`, then establish properties of the transformed trees and their numerical meaning.

**Prerequisites.** `01-naturals` (induction on `MyNat`) and `02-propositions` (the tactics).

**The rung.** Single rung — the type `Expr` and the functions `eval`, `swap`, `size` are *given*; you
prove three theorems by induction over a **branching** type (two recursive children → two induction
hypotheses). The course demonstrates induction with a separate function, `copy`; the required
proofs appear only after the exercises and hints, in §7.

**Optional practice.** `optional/Skeleton.lean` provides two further exercises: reuse a proved
equality inside the evaluator, and implement a leaf-counting function and prove its invariance.
The answer key and worked explanations are in `optional/Solution.lean` and §9 of the lesson.
The same `make lab` command checks both sets, with yellow pending statuses for unfinished optional
work. Required exercises alone determine whether the lab passes.

## Definition of done

- [ ] `make lab C=00-foundations/03-recursion` goes red → green (all three `sorry`s discharged).
- [ ] `make test` stays green.
- [ ] `make axioms` clean (completed proofs have no `sorryAx` dependency or ad-hoc axiom declarations).

## Run

```bash
make lab C=00-foundations/03-recursion
make explainer C=00-foundations/03-recursion
make reset C=00-foundations/03-recursion DRY_RUN=1  # preview resetting both exercise sets
```

Read `explainer.qmd` (or `explainer.html` / `explainer.pdf`) first.
