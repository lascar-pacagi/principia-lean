# 02-propositions — the logical connectives, and the tactics that build & break them

**Objective.** Learn to prove statements built from the logical connectives — `→`, `∧`, `∨`, `¬`, `↔`,
`∀`, `∃` — by mastering the *two moves per connective*: how to **build** a proof (introduction) and how
to **use** one (elimination). This is the core logic toolkit, and the intro/elim pattern you'll meet
here is exactly the **natural deduction** system we formalize a prover for in Course 1.

**Prerequisites.** `00-setup` and `01-naturals` (the loop; `exact`, `rfl`, `rw`, and induction).
This lesson introduces `intro`, `apply`, `have`, `obtain`, and case analysis for propositions.

**The rung.** Single rung — seven theorems covering the connectives, including a dedicated universal
goal (`forall_and`) and an existential goal (`exists_imp`). All are **constructive** (they
depend on no axioms); classical reasoning (`¬¬p → p`, `p ∨ ¬p`) waits for Course 0.4.

**Optional practice.** `optional/Skeleton.lean` contains currying and a constructive De Morgan law;
`optional/Solution.lean` contains their verified proofs. The same `make lab` command reports optional
progress separately in yellow while unfinished. Required proofs alone determine whether the lab
passes. `make test` checks both answer keys, and `make axioms` audits their dependencies.

The lesson's teaching examples are separate from the seven required goals. Worked corrections follow
the exercises and hints, in §7 for required work and §9 for optional work.

## Definition of done

- [ ] `make lab C=00-foundations/02-propositions` goes red → green (all seven `sorry`s discharged).
- [ ] `make test` stays green.
- [ ] `make axioms` clean (every keystone depends on no axioms).

## Run

```bash
make lab C=00-foundations/02-propositions
make explainer C=00-foundations/02-propositions
```

Read `explainer.qmd` (or `explainer.html` / `explainer.pdf`) first.
