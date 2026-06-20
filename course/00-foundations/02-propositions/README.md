# 02-propositions — the logical connectives, and the tactics that build & break them

**Objective.** Learn to prove statements built from the logical connectives — `→`, `∧`, `∨`, `¬`, `↔`,
`∀`, `∃` — by mastering the *two moves per connective*: how to **build** a proof (introduction) and how
to **use** one (elimination). This is the core logic toolkit, and the intro/elim pattern you'll meet
here is exactly the **natural deduction** system we formalize a prover for in Course 1.

**Prerequisites.** `00-setup` and `01-naturals` (the loop; `intro`/`exact`/`rfl`/`rw`/`induction`).

**The rung.** Single rung — six theorems, one per connective family. All are **constructive** (they
depend on no axioms); classical reasoning (`¬¬p → p`, `p ∨ ¬p`) waits for Course 0.4.

## Definition of done

- [ ] `make lab C=00-foundations/02-propositions` goes red → green (all six `sorry`s discharged).
- [ ] `make test` stays green.
- [ ] `make axioms` clean (every keystone depends on no axioms).

## Run

```bash
make lab C=00-foundations/02-propositions
make explainer C=00-foundations/02-propositions
```

Read `explainer.qmd` (or `explainer.html` / `explainer.pdf`) first.
