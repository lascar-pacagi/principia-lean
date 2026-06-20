# 02-semantics — what a formula *means*

**Objective.** Give formulas meaning: define `eval`, the truth table of `04-logic` as a Lean function;
define validity `Tautology` (`⊨ φ`) and semantic entailment `Entails` (`Γ ⊨ φ`); and meet a **runnable
tautology checker** `taut?`. You'll prove three basic semantic facts. This is **slice 1.2**; its code
graduates into `Principia.Logic.Semantics` and is the `⊨` side of the soundness/completeness theorems to
come.

**Prerequisites.** Slice 1.1 (`Form`), and `04-logic` (truth tables, `⊨`).

**The rung.** Single rung — `eval`, `Tautology`, `Entails`, and the checker `taut?` are *given*; you
prove `eval_neg`, `taut_imp_self`, `taut_em`.

## Definition of done

- [ ] `make lab C=01-natural-deduction/02-semantics` goes red → green.
- [ ] `make test` stays green; `make axioms` clean.

## Run

```bash
make lab C=01-natural-deduction/02-semantics
make explainer C=01-natural-deduction/02-semantics
```

Next slice: **1.3 — natural deduction** (`Γ ⊢ φ` as an inductive type of proof trees).
