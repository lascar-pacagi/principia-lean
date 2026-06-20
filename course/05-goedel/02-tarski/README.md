# 02-tarski — the undefinability of truth

**Objective.** Prove **Tarski's theorem**: no language can define its own truth predicate. We model a
language abstractly (sentences, semantic truth `True_`, negation, a class of `Definable` predicates closed
under negation, and the **diagonal lemma**), and show `True_` is not among the definable predicates — for
if it were, the diagonal lemma would build a **Liar** sentence `True_ s ↔ ¬ True_ s`, impossible by 5.1's
`no_self_neg`. It's the diagonal argument with *truth* substituted in. **Slice 5.2**; graduates into
`Principia.Goedel.Tarski`.

**Prerequisites.** Slice 5.1 (`no_self_neg`).

**The rung.** Single rung — the `Lang` framework is *given*; you prove `tarski`.

## Definition of done

- [ ] `make lab C=05-goedel/02-tarski` goes red → green.
- [ ] `make test` stays green; `make axioms` clean.

## Run

```bash
make lab C=05-goedel/02-tarski
make explainer C=05-goedel/02-tarski
```

Next: **5.3 — the abstract first incompleteness theorem.**
