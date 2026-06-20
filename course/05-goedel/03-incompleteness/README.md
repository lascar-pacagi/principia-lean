# 03-incompleteness — Gödel's first incompleteness theorem (abstract)

**Objective.** The finale's summit: prove **Gödel's first incompleteness theorem** in abstract form. A
`Theory` has a provability predicate `Prov`, a semantic truth `True_`, negation, **soundness** (provable ⇒
true), and a **Gödel sentence** `G` with `True_ G ↔ ¬ Prov G` ("I am unprovable") — the latter being what
the diagonal lemma yields for the provability predicate. From these, `G` is **true but unprovable**, and
its negation is unprovable too: the theory is **incomplete**. The same diagonal argument as 5.1–5.2, now
carrying provability. **Slice 5.3**; graduates into `Principia.Goedel.Incompleteness`.

**Honest scope.** Everything here is verified and axiom-clean. The single hypothesis we don't *discharge*
is `goedel_sentence` — producing it concretely is the **arithmetisation** (Gödel numbering a real theory
like Robinson's Q or PA, and proving the diagonal lemma for it), which is a large, separate undertaking
(the FFL-Foundation / `Mathlib` developments do this). We take its existence as a field and derive the
famous conclusion cleanly — "the logical heart of Gödel," as intended.

**Prerequisites.** Slice 5.1 (the diagonal idea). Conceptually continues 5.2.

**The rung.** Single rung — the `Theory` framework is *given*; you prove `incompleteness`.

## Definition of done

- [ ] `make lab C=05-goedel/03-incompleteness` goes red → green.
- [ ] `make test` stays green; `make axioms` clean (`incompleteness` depends on **no** Lean axioms).

## Run

```bash
make lab C=05-goedel/03-incompleteness
make explainer C=05-goedel/03-incompleteness
```
