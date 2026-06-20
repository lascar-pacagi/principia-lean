# 01-diagonal — the diagonal argument, once and for all

**Objective.** Begin Course 5 (the finale) by isolating the single argument behind Cantor, Russell, the
Liar, Tarski, Gödel, and Turing: **Lawvere's fixed-point theorem**. A point-surjective `e : A → (A → B)`
forces every `g : B → B` to have a fixed point; read backwards, it forbids surjections — that's Cantor,
and (in later slices) Tarski and Gödel. This is **slice 5.1**; code graduates into
`Principia.Goedel.Diagonal`.

**Why start here.** The "self-reference" in Gödel's theorem looks mysterious. It isn't: it's diagonalization,
the same three-line trick as Cantor's. Pin it down abstractly now and the incompleteness theorems (5.2,
5.3) become short corollaries.

**Prerequisites.** Course 0 (functions, `∃`, `congrFun`, `rintro`). No dependence on Courses 1–4.

**The rung.** Single rung — prove `lawvere`, `cantor`, and `no_self_neg`.

## Definition of done

- [ ] `make lab C=05-goedel/01-diagonal` goes red → green.
- [ ] `make test` stays green; `make axioms` clean.

## Run

```bash
make lab C=05-goedel/01-diagonal
make explainer C=05-goedel/01-diagonal
```

Next: **5.2 — Tarski's undefinability of truth** (the Liar, formalised), then **5.3 — the abstract first
incompleteness theorem**.
