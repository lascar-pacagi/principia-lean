# 04-soundness — a refutation witnesses unsatisfiability

**Objective.** Prove **resolution soundness**: `Refut S [] → S.Unsat`. Reaching the empty clause really
does mean the clause set has no model — so the prover's "yes" is *correct*. The engine is that the
**resolvent preserves models**; by induction every derived clause holds in every model, and `□` (true in
no model) forces there to be no model. The corollary `taut_of_refut` closes the whole chain: refute the
clauses of `∼φ` ⟹ `φ` is valid. This is **slice 2.4**, a **keystone**; code graduates into
`Principia.Resolution.Soundness`.

**Prerequisites.** Slices 2.1 (`Cnf.eval`, the bridge), 2.2 (`Refut`, `resolvent`); slice 1.4 (soundness
by induction on a derivation).

**The rung.** Single rung — the per-step lemmas (`Lit.neg_eval`, `erase_eval`, `resolvent_sound`) are
*given*; you prove `refut_sound` (induction on the refutation), `refut_unsat` (the keystone), and
`taut_of_refut`.

## Definition of done

- [ ] `make lab C=02-resolution/04-soundness` goes red → green.
- [ ] `make test` stays green; `make axioms` clean.

## Run

```bash
make lab C=02-resolution/04-soundness
make explainer C=02-resolution/04-soundness
```

Next slice: **2.5 — refutation-completeness** (`S.Unsat → Refut S []`), the converse and hard keystone.
