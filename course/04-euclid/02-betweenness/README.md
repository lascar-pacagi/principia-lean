# 02-betweenness — order, SAS without angles, and segment addition

**Objective.** Extend the geometry with Tarski's second primitive, **betweenness** `Betw a b c`, plus the
**five-segment axiom** — Tarski's remarkable angle-free encoding of Euclid's **SAS** (Prop I.4) — and
**segment construction**. From these, prove the bedrock facts the rest of geometry stands on: any two null
segments are congruent (`cong_null`), degenerate betweenness (`betw_trivial`), and **segment addition**
(`segment_add`, Tarski's l2_11). This is **slice 4.2**; code graduates into `Principia.Euclid.Betweenness`.

**The big idea.** Euclid's SAS says "two sides and the *included angle* equal ⇒ triangles congruent." But
our language has *no angle primitive*. Tarski's trick: replace "the angle at `b`" by a *fourth point* `d`
whose distances to `a` and `b` are fixed — that pins the configuration's rigidity without ever measuring
an angle. That is the five-segment axiom.

**Honest scope.** The five-segment axiom *is* the heart of I.4. Deriving the *general* triangle-congruence
form of I.4, and I.5 (*pons asinorum*), additionally needs the Pasch axiom, point reflection, and a
defined angle-congruence — substantial machinery (this is what GeoCoq builds over hundreds of lemmas). We
prove the foundational congruence consequences here and flag the rest as the natural continuation.

**Prerequisites.** Slice 4.1 (`EuclidPlane`, `cong_symm`/`cong_trans'`/`cong_pseudo_refl`).

**The rung.** Single rung — the axiom system `EuclidPlane2` is *given*; you prove `cong_null`,
`betw_trivial`, and `segment_add`.

## Definition of done

- [ ] `make lab C=04-euclid/02-betweenness` goes red → green.
- [ ] `make test` stays green; `make axioms` clean (no Lean `axiom` dependence — postulates are fields).

## Run

```bash
make lab C=04-euclid/02-betweenness
make explainer C=04-euclid/02-betweenness
```
