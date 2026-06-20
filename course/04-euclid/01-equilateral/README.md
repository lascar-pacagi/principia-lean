# 01-equilateral — Euclid's Proposition I.1, made honest

**Objective.** Do synthetic Euclidean geometry the rigorous way: state the postulates as a **`class`**
(so there is *no* `axiom` keyword — the geometric assumptions are hypotheses, and theorems hold in any
model), derive that **segment congruence is an equivalence** from Tarski's spare axioms, and prove
**Elements I.1** — on any segment you can erect an equilateral triangle — with the famous **hidden
continuity assumption made explicit**. This is **Course 4**, a change of pace into real mathematics; code
graduates into `Principia.Euclid.Basic`.

**Why this matters.** Euclid's I.1 *constructs* the apex of the triangle as the intersection of two
circles — but his postulates never guarantee the circles meet. That gap (diagrams smuggling in
continuity) is the whole reason modern geometry is axiomatised so carefully. Here the gap is one named
axiom, `circles_meet`, and I.1 follows in a few honest lines.

**Prerequisites.** Course 0 (tactics, `obtain`, `∃`). No dependence on the logic/SAT development.

**The rung.** Single rung — the axiom system `EuclidPlane` is *given*; you prove `cong_refl`, `cong_symm`,
`cong_trans'`, and `prop_I1`.

## Definition of done

- [ ] `make lab C=04-euclid/01-equilateral` goes red → green.
- [ ] `make test` stays green; `make axioms` clean (`prop_I1` depends on **no** Lean axioms — the
      geometric postulates are class fields, not `axiom`s).

## Run

```bash
make lab C=04-euclid/01-equilateral
make explainer C=04-euclid/01-equilateral
```
