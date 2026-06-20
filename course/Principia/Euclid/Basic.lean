/-!
# Principia.Euclid.Basic — synthetic Euclidean geometry, from axioms (Course 4)

Euclid's *Elements* reasons from axioms about points, lines, and magnitudes — but with gaps (steps that
"look obvious from the diagram" but aren't justified by his stated postulates). We make the method honest
in Lean by stating the axioms as a **`class`** (so there's no `axiom` keyword — the geometric postulates
become *hypotheses*, and every theorem holds in any model of them), and proving the first proposition,
**making the hidden continuity assumption explicit**.

We use a Tarski-style **segment-congruence** primitive `Cong a b c d` ("ab and cd have equal length") with
three congruence axioms, plus the single **circle–circle continuity** instance Euclid silently uses in
Proposition I.1.
-/
namespace Principia

/-- A model of (the fragment of) Euclidean geometry we need: segment congruence with Tarski's axioms,
    and the circle-intersection postulate for Prop I.1. -/
class EuclidPlane (Point : Type) where
  /-- `Cong a b c d`: segment `ab` is congruent to segment `cd`. -/
  Cong : Point → Point → Point → Point → Prop
  /-- a segment is congruent to its reverse -/
  cong_pseudo_refl : ∀ {a b}, Cong a b b a
  /-- (Tarski) two segments each congruent to `ab` are congruent to each other -/
  cong_trans : ∀ {a b p q r s}, Cong a b p q → Cong a b r s → Cong p q r s
  /-- a segment congruent to a null segment is itself null -/
  cong_identity : ∀ {a b c}, Cong a b c c → a = b
  /-- **Continuity** (Euclid's implicit assumption in I.1): the circle centred `a` through `b` and the
      circle centred `b` through `a` intersect — there is a point equidistant `ab` from both `a` and `b`. -/
  circles_meet : ∀ (a b : Point), ∃ c, Cong a c a b ∧ Cong b c b a

open EuclidPlane
variable {Point : Type} [EuclidPlane Point]

/-- Congruence is reflexive (derived from the two Tarski axioms). -/
theorem cong_refl (a b : Point) : Cong a b a b := cong_trans cong_pseudo_refl cong_pseudo_refl
/-- Congruence is symmetric. -/
theorem cong_symm {a b c d : Point} (h : Cong a b c d) : Cong c d a b := cong_trans h (cong_refl a b)
/-- Congruence is transitive (the usual orientation). -/
theorem cong_trans' {a b c d e f : Point} (h1 : Cong a b c d) (h2 : Cong c d e f) : Cong a b e f :=
  cong_trans (cong_symm h1) h2

/-- **Euclid, Elements I.1.** On any segment `ab` one can erect an equilateral triangle: there is a point
    `c` with `ab ≅ ac`, `ab ≅ bc`, and (hence) `ac ≅ bc`. The point comes from where the two circles meet;
    the equalities are read off as radii. The whole content of the famous *gap* sits in `circles_meet`. -/
theorem prop_I1 (a b : Point) : ∃ c, Cong a b a c ∧ Cong a b b c ∧ Cong a c b c := by
  obtain ⟨c, hca, hcb⟩ := circles_meet a b          -- c on both circles: ac ≅ ab and bc ≅ ba
  refine ⟨c, cong_symm hca, ?_, ?_⟩
  · exact cong_trans' cong_pseudo_refl (cong_symm hcb)         -- ab ≅ ba ≅ bc
  · exact cong_trans' hca (cong_trans' cong_pseudo_refl (cong_symm hcb))   -- ac ≅ ab ≅ bc

end Principia
