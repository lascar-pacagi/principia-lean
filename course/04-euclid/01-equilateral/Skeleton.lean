/-!
# 01-equilateral — Skeleton  (THIS IS YOUR FILE)

The axiom system `EuclidPlane` is GIVEN (postulates as a `class` — no `axiom` keyword). Prove that
congruence is an equivalence (`cong_refl`, `cong_symm`, `cong_trans'`) and then **Euclid I.1** (`prop_I1`).

Run:  make lab C=04-euclid/01-equilateral
Stuck? See §5 "Prove it" and §6 "Hints for the skeleton" in `explainer.qmd`.
-/
set_option warningAsError true
namespace Principia

class EuclidPlane (Point : Type) where
  Cong : Point → Point → Point → Point → Prop
  cong_pseudo_refl : ∀ {a b}, Cong a b b a
  cong_trans : ∀ {a b p q r s}, Cong a b p q → Cong a b r s → Cong p q r s
  cong_identity : ∀ {a b c}, Cong a b c c → a = b
  circles_meet : ∀ (a b : Point), ∃ c, Cong a c a b ∧ Cong b c b a

open EuclidPlane
variable {Point : Type} [EuclidPlane Point]

/-! Your theorems. The only tools are the four axiom fields above (and the lemmas as you build them). -/

-- congruence is reflexive (use `cong_trans` on two copies of `cong_pseudo_refl`)
theorem cong_refl (a b : Point) : Cong a b a b := by
  sorry

-- congruence is symmetric
theorem cong_symm {a b c d : Point} (h : Cong a b c d) : Cong c d a b := by
  sorry

-- congruence is transitive (the usual orientation)
theorem cong_trans' {a b c d e f : Point} (h1 : Cong a b c d) (h2 : Cong c d e f) : Cong a b e f := by
  sorry

-- Euclid, Elements I.1: an equilateral triangle on any segment `ab`.
theorem prop_I1 (a b : Point) : ∃ c, Cong a b a c ∧ Cong a b b c ∧ Cong a c b c := by
  sorry

end Principia
