import Principia.Euclid.Basic

/-!
# 02-betweenness — Skeleton  (THIS IS YOUR FILE)

The extended axiom system `EuclidPlane2` (betweenness + segment construction + the five-segment/SAS axiom)
is GIVEN, and so are slice 4.1's congruence lemmas (imported). Prove `cong_null`, `betw_trivial`, and
`segment_add`.

Run:  make lab C=04-euclid/02-betweenness
Stuck? See §5 "Prove it" and §6 "Hints for the skeleton" in `explainer.qmd`.
-/
set_option warningAsError true
namespace Principia
open EuclidPlane

class EuclidPlane2 (Point : Type) extends EuclidPlane Point where
  Betw : Point → Point → Point → Prop
  betw_identity : ∀ {a b : Point}, Betw a b a → a = b
  segment_construction : ∀ (a b c d : Point), ∃ e, Betw a b e ∧ Cong b e c d
  five_segment : ∀ {a b c d a' b' c' d' : Point},
    Betw a b c → Betw a' b' c' → Cong a b a' b' → Cong b c b' c' →
    Cong a d a' d' → Cong b d b' d' → Cong c d c' d'

open EuclidPlane2
variable {Point : Type} [EuclidPlane2 Point]

/-! Your theorems. Tools: the axiom fields above + 4.1's `cong_pseudo_refl`/`cong_symm`/`cong_trans'`. -/

-- any two null segments are congruent (use `segment_construction` then `cong_identity`)
theorem cong_null (a b : Point) : Cong a a b b := by
  sorry

-- `b` lies between `a` and itself
theorem betw_trivial (a b : Point) : Betw a b b := by
  sorry

-- segment addition: congruent pieces, laid end to end, give congruent wholes
theorem segment_add {a b c a' b' c' : Point}
    (hbc : Betw a b c) (hbc' : Betw a' b' c')
    (h1 : Cong a b a' b') (h2 : Cong b c b' c') : Cong a c a' c' := by
  sorry

end Principia
