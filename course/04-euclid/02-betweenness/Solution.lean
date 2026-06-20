import Principia.Euclid.Basic

/-!
# 02-betweenness — Solution  (verified answer key)

`make test` kernel-checks this; `make axioms` audits it. Graduates into `Principia.Euclid.Betweenness`.
-/
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

-- construct a copy of the null segment `bb` off `aa`; `cong_identity` collapses it, giving `Cong a a b b`.
theorem cong_null (a b : Point) : Cong a a b b := by
  obtain ⟨e, _, he⟩ := segment_construction a a b b
  have : a = e := cong_identity he
  subst this; exact he

-- same move: extend `ab` by the null `bb`; the new point is `b`, witnessing `Betw a b b`.
theorem betw_trivial (a b : Point) : Betw a b b := by
  obtain ⟨e, hbe, he⟩ := segment_construction a b b b
  have : b = e := cong_identity he
  subst this; exact hbe

-- five-segment with the fourth point taken as `a` (resp. `a'`): the `ad`/`bd` hypotheses become the
-- null `aa` and the reversed `ab`, and the conclusion `ca ≅ c'a'` flips to `ac ≅ a'c'`.
theorem segment_add {a b c a' b' c' : Point}
    (hbc : Betw a b c) (hbc' : Betw a' b' c')
    (h1 : Cong a b a' b') (h2 : Cong b c b' c') : Cong a c a' c' := by
  have hba : Cong b a b' a' := cong_trans' (cong_trans' cong_pseudo_refl h1) cong_pseudo_refl
  have h := five_segment hbc hbc' h1 h2 (cong_null a a') hba
  exact cong_trans' (cong_trans' cong_pseudo_refl h) cong_pseudo_refl

/-! ## Checks (honesty audit) — the postulates are class fields, so nothing rests on a Lean `axiom`. -/

#print axioms cong_null
#print axioms segment_add

end Principia
