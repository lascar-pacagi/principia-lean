import Principia.Euclid.Basic

/-!
# Principia.Euclid.Betweenness — order, the five-segment axiom (SAS), and its first consequences (Course 4, 4.2)

We extend the congruence system of `Euclid.Basic` with Tarski's second primitive, **betweenness**
`Betw a b c` ("`b` lies between `a` and `c`"), plus two more postulates:

* **segment construction** — any ray can be extended by a copy of any segment; and
* the **five-segment axiom** — Tarski's angle-free encoding of Euclid's **SAS** (I.4): instead of saying
  "the included angles are equal", it fixes a fourth point's distances, pinning the configuration's shape
  without ever measuring an angle.

From these we derive the foundational facts the rest of plane geometry rests on: any two null segments are
congruent (`cong_null`), degenerate betweenness (`betw_trivial`), and **segment addition** (`segment_add`,
Tarski's l2_11) — congruent pieces laid end to end yield congruent wholes.
-/
namespace Principia

open EuclidPlane

/-- Tarski's congruence-and-order plane: `EuclidPlane` (segment congruence) plus betweenness, segment
    construction, and the five-segment (SAS) axiom. -/
class EuclidPlane2 (Point : Type) extends EuclidPlane Point where
  /-- `Betw a b c`: point `b` lies (non-strictly) between `a` and `c`. -/
  Betw : Point → Point → Point → Prop
  /-- a point between `a` and `a` is `a` itself -/
  betw_identity : ∀ {a b : Point}, Betw a b a → a = b
  /-- **segment construction**: extend ray `ab` by a segment congruent to `cd`. -/
  segment_construction : ∀ (a b c d : Point), ∃ e, Betw a b e ∧ Cong b e c d
  /-- **five-segment axiom** (Euclid's SAS, angle-free): if two point-triples `abc`, `a'b'c'` are
      collinear with `ab ≅ a'b'`, `bc ≅ b'c'`, and a fourth point matches via `ad ≅ a'd'`, `bd ≅ b'd'`,
      then the last distances match too: `cd ≅ c'd'`. -/
  five_segment : ∀ {a b c d a' b' c' d' : Point},
    Betw a b c → Betw a' b' c' → Cong a b a' b' → Cong b c b' c' →
    Cong a d a' d' → Cong b d b' d' → Cong c d c' d'

open EuclidPlane2
variable {Point : Type} [EuclidPlane2 Point]

/-- Any two null ("zero-length") segments are congruent. -/
theorem cong_null (a b : Point) : Cong a a b b := by
  obtain ⟨e, _, he⟩ := segment_construction a a b b
  have : a = e := cong_identity he          -- `Cong a e b b` ⇒ `a = e`
  subst this; exact he

/-- Degenerate betweenness: `b` lies between `a` and itself. -/
theorem betw_trivial (a b : Point) : Betw a b b := by
  obtain ⟨e, hbe, he⟩ := segment_construction a b b b
  have : b = e := cong_identity he
  subst this; exact hbe

/-- **Segment addition** (Tarski l2_11): if `b` and `b'` split `ac`, `a'c'` into congruent pieces
    (`ab ≅ a'b'`, `bc ≅ b'c'`), the wholes are congruent (`ac ≅ a'c'`). The five-segment axiom applied
    with the fourth point taken to be `a` itself. -/
theorem segment_add {a b c a' b' c' : Point}
    (hbc : Betw a b c) (hbc' : Betw a' b' c')
    (h1 : Cong a b a' b') (h2 : Cong b c b' c') : Cong a c a' c' := by
  have hba : Cong b a b' a' := cong_trans' (cong_trans' cong_pseudo_refl h1) cong_pseudo_refl
  have h := five_segment hbc hbc' h1 h2 (cong_null a a') hba    -- `Cong c a c' a'`
  exact cong_trans' (cong_trans' cong_pseudo_refl h) cong_pseudo_refl

end Principia
