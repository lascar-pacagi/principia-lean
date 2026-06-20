/-!
# 01-equilateral — Solution  (verified answer key)

`make test` kernel-checks this; `make axioms` audits it. Graduates into `Principia.Euclid.Basic`.
-/
namespace Principia

class EuclidPlane (Point : Type) where
  Cong : Point → Point → Point → Point → Prop
  cong_pseudo_refl : ∀ {a b}, Cong a b b a
  cong_trans : ∀ {a b p q r s}, Cong a b p q → Cong a b r s → Cong p q r s
  cong_identity : ∀ {a b c}, Cong a b c c → a = b
  circles_meet : ∀ (a b : Point), ∃ c, Cong a c a b ∧ Cong b c b a

open EuclidPlane
variable {Point : Type} [EuclidPlane Point]

-- two copies of `cong_pseudo_refl` (`Cong b a a b`) feed Tarski transitivity to give `Cong a b a b`.
theorem cong_refl (a b : Point) : Cong a b a b := cong_trans cong_pseudo_refl cong_pseudo_refl
-- from `Cong a b c d` and `Cong a b a b`, transitivity gives `Cong c d a b`.
theorem cong_symm {a b c d : Point} (h : Cong a b c d) : Cong c d a b := cong_trans h (cong_refl a b)
-- flip the first to `Cong c d a b`, then it shares `c d` with `h2`.
theorem cong_trans' {a b c d e f : Point} (h1 : Cong a b c d) (h2 : Cong c d e f) : Cong a b e f :=
  cong_trans (cong_symm h1) h2

-- `circles_meet` hands us the apex `c`; the three side-equalities are bookkeeping with the lemmas above.
theorem prop_I1 (a b : Point) : ∃ c, Cong a b a c ∧ Cong a b b c ∧ Cong a c b c := by
  obtain ⟨c, hca, hcb⟩ := circles_meet a b          -- hca : ac ≅ ab,  hcb : bc ≅ ba
  refine ⟨c, cong_symm hca, ?_, ?_⟩
  · exact cong_trans' cong_pseudo_refl (cong_symm hcb)                      -- ab ≅ ba ≅ bc
  · exact cong_trans' hca (cong_trans' cong_pseudo_refl (cong_symm hcb))    -- ac ≅ ab ≅ bc

/-! ## Checks (honesty audit + consistency)

`#print axioms` confirms the geometric postulates are *hypotheses* (class fields), not Lean `axiom`s —
`prop_I1` rests on nothing. And the axiom system is *consistent*: the one-point space is a (degenerate)
model, so the theorems aren't vacuous. -/

#print axioms prop_I1

instance : EuclidPlane Unit where      -- a trivial model ⇒ the axioms are consistent
  Cong _ _ _ _ := True
  cong_pseudo_refl := trivial
  cong_trans _ _ := trivial
  cong_identity _ := rfl
  circles_meet _ _ := ⟨(), trivial, trivial⟩

end Principia
