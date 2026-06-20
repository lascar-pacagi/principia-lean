import Principia.NatDed.Kalmar
import Principia.NatDed.Soundness

/-!
# 06-completeness — Solution  (verified answer key)

`make test` kernel-checks this; `make axioms` audits it. Graduates into `Principia.NatDed.Completeness`.
Read to understand *why*, not to copy.
-/
open scoped Principia.Form Principia

namespace Principia.Form

-- Pick `n = maxVar φ` so every atom of `φ` is covered. For each `v`, `(kalmar …).1 (h v)` proves `φ`
-- from `litCtx v n` (using `h v : eval v φ = true`); `elim` collapses all those contexts to `[]`.
noncomputable def completeness {φ : Form} (h : Tautology φ) : [] ⊢ φ :=
  elim φ.maxVar φ (fun v => (kalmar v φ.maxVar φ (Nat.le_refl _)).1 (h v))

theorem provable_iff_tautology {φ : Form} : Nonempty ([] ⊢ φ) ↔ Tautology φ :=
  ⟨fun ⟨d⟩ => tautology_of_proof d, fun h => ⟨completeness h⟩⟩

/-! ## Checks (Tier-1 + honesty audit)

The headline: completeness produces derivations the slice-1.5 prover *couldn't* find — e.g.
`(p ⋏ q) ⇒ p`, which is valid but needs ∧-elimination. -/

example : Nonempty ([] ⊢ (Form.var 0 ⇒ Form.var 0)) := ⟨completeness (taut_imp_self _)⟩

example : Nonempty ([] ⊢ ((Form.var 0 ⋏ Form.var 1) ⇒ Form.var 0)) :=
  ⟨completeness (by intro v; simp only [eval]; cases v 0 <;> cases v 1 <;> rfl)⟩

#print axioms completeness
#print axioms provable_iff_tautology

end Principia.Form
