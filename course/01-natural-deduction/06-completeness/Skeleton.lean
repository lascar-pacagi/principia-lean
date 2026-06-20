import Principia.NatDed.Kalmar
import Principia.NatDed.Soundness

/-!
# 06-completeness — Skeleton  (THIS IS YOUR FILE)

The machinery is GIVEN (imported): `kalmar v n φ _ : (eval v φ = true → litCtx v n ⊢ φ) × …` and
`elim n φ : (∀ v, litCtx v n ⊢ φ) → ([] ⊢ φ)`. Assemble the two final results — replace each `sorry`.

Run:  make lab C=01-natural-deduction/06-completeness
Stuck? See §5 "Prove it" and §6 "Hints for the skeleton" in `explainer.qmd`.
-/
set_option warningAsError true
open scoped Principia.Form Principia

namespace Principia.Form

-- Completeness: for each valuation, `kalmar` gives a proof from that valuation's literals (the formula
-- is true everywhere, since it's a tautology); `elim` collapses all the literal contexts to `[]`.
noncomputable def completeness {φ : Form} (h : Tautology φ) : [] ⊢ φ := by
  sorry

-- The loop closes: `mp` is soundness (`tautology_of_proof`), `mpr` is completeness.
theorem provable_iff_tautology {φ : Form} : Nonempty ([] ⊢ φ) ↔ Tautology φ := by
  sorry

end Principia.Form
