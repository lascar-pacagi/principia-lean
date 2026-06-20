import Principia.NatDed.Basic
import Principia.Logic.Semantics

/-!
# 04-soundness — Skeleton  (THIS IS YOUR FILE)

The Boolean helper lemmas are GIVEN. Prove `soundness` (induction on the derivation) and the corollary
`tautology_of_proof` — replace each `sorry`.

Run:  make lab C=01-natural-deduction/04-soundness
Stuck? See §4 "Prove it" and §5 "Hints for the skeleton" in `explainer.qmd`.
-/
set_option warningAsError true
open scoped Principia.Form Principia

namespace Principia.Form

/-- GIVEN: extend a satisfied context by a true formula. -/
theorem sat_cons {v : Nat → Bool} {Γ : List Form} {a : Form}
    (ha : eval v a = true) (hΓ : ∀ ψ ∈ Γ, eval v ψ = true) :
    ∀ ψ ∈ (a :: Γ), eval v ψ = true := by
  intro ψ hψ; cases hψ with
  | head => exact ha
  | tail _ h => exact hΓ ψ h

/-- GIVEN: how `⇒`/`⋏`/`⋎` truth values behave. -/
theorem eval_imp (v : Nat → Bool) (a b : Form) :
    eval v (a ⇒ b) = true ↔ (eval v a = true → eval v b = true) := by
  simp only [eval]; cases eval v a <;> cases eval v b <;> simp
theorem eval_and (v : Nat → Bool) (a b : Form) :
    eval v (a ⋏ b) = true ↔ (eval v a = true ∧ eval v b = true) := by
  simp only [eval]; cases eval v a <;> cases eval v b <;> simp
theorem eval_or (v : Nat → Bool) (a b : Form) :
    eval v (a ⋎ b) = true ↔ (eval v a = true ∨ eval v b = true) := by
  simp only [eval]; cases eval v a <;> cases eval v b <;> simp
/-- GIVEN: the classical core for the `raa` rule. -/
theorem byContra_eval {v : Nat → Bool} {a : Form}
    (h : eval v (∼a) = true → eval v Form.fls = true) : eval v a = true := by
  cases hx : eval v a with
  | true  => rfl
  | false => have hna : eval v (∼a) = true := by simp [eval_neg, hx]
             have := h hna; simp [eval] at this

/-! Your two theorems. -/

-- Soundness: induct on `d`; in each case show the conclusion's value is `true`, using the helpers
-- above (and `ih`/`sat_cons` for the rules that extend the context: impI, orE, raa).
theorem soundness {Γ : List Form} {φ : Form} (d : Γ ⊢ φ) : Entails Γ φ := by
  sorry

-- A closed proof certifies a tautology (specialise soundness to the empty context).
theorem tautology_of_proof {φ : Form} (d : [] ⊢ φ) : Tautology φ := by
  sorry

end Principia.Form
