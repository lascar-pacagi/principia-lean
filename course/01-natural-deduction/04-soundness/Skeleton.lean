import Principia.NatDed.Basic
import Principia.Logic.Semantics

/-!
# 04-soundness — Your exercises

Run: make lab C=01-natural-deduction/04-soundness
See §6 for statements, §7 for hints, and §8 for worked corrections.
Optional exercises have their own skeleton and answer key under optional/.
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

theorem soundness {Γ : List Form} {φ : Form} (d : Γ ⊢ φ) : Entails Γ φ := by
  sorry

theorem tautology_of_proof {φ : Form} (d : [] ⊢ φ) : Tautology φ := by
  sorry

end Principia.Form
