import Principia.NatDed.Basic
import Principia.Logic.Semantics

/-!
# 04-soundness — Solution  (verified answer key)

`make test` kernel-checks this; `make axioms` audits it. Graduates into `Principia.NatDed.Soundness`.
Read to understand *why*, not to copy.
-/
open scoped Principia.Form Principia

namespace Principia.Form

theorem sat_cons {v : Nat → Bool} {Γ : List Form} {a : Form}
    (ha : eval v a = true) (hΓ : ∀ ψ ∈ Γ, eval v ψ = true) :
    ∀ ψ ∈ (a :: Γ), eval v ψ = true := by
  intro ψ hψ; cases hψ with
  | head => exact ha
  | tail _ h => exact hΓ ψ h

theorem eval_imp (v : Nat → Bool) (a b : Form) :
    eval v (a ⇒ b) = true ↔ (eval v a = true → eval v b = true) := by
  simp only [eval]; cases eval v a <;> cases eval v b <;> simp
theorem eval_and (v : Nat → Bool) (a b : Form) :
    eval v (a ⋏ b) = true ↔ (eval v a = true ∧ eval v b = true) := by
  simp only [eval]; cases eval v a <;> cases eval v b <;> simp
theorem eval_or (v : Nat → Bool) (a b : Form) :
    eval v (a ⋎ b) = true ↔ (eval v a = true ∨ eval v b = true) := by
  simp only [eval]; cases eval v a <;> cases eval v b <;> simp
theorem byContra_eval {v : Nat → Bool} {a : Form}
    (h : eval v (∼a) = true → eval v Form.fls = true) : eval v a = true := by
  cases hx : eval v a with
  | true  => rfl
  | false => have hna : eval v (∼a) = true := by simp [eval_neg, hx]
             have := h hna; simp [eval] at this

-- Induction on the derivation: one case per inference rule, each shown to preserve truth.
theorem soundness {Γ : List Form} {φ : Form} (d : Γ ⊢ φ) : Entails Γ φ := by
  induction d with
  | ax h           => intro v hΓ; exact hΓ _ h
  | impI d ih      => intro v hΓ; rw [eval_imp]; intro ha; exact ih v (sat_cons ha hΓ)
  | impE d1 d2 ih1 ih2 => intro v hΓ; have h1 := ih1 v hΓ; rw [eval_imp] at h1; exact h1 (ih2 v hΓ)
  | andI d1 d2 ih1 ih2 => intro v hΓ; rw [eval_and]; exact ⟨ih1 v hΓ, ih2 v hΓ⟩
  | andE₁ d ih     => intro v hΓ; have h := ih v hΓ; rw [eval_and] at h; exact h.1
  | andE₂ d ih     => intro v hΓ; have h := ih v hΓ; rw [eval_and] at h; exact h.2
  | orI₁ d ih      => intro v hΓ; rw [eval_or]; exact Or.inl (ih v hΓ)
  | orI₂ d ih      => intro v hΓ; rw [eval_or]; exact Or.inr (ih v hΓ)
  | orE dor dl dr ihor ihl ihr =>
      intro v hΓ; have hor := ihor v hΓ; rw [eval_or] at hor
      cases hor with
      | inl ha => exact ihl v (sat_cons ha hΓ)
      | inr hb => exact ihr v (sat_cons hb hΓ)
  | flsE d ih      => intro v hΓ; have h := ih v hΓ; simp [eval] at h
  | raa d ih       => intro v hΓ; apply byContra_eval; intro hna; exact ih v (sat_cons hna hΓ)

theorem tautology_of_proof {φ : Form} (d : [] ⊢ φ) : Tautology φ :=
  fun v => soundness d v (by intro ψ h; cases h)

/-! ## Checks (Tier-2 + honesty audit) -/

-- A proof tree you build → a tautology you get for free (Milestone M1 in action):
example (φ : Form) : Tautology (φ ⇒ φ) :=
  tautology_of_proof (.impI (.ax (a := φ) (by simp)))

#print axioms soundness
#print axioms tautology_of_proof

end Principia.Form
