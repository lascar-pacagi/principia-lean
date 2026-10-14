/-!
# 02-propositions — Skeleton  (THIS IS YOUR FILE)

One theorem per connective. Replace each `sorry`. All are constructive (no classical logic needed).

Run:  make lab C=00-foundations/02-propositions
Try each cold. Stuck? See §5 "Prove it" and §6 "Hints for the skeleton" in `explainer.qmd`.
-/
set_option warningAsError true

namespace Course02


theorem imp_trans (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r := by
  intro hp
  have hq : q := hpq hp
  have hr : r := hqr hq
  exact hr

/-!
theorem imp_trans (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r := by
  intro hp
  apply hqr
  apply hpq
  exact hp
-/

theorem and_reassoc (p q r : Prop) (h : p ∧ (q ∧ r)) : (p ∧ q) ∧ r := by
  apply And.intro
  . apply And.intro
    . exact h.1
    . exact h.2.1
  . exact h.2.2

theorem or_comm' (p q : Prop) (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp =>
    right
    exact hp
  | inr hq =>
    left
    exact hq

theorem contrapositive (p q : Prop) (h : p → q) : ¬q → ¬p := by
  intro nhq
  intro hp
  apply nhq
  apply h
  exact hp

theorem iff_symm (p q : Prop) (h : p ↔ q) : q ↔ p := by
  constructor
  . exact h.mpr
  . exact h.mp

theorem exists_imp (α : Type) (p q : α → Prop)
    (h : ∀ x, p x → q x) (hex : ∃ x, p x) : ∃ x, q x := by
  obtain ⟨ x, hexx ⟩ := hex
  have hx := h x
  have qx := hx hexx
  exact ⟨ x, qx ⟩

theorem forall_and (α : Type) (P Q : α → Prop)
    (hP : ∀ x, P x) (hQ : ∀ x, Q x) : ∀ x, P x ∧ Q x := by
  intro x
  exact ⟨ hP x, hQ x ⟩


end Course02
