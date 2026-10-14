/-!
# 02-propositions — Optional solutions

`make test` kernel-checks these proofs; `make axioms` audits them.
See §9 of the lesson for worked explanations.
-/
set_option warningAsError true

namespace Course02.Optional

theorem curry (p q r : Prop) : (p ∧ q → r) ↔ (p → q → r) := by
  constructor
  · intro h
    intro hp
    intro hq
    exact h ⟨hp, hq⟩
  · intro h
    intro hpq
    exact h hpq.1 hpq.2

theorem not_or (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  constructor
  · intro hnpq
    constructor
    · intro hp
      exact hnpq (Or.inl hp)
    · intro hq
      exact hnpq (Or.inr hq)
  · intro h
    intro hpq
    cases hpq with
    | inl hp => exact h.1 hp
    | inr hq => exact h.2 hq

/-! ## Checks — dependencies of the verified proofs -/
#print axioms curry
#print axioms not_or

end Course02.Optional
