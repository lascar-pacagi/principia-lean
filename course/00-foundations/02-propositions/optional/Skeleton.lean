/-!
# 02-propositions — Optional exercises

Replace each `sorry` with a proof. Run: make lab C=00-foundations/02-propositions
Unfinished optional work doesn't prevent the required lab from passing.
See §8 for goals and hints, and §9 for worked corrections.
-/
set_option warningAsError true

namespace Course02.Optional

theorem curry (p q r : Prop) : (p ∧ q → r) ↔ (p → q → r) := by
  constructor
  . intro hpqir
    intro hp
    intro hq
    exact hpqir ⟨ hp, hq ⟩
  . intro hpiqir
    intro hpq
    exact hpiqir hpq.1 hpq.2

theorem not_or (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  constructor
  . intro nporq
    constructor
    . intro hp
      apply nporq
      exact Or.inl hp
    . intro hq
      apply nporq
      exact Or.inr hq
  . intro npornq
    intro porq
    cases porq with
    | inl hl =>
      exact npornq.1 hl
    | inr hr =>
      exact npornq.2 hr

end Course02.Optional
