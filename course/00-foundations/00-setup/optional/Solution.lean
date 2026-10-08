/-!
# 00-setup — Optional exercise solutions

`make test` checks these proofs; `make axioms` audits them.
See §12 of the lesson for the worked explanations.
-/
set_option warningAsError true

namespace Setup.Optional

theorem or_swap (p q : Prop) (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

theorem add_zero' (n : Nat) : n + 0 = n := by
  rfl

theorem add_assoc' (a b n : Nat) : (a + b) + n = a + (b + n) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Nat.add_succ, Nat.add_succ, ih, Nat.add_succ]

/-! ## Checks -/

#guard 5 + 0 == 5
#guard (2 + 3) + 0 == 2 + (3 + 0)
#guard (2 + 3) + 4 == 2 + (3 + 4)
#print axioms or_swap
#print axioms add_zero'
#print axioms add_assoc'

end Setup.Optional
