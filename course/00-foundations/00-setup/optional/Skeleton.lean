/-!
# 00-setup — Optional exercises

Replace each `sorry` with a proof. Run: make lab C=00-foundations/00-setup
Unfinished optional exercises do not prevent the required lab from passing.
The lesson's §11 states the exercises; §12 explains the solutions.
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
  | succ k ih => rw [Nat.add_succ, Nat.add_succ, Nat.add_succ, ih]

end Setup.Optional
