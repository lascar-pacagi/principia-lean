/-!
# 00-setup — Solution  (verified answer key)

`make test` kernel-checks this; `make axioms` audits the keystones below. Peek only when stuck —
and aim to understand *why* each proof works.
-/
namespace Setup

theorem and_swap (p q : Prop) (h : p ∧ q) : q ∧ p :=
  ⟨h.2, h.1⟩

theorem two_plus_two : 2 + 2 = 4 := by
  rfl

theorem zero_add' (n : Nat) : 0 + n = n := by
  induction n with
  | zero      => rfl
  | succ k ih => rw [Nat.add_succ, ih]

/-! ## Checks (Tier-2 computational + honesty audit) -/

#guard 2 + 2 == 4
#print axioms and_swap
#print axioms zero_add'

end Setup
