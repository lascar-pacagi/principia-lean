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

/-! ## Section 9 exercises -/

theorem and_reorder (p q r : Prop) (h : p ∧ (q ∧ r)) : q ∧ (p ∧ r) := by
  -- Build q first, then a pair of proofs of p and r.
  -- h.2 is itself a pair, so its components are h.2.1 and h.2.2.
  constructor
  · exact h.2.1
  · constructor
    · exact h.1
    · exact h.2.2

theorem sum_lt : 3 + 4 < 5 + 3 := by
  -- The comparison procedure computes the sums and proves 7 < 8.
  decide

theorem one_add' (n : Nat) : 1 + n = n + 1 := by
  -- At zero, both sides compute to 1. At a successor, expose 1 + k
  -- with the addition definition, then replace it using the induction hypothesis.
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]

/-! ## Checks (Tier-2 computational + honesty audit) -/

#guard 2 + 2 == 4
#print axioms and_swap
#print axioms zero_add'
#guard 3 + 4 < 5 + 3
#guard 1 + 0 == 0 + 1
#guard 1 + 5 == 5 + 1
#print axioms and_reorder
#print axioms sum_lt
#print axioms one_add'

end Setup
