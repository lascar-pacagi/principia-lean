/-!
# 01-naturals — Optional solutions
The definitions and six proved addition laws below are GIVEN for these exercises.
Run: make lab C=00-foundations/01-naturals
See the lesson's §8 for goals and hints, and §9 for worked corrections.
-/
set_option warningAsError true

namespace Course01.Optional

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat
deriving Repr, DecidableEq

namespace MyNat

def add (m : MyNat) : MyNat → MyNat
  | .zero => m
  | .succ n => .succ (add m n)

instance : Add MyNat := ⟨add⟩

@[simp] theorem add_zero (m : MyNat) : m + zero = m := rfl
@[simp] theorem add_succ (m n : MyNat) : m + succ n = succ (m + n) := rfl

@[simp] theorem zero_add (n : MyNat) : zero + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [add_succ, ih]

@[simp] theorem succ_add (m n : MyNat) : succ m + n = succ (m + n) := by
  induction n with
  | zero => rfl
  | succ k ih => rw [add_succ, ih, add_succ]

theorem add_comm (m n : MyNat) : m + n = n + m := by
  induction n with
  | zero => rw [add_zero, zero_add]
  | succ k ih => rw [add_succ, ih, succ_add]

theorem add_assoc (a b c : MyNat) : a + b + c = a + (b + c) := by
  induction c with
  | zero => rw [add_zero, add_zero]
  | succ k ih => rw [add_succ, add_succ, add_succ, ih]

/-! Your optional exercises. -/

theorem add_right_comm (a b c : MyNat) : a + b + c = a + c + b := by
  rw [add_assoc, add_comm b c, ← add_assoc]

theorem add_two_successors (a b : MyNat) :
    succ (a + zero) + (zero + succ b) = succ (succ (a + b)) := by
  simp

/-! ## Checks -/
#guard succ (succ zero + zero) + (zero + succ (succ zero)) = succ (succ (succ (succ zero)))
#print axioms add_right_comm
#print axioms add_two_successors

end MyNat
end Course01.Optional
