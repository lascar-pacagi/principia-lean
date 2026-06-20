/-!
# 01-naturals — Solution  (verified answer key)

`make test` kernel-checks this; `make axioms` audits the keystones. Read to understand *why*, not to copy.
-/
namespace Course01

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat
deriving Repr, DecidableEq

namespace MyNat

def add (m : MyNat) : MyNat → MyNat
  | .zero   => m
  | .succ n => .succ (add m n)

instance : Add MyNat := ⟨add⟩

-- The two defining equations: true by definition, so `rfl`.
@[simp] theorem add_zero (m : MyNat) : m + zero = m := rfl
@[simp] theorem add_succ (m n : MyNat) : m + succ n = succ (m + n) := rfl

@[simp] theorem zero_add (n : MyNat) : zero + n = n := by
  induction n with
  | zero      => rfl
  | succ k ih => rw [add_succ, ih]

@[simp] theorem succ_add (m n : MyNat) : succ m + n = succ (m + n) := by
  induction n with
  | zero      => rfl
  | succ k ih => rw [add_succ, ih, add_succ]

theorem add_comm (m n : MyNat) : m + n = n + m := by
  induction n with
  | zero      => rw [add_zero, zero_add]
  | succ k ih => rw [add_succ, ih, succ_add]

theorem add_assoc (a b c : MyNat) : a + b + c = a + (b + c) := by
  induction c with
  | zero      => rw [add_zero, add_zero]
  | succ k ih => rw [add_succ, add_succ, add_succ, ih]

/-! ## Checks (Tier-2 computational + honesty audit) -/

abbrev one : MyNat := succ zero
abbrev two : MyNat := succ one

#guard (one + one) = two            -- our addition actually computes
#eval two + one                     -- ⇒ succ (succ (succ zero))

-- Once the rules above are @[simp], `simp` chains them automatically:
example (a b : MyNat) : (zero + a) + (b + zero) = a + b := by simp

#print axioms add_comm               -- ⇒ depends on no axioms
#print axioms add_assoc

end MyNat
end Course01
