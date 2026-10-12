/-!
# 01-naturals — Skeleton  (THIS IS YOUR FILE)

Build the naturals from nothing and prove their addition laws. The TYPE (`MyNat`) and the DEFINITION of
addition (`add`) and the three worked results are GIVEN; prove the three exercise theorems below.

Run:  make lab C=00-foundations/01-naturals
Try each cold. Stuck? See §5 "Prove it" and §6 "Hints for the skeleton" in `explainer.qmd`.
-/
set_option warningAsError true

namespace Course01

/-- The natural numbers, Peano-style: every number is `zero` or the `succ`essor of one. GIVEN. -/
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat
deriving Repr, DecidableEq

namespace MyNat

/-- Addition, by recursion on the *second* argument. GIVEN. -/
def add (m : MyNat) : MyNat → MyNat
  | .zero   => m
  | .succ n => .succ (add m n)

instance : Add MyNat := ⟨add⟩

/-! Given results from the lesson's worked examples. -/

@[simp] theorem add_zero (m : MyNat) : m + zero = m := rfl

@[simp] theorem add_succ (m n : MyNat) : m + succ n = succ (m + n) := rfl

@[simp] theorem zero_add (n : MyNat) : zero + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [add_succ, ih]

/-! Your three exercises. Later ones may use earlier ones. -/

@[simp] theorem succ_add (m n : MyNat) : succ m + n = succ (m + n) := by
  induction n with
  | zero => rw [add_zero, add_zero]
  | succ k ih => rw [add_succ, ih, add_succ]

theorem add_comm (m n : MyNat) : m + n = n + m := by
  induction n with
  | zero => rw [add_zero, zero_add]
  | succ k ih => rw [add_succ, ih, succ_add]

theorem add_assoc (a b c : MyNat) : a + b + c = a + (b + c) := by
  induction c with
  | zero => rw [add_zero, add_zero]
  | succ k ih => rw [add_succ, ih, add_succ, add_succ]

end MyNat
end Course01
