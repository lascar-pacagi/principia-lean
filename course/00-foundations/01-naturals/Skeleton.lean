/-!
# 01-naturals — Skeleton  (THIS IS YOUR FILE)

Build the naturals from nothing and prove their addition laws. The TYPE (`MyNat`) and the DEFINITION of
addition (`add`) are GIVEN; your job is the six theorems below — replace each `sorry`.

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

/-! Your six theorems. Prove them top to bottom — later ones may use earlier ones. -/

@[simp] theorem add_zero (m : MyNat) : m + zero = m := by
  sorry

@[simp] theorem add_succ (m n : MyNat) : m + succ n = succ (m + n) := by
  sorry

@[simp] theorem zero_add (n : MyNat) : zero + n = n := by
  sorry

@[simp] theorem succ_add (m n : MyNat) : succ m + n = succ (m + n) := by
  sorry

theorem add_comm (m n : MyNat) : m + n = n + m := by
  sorry

theorem add_assoc (a b c : MyNat) : a + b + c = a + (b + c) := by
  sorry

end MyNat
end Course01
