/-!
# 03-recursion — Skeleton  (THIS IS YOUR FILE)

The type `Expr` and the functions `eval`, `swap`, `size` are GIVEN. Prove the three theorems by
induction — replace each `sorry`.

Run:  make lab C=00-foundations/03-recursion
Try each cold. Stuck? See §5 "Prove it" and §6 "Hints for the skeleton" in `explainer.qmd`.
-/
set_option warningAsError true

namespace Course03

/-- A tiny expression language: a number, or the sum of two expressions. GIVEN. -/
inductive Expr where
  | const : Nat → Expr
  | plus  : Expr → Expr → Expr
deriving Repr, DecidableEq

namespace Expr

/-- Evaluate an expression to a number. GIVEN. -/
def eval : Expr → Nat
  | const n  => n
  | plus a b => eval a + eval b

/-- Swap the two operands of every `plus`. GIVEN. -/
def swap : Expr → Expr
  | const n  => const n
  | plus a b => plus (swap b) (swap a)

/-- Number of constructors in an expression (its "size"). GIVEN. -/
def size : Expr → Nat
  | const _  => 1
  | plus a b => 1 + size a + size b

/-! Your three theorems. Each is an induction on `e`. -/

-- swapping twice gets you back where you started
theorem swap_swap (e : Expr) : swap (swap e) = e := by
  sorry

-- swapping operands doesn't change the value (because `+` is commutative)
theorem eval_swap (e : Expr) : eval (swap e) = eval e := by
  sorry

-- swapping doesn't change the size
theorem size_swap (e : Expr) : size (swap e) = size e := by
  sorry

end Expr
end Course03
