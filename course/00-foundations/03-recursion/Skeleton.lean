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

/-! Your three theorems. -/

theorem swap_swap (e : Expr) : swap (swap e) = e := by
  induction e with
  | const n => rfl
  | plus a b iha ihb =>
    simp only [swap]
    rw [iha]
    rw [ihb]

theorem eval_swap (e : Expr) : eval (swap e) = eval e := by
  induction e with
  | const n => rfl
  | plus a b iha ihb =>
    simp only [swap]
    simp only [eval]
    rw [iha]
    rw [ihb]
    apply Nat.add_comm

theorem size_swap (e : Expr) : size (swap e) = size e := by
  induction e with
  | const n => rfl
  | plus a b iha ihb =>
    simp only [swap, size]
    rw [iha, ihb]
    rw [Nat.add_assoc, Nat.add_comm b.size a.size]
    rw [Nat.add_assoc]

end Expr
end Course03
