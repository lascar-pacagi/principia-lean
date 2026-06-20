/-!
# 03-recursion — Solution  (verified answer key)

`make test` kernel-checks this; `make axioms` audits the keystones. Read to understand *why*, not to copy.
-/
namespace Course03

inductive Expr where
  | const : Nat → Expr
  | plus  : Expr → Expr → Expr
deriving Repr, DecidableEq

namespace Expr

def eval : Expr → Nat
  | const n  => n
  | plus a b => eval a + eval b

def swap : Expr → Expr
  | const n  => const n
  | plus a b => plus (swap b) (swap a)

def size : Expr → Nat
  | const _  => 1
  | plus a b => 1 + size a + size b

-- `simp only [swap, …]` unfolds the function's defining equations; `iha`/`ihb` are the two
-- induction hypotheses (one per recursive child of `plus`); `omega` finishes the arithmetic.
theorem swap_swap (e : Expr) : swap (swap e) = e := by
  induction e with
  | const n          => rfl
  | plus a b iha ihb => simp only [swap, iha, ihb]

theorem eval_swap (e : Expr) : eval (swap e) = eval e := by
  induction e with
  | const n          => rfl
  | plus a b iha ihb => simp only [swap, eval, iha, ihb]; omega

theorem size_swap (e : Expr) : size (swap e) = size e := by
  induction e with
  | const n          => rfl
  | plus a b iha ihb => simp only [swap, size, iha, ihb]; omega

/-! ## Checks (Tier-2 computational + honesty audit) -/

#eval eval (Expr.plus (Expr.const 2) (Expr.plus (Expr.const 3) (Expr.const 4)))  -- ⇒ 9
#guard size (Expr.plus (Expr.const 2) (Expr.const 3)) == 3
#guard eval (swap (Expr.plus (Expr.const 1) (Expr.const 2))) == eval (Expr.plus (Expr.const 1) (Expr.const 2))

#print axioms swap_swap        -- accepted axioms only (propext / Quot.sound) — never sorryAx
#print axioms eval_swap
#print axioms size_swap

end Expr
end Course03
