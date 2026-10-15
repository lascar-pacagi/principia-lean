/-!
# 03-recursion — Optional solutions

The expression type, functions, and three proved laws below are GIVEN.
Run: make lab C=00-foundations/03-recursion
See §8 for goals and hints, and §9 for worked corrections.
-/
set_option warningAsError true

namespace Course03.Optional

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

theorem swap_swap (e : Expr) : swap (swap e) = e := by
  induction e with
  | const n => rfl
  | plus a b iha ihb =>
    simp only [swap]
    rw [iha, ihb]

theorem eval_swap (e : Expr) : eval (swap e) = eval e := by
  induction e with
  | const n => rfl
  | plus a b iha ihb =>
    simp only [swap, eval, iha, ihb]
    omega

theorem size_swap (e : Expr) : size (swap e) = size e := by
  induction e with
  | const n => rfl
  | plus a b iha ihb =>
    simp only [swap, size, iha, ihb]
    omega

/-! Optional exercise solutions. -/

theorem eval_swap_swap (e : Expr) : eval (swap (swap e)) = eval e := by
  rw [swap_swap]

def numLeaves : Expr → Nat
  | const _ => 1
  | plus a b => numLeaves a + numLeaves b

theorem leaves_swap (e : Expr) : numLeaves (swap e) = numLeaves e := by
  induction e with
  | const n => rfl
  | plus a b iha ihb =>
    simp only [swap, numLeaves, iha, ihb]
    omega

/-! ## Checks -/
#guard numLeaves (plus (const 2) (plus (const 3) (const 4))) == 3
#guard size (plus (const 2) (plus (const 3) (const 4))) == 5
#print axioms eval_swap_swap
#print axioms leaves_swap

end Expr
end Course03.Optional
