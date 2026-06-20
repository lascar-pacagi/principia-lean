/-!
# 01-syntax — Solution  (verified answer key)

`make test` kernel-checks this; `make axioms` audits the keystones. This slice's code graduates into
`Principia.Logic.Syntax`. Read to understand *why*, not to copy.
-/
namespace Principia

inductive Form where
  | var : Nat → Form
  | fls : Form
  | imp : Form → Form → Form
  | and : Form → Form → Form
  | or  : Form → Form → Form
deriving DecidableEq, Repr

namespace Form

def neg (φ : Form) : Form := imp φ fls
def top : Form := neg fls
def iff (a b : Form) : Form := and (imp a b) (imp b a)

def size : Form → Nat
  | var _   => 1
  | fls     => 1
  | imp a b => 1 + size a + size b
  | and a b => 1 + size a + size b
  | or a b  => 1 + size a + size b

scoped infixr:55 " ⇒ " => Form.imp
scoped infixr:65 " ⋏ " => Form.and
scoped infixr:60 " ⋎ " => Form.or
scoped prefix:70 "∼"    => Form.neg
scoped notation:max "⊥" => Form.fls

-- induction over all five constructors; each case is `1 ≤ (something ≥ 1)`, which `omega` closes.
theorem size_pos (φ : Form) : 1 ≤ φ.size := by
  induction φ <;> simp only [size] <;> omega

-- `∼φ = φ ⇒ ⊥`, so `size = 1 + size φ + size ⊥ = size φ + 2`; just unfold and do the arithmetic.
theorem size_neg (φ : Form) : (∼φ).size = φ.size + 2 := by
  simp only [neg, size]; omega

/-! ## Checks (Tier-2 computational + honesty audit) -/

-- formulas are ordinary data we can build and compute with:
#eval (Form.var 0 ⇒ (Form.var 1 ⇒ Form.var 0)).size        -- ⇒ 5
#guard (∼Form.fls) == Form.imp Form.fls Form.fls            -- ∼⊥ unfolds to ⊥ ⇒ ⊥
#guard Form.top.size == 3

#print axioms size_pos
#print axioms size_neg

end Form
end Principia
