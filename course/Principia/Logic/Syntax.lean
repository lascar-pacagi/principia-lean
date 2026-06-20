/-!
# Principia.Logic.Syntax — propositional formulas

The language of the prover (Course 1, slice 1.1). `var : Nat → Form` keeps the type first-order-ready;
`¬`, `⊤`, `↔` are *derived*, so the core has just five constructors to reason about.
-/
namespace Principia

/-- Propositional formulas. -/
inductive Form where
  | var : Nat → Form
  | fls : Form
  | imp : Form → Form → Form
  | and : Form → Form → Form
  | or  : Form → Form → Form
deriving DecidableEq, Repr

namespace Form

/-- Negation: `∼φ := φ ⇒ ⊥`. -/
def neg (φ : Form) : Form := imp φ fls
/-- Truth: `⊤ := ∼⊥`. -/
def top : Form := neg fls
/-- Bi-implication, derived. -/
def iff (a b : Form) : Form := and (imp a b) (imp b a)

/-- The number of constructors in a formula. -/
def size : Form → Nat
  | var _   => 1
  | fls     => 1
  | imp a b => 1 + size a + size b
  | and a b => 1 + size a + size b
  | or a b  => 1 + size a + size b

/-- Object-logic notation, `scoped` so it never clashes with Lean's own `→`/`∧`/`∨`/`⊥`.
    Open it with `open scoped Principia.Form` (or `open Principia.Form`). -/
scoped infixr:55 " ⇒ " => Form.imp
scoped infixr:65 " ⋏ " => Form.and
scoped infixr:60 " ⋎ " => Form.or
scoped prefix:70 "∼"    => Form.neg
scoped notation:max "⊥" => Form.fls

theorem size_pos (φ : Form) : 1 ≤ φ.size := by
  induction φ <;> simp only [size] <;> omega

theorem size_neg (φ : Form) : (∼φ).size = φ.size + 2 := by
  simp only [neg, size]; omega

end Form
end Principia
