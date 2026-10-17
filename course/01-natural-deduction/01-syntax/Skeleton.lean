/-!
# 01-syntax — Your exercises

Run: make lab C=01-natural-deduction/01-syntax
See §6 for statements, §7 for hints, and §8 for worked corrections.
Optional exercises have their own skeleton and answer key under optional/.
-/
set_option warningAsError true

namespace Principia

/-- Propositional formulas. `var n` is the n-th atom; `¬`, `⊤`, `↔` are derived (below).
    Indices provide arbitrarily many propositional atom names. GIVEN. -/
inductive Form where
  | var : Nat → Form
  | fls : Form
  | imp : Form → Form → Form
  | and : Form → Form → Form
  | or  : Form → Form → Form
deriving DecidableEq, Repr

namespace Form

/-- Negation is not primitive: `∼φ` is just `φ ⇒ ⊥`. GIVEN. -/
def neg (φ : Form) : Form := imp φ fls
/-- Truth `⊤` is `∼⊥`. GIVEN. -/
def top : Form := neg fls
/-- Bi-implication, derived. GIVEN. -/
def iff (a b : Form) : Form := and (imp a b) (imp b a)

/-- The number of constructors in a formula. GIVEN. -/
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

/-! Your two lemmas. -/

theorem size_pos (φ : Form) : 1 ≤ φ.size := by
  sorry

theorem size_neg (φ : Form) : (∼φ).size = φ.size + 2 := by
  sorry

end Form
end Principia
