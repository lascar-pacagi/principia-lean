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
  | falsum : Form
  | imp : Form → Form → Form
  | and : Form → Form → Form
  | or  : Form → Form → Form
deriving DecidableEq, Repr

namespace Form

/-- Negation is not primitive: `∼φ` is just `φ ⇒ ⊥`. GIVEN. -/
def neg (φ : Form) : Form := imp φ falsum
/-- Truth `⊤` is `∼⊥`. GIVEN. -/
def top : Form := neg falsum
/-- Bi-implication, derived. GIVEN. -/
def iff (a b : Form) : Form := and (imp a b) (imp b a)

/-- The number of constructors in a formula. GIVEN. -/
def size : Form → Nat
  | var _   => 1
  | falsum     => 1
  | imp a b => 1 + size a + size b
  | and a b => 1 + size a + size b
  | or a b  => 1 + size a + size b

/-!
These declarations give readable symbols to the formula constructors and definitions:
`a ⇒ b` means `Form.imp a b`; similarly, `⋏` means conjunction, `⋎` disjunction,
`∼a` negation, and `⊥` falsehood. The `=>` here specifies what each notation expands to.

`infixr` places a symbol between two arguments and groups repeated uses to the right:
`a ⇒ b ⇒ c` means `a ⇒ (b ⇒ c)`. `prefix` places a symbol before its argument.
The numbers are parsing priorities: a larger number binds more tightly. Thus
`∼a ⋏ b ⋎ c ⇒ d` means `(((∼a) ⋏ b) ⋎ c) ⇒ d`. Parentheses can override this order.
`notation:max` gives the standalone symbol `⊥` the highest parsing priority.

`scoped` makes these notations available inside this namespace. Elsewhere, activate
them with `open scoped Principia.Form`; this does not open its other names.
-/
scoped infixr:55 " ⇒ " => Form.imp
scoped infixr:65 " ⋏ " => Form.and
scoped infixr:60 " ⋎ " => Form.or
scoped prefix:70 "∼"    => Form.neg
scoped notation:max "⊥" => Form.falsum

/-! Your two lemmas. -/

theorem size_pos (φ : Form) : 1 ≤ φ.size := by
  induction φ with
  | var _ =>
    simp [size]
  | falsum =>
    simp [size]
  | imp a b iha ihb =>
    simp [size]
    omega
  | and a b iha ihb =>
    simp [size]
    omega
  | or a b iha ihb =>
    simp [size]
    omega

theorem size_neg (φ : Form) : (∼φ).size = φ.size + 2 := by
  simp [neg, size]
  omega

end Form
end Principia
