/-!
# 01-syntax — Skeleton  (THIS IS YOUR FILE)

The formula type `Form`, its notation, the derived connectives, and `size` are GIVEN. Prove the two
structural lemmas — replace each `sorry`.

Run:  make lab C=01-natural-deduction/01-syntax
Stuck? See §5 "Prove it" and §6 "Hints for the skeleton" in `explainer.qmd`.
-/
set_option warningAsError true

namespace Principia

/-- Propositional formulas. `var n` is the n-th atom; `¬`, `⊤`, `↔` are derived (below).
    Choosing `var : Nat → Form` (rather than a fixed list) keeps us first-order-ready. GIVEN. -/
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

-- every formula has at least one constructor
theorem size_pos (φ : Form) : 1 ≤ φ.size := by
  sorry

-- `∼φ` is `φ ⇒ ⊥`, so it has two more constructors than `φ`
theorem size_neg (φ : Form) : (∼φ).size = φ.size + 2 := by
  sorry

end Form
end Principia
