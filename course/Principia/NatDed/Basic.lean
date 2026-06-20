import Principia.Logic.Syntax

/-!
# Principia.NatDed.Basic — natural deduction (Course 1, slice 1.3)

The provability relation `Γ ⊢ φ` as an **inductive type**: its constructors are exactly the inference
rules of natural deduction (`04-logic §2`). A *value* of `Γ ⊢ φ` is a proof tree. The `raa` rule makes
the system **classical** (so Peirce's law and excluded middle are derivable). `¬`/`⊤`/`↔` are derived,
so they need no rules of their own — negation rules fall out of `⇒`/`⊥`.
-/
namespace Principia

open scoped Principia.Form

/-- `Γ ⊢ φ`: a natural-deduction derivation of `φ` from assumptions `Γ`. -/
inductive Deriv : List Form → Form → Type where
  /-- assumption: anything in the context is provable -/
  | ax    {Γ a}     : a ∈ Γ → Deriv Γ a
  /-- →-introduction: discharge an assumption -/
  | impI  {Γ a b}   : Deriv (a :: Γ) b → Deriv Γ (a ⇒ b)
  /-- →-elimination (modus ponens) -/
  | impE  {Γ a b}   : Deriv Γ (a ⇒ b) → Deriv Γ a → Deriv Γ b
  /-- ∧-introduction -/
  | andI  {Γ a b}   : Deriv Γ a → Deriv Γ b → Deriv Γ (a ⋏ b)
  /-- ∧-elimination (left) -/
  | andE₁ {Γ a b}   : Deriv Γ (a ⋏ b) → Deriv Γ a
  /-- ∧-elimination (right) -/
  | andE₂ {Γ a b}   : Deriv Γ (a ⋏ b) → Deriv Γ b
  /-- ∨-introduction (left) -/
  | orI₁  {Γ a b}   : Deriv Γ a → Deriv Γ (a ⋎ b)
  /-- ∨-introduction (right) -/
  | orI₂  {Γ a b}   : Deriv Γ b → Deriv Γ (a ⋎ b)
  /-- ∨-elimination (case split) -/
  | orE   {Γ a b c} : Deriv Γ (a ⋎ b) → Deriv (a :: Γ) c → Deriv (b :: Γ) c → Deriv Γ c
  /-- ⊥-elimination (ex falso quodlibet) -/
  | flsE  {Γ a}     : Deriv Γ Form.fls → Deriv Γ a
  /-- reductio ad absurdum (the classical rule): assume `∼a`, derive `⊥` -/
  | raa   {Γ a}     : Deriv (Form.neg a :: Γ) Form.fls → Deriv Γ a

@[inherit_doc] scoped notation:40 Γ " ⊢ " φ => Deriv Γ φ

end Principia
