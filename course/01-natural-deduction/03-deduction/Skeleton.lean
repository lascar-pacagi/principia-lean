import Principia.Logic.Syntax

/-!
# 03-deduction — Your exercises

Run: make lab C=01-natural-deduction/03-deduction
See §6 for statements, §7 for hints, and §8 for worked corrections.
Optional exercises have their own skeleton and answer key under optional/.
-/
set_option warningAsError true
open scoped Principia.Form

namespace Principia

inductive Deriv : List Form → Form → Type where
  | ax    {Γ a}     : a ∈ Γ → Deriv Γ a
  | impI  {Γ a b}   : Deriv (a :: Γ) b → Deriv Γ (a ⇒ b)
  | impE  {Γ a b}   : Deriv Γ (a ⇒ b) → Deriv Γ a → Deriv Γ b
  | andI  {Γ a b}   : Deriv Γ a → Deriv Γ b → Deriv Γ (a ⋏ b)
  | andE₁ {Γ a b}   : Deriv Γ (a ⋏ b) → Deriv Γ a
  | andE₂ {Γ a b}   : Deriv Γ (a ⋏ b) → Deriv Γ b
  | orI₁  {Γ a b}   : Deriv Γ a → Deriv Γ (a ⋎ b)
  | orI₂  {Γ a b}   : Deriv Γ b → Deriv Γ (a ⋎ b)
  | orE   {Γ a b c} : Deriv Γ (a ⋎ b) → Deriv (a :: Γ) c → Deriv (b :: Γ) c → Deriv Γ c
  | flsE  {Γ a}     : Deriv Γ Form.falsum → Deriv Γ a
  | raa   {Γ a}     : Deriv (Form.neg a :: Γ) Form.falsum → Deriv Γ a

scoped notation:40 Γ " ⊢ " φ => Deriv Γ φ

/-! Build these four derivations. -/

def derive_identity (φ : Form) : [] ⊢ (φ ⇒ φ) := sorry

def derive_and_commutativity (φ ψ : Form) : [] ⊢ ((φ ⋏ ψ) ⇒ (ψ ⋏ φ)) := sorry

def derive_modus_ponens (φ ψ : Form) : [] ⊢ (φ ⇒ (φ ⇒ ψ) ⇒ ψ) := sorry

def derive_peirce (φ ψ : Form) : [] ⊢ (((φ ⇒ ψ) ⇒ φ) ⇒ φ) := sorry

end Principia
