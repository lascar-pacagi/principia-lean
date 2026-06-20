import Principia.Logic.Syntax

/-!
# 03-deduction — Skeleton  (THIS IS YOUR FILE)

The derivation type `Deriv` (notation `Γ ⊢ φ`) is GIVEN — its constructors are the natural-deduction
rules. Build the four derivations by replacing each `sorry`.

Tip that you'll need: write `Deriv.ax (a := <the exact formula>) (by simp)` for an assumption — naming
the formula is what lets `simp` discharge the membership. See §6 for why.

Run:  make lab C=01-natural-deduction/03-deduction
Stuck? See §5 "Prove it" and §6 "Hints for the skeleton" in `explainer.qmd`.
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
  | flsE  {Γ a}     : Deriv Γ Form.fls → Deriv Γ a
  | raa   {Γ a}     : Deriv (Form.neg a :: Γ) Form.fls → Deriv Γ a

scoped notation:40 Γ " ⊢ " φ => Deriv Γ φ

/-! Build these four derivations. -/

-- identity
def dId (φ : Form) : [] ⊢ (φ ⇒ φ) := sorry

-- commutativity of ∧ (as an implication)
def dAndComm (φ ψ : Form) : [] ⊢ ((φ ⋏ ψ) ⇒ (ψ ⋏ φ)) := sorry

-- modus ponens, packaged as a theorem
def dMP (φ ψ : Form) : [] ⊢ (φ ⇒ (φ ⇒ ψ) ⇒ ψ) := sorry

-- Peirce's law — needs the classical `raa` rule
def peirce (φ ψ : Form) : [] ⊢ (((φ ⇒ ψ) ⇒ φ) ⇒ φ) := sorry

end Principia
