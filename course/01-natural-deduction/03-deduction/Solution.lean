import Principia.Logic.Syntax

/-!
# 03-deduction — Solution  (verified answer key)

`make test` kernel-checks this (each `def` typechecks ⇒ the derivation is a valid proof tree).
`Deriv` graduates into `Principia.NatDed.Basic`. Read to understand *why*, not to copy.
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

-- identity: assume `φ`, conclude `φ`.
def derive_identity (φ : Form) : [] ⊢ (φ ⇒ φ) :=
  .impI (.ax (a := φ) (by simp))

-- destructure the conjunction, reassemble it the other way.
def derive_and_commutativity (φ ψ : Form) : [] ⊢ ((φ ⋏ ψ) ⇒ (ψ ⋏ φ)) :=
  .impI (.andI (.andE₂ (.ax (a := φ ⋏ ψ) (by simp)))
               (.andE₁ (.ax (a := φ ⋏ ψ) (by simp))))

-- assume `φ`, then `φ ⇒ ψ`, then apply (impE). The middle formula `φ` must be named.
def derive_modus_ponens (φ ψ : Form) : [] ⊢ (φ ⇒ (φ ⇒ ψ) ⇒ ψ) :=
  .impI (.impI (.impE (a := φ) (.ax (a := φ ⇒ ψ) (by simp)) (.ax (a := φ) (by simp))))

-- Peirce: classical. Assume `(φ⇒ψ)⇒φ`; by `raa` assume `∼φ` and derive `⊥`. To get `φ`, feed
-- `(φ⇒ψ)⇒φ` a proof of `φ⇒ψ` (built vacuously from `∼φ` and ex falso); then `∼φ` applied to `φ` is `⊥`.
def derive_peirce (a b : Form) : [] ⊢ (((a ⇒ b) ⇒ a) ⇒ a) := by
  apply Deriv.impI
  apply Deriv.raa
  have buildImplication : [∼a, (a ⇒ b) ⇒ a] ⊢ (a ⇒ b) := by
    apply Deriv.impI
    apply Deriv.flsE
    apply Deriv.impE (a := a)
    · exact Deriv.ax (a := ∼a) (by simp)
    · exact Deriv.ax (a := a) (by simp)
  have deriveA : [∼a, (a ⇒ b) ⇒ a] ⊢ a :=
    Deriv.impE (Deriv.ax (a := (a ⇒ b) ⇒ a) (by simp))
      buildImplication
  exact Deriv.impE (Deriv.ax (a := ∼a) (by simp)) deriveA

/-! ## Checks (the kernel verifies each derivation just by type-checking it) -/

#check (derive_identity : (φ : Form) → [] ⊢ (φ ⇒ φ))
#check (derive_peirce : (φ ψ : Form) → [] ⊢ (((φ ⇒ ψ) ⇒ φ) ⇒ φ))
#print axioms derive_modus_ponens
#print axioms derive_peirce

end Principia
