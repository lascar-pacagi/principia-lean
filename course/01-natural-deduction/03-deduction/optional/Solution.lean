import Principia.NatDed.Basic

/-! Optional exercises; see the lesson for hints and corrections. -/
set_option warningAsError true
open Principia Principia.Form
open scoped Principia.Form Principia
namespace Course1.Deduction

def derive_or_commutativity (a b : Form) : [] ⊢ ((a ⋎ b) ⇒ (b ⋎ a)) := by
  apply Deriv.impI
  apply Deriv.orE (a := a) (b := b)
  · exact Deriv.ax (by simp)
  · apply Deriv.orI₂
    exact Deriv.ax (by simp)
  · apply Deriv.orI₁
    exact Deriv.ax (by simp)

def derive_excluded_middle (a : Form) : [] ⊢ (a ⋎ ∼a) := by
  apply Deriv.raa
  have dn : [∼(a ⋎ ∼a)] ⊢ ∼a := by
    apply Deriv.impI
    apply Deriv.impE (a := a ⋎ ∼a)
    · exact Deriv.ax (a := ∼(a ⋎ ∼a)) (by simp)
    · apply Deriv.orI₁
      exact Deriv.ax (by simp)
  exact Deriv.impE (a := a ⋎ ∼a)
    (Deriv.ax (a := ∼(a ⋎ ∼a)) (by simp))
    (Deriv.orI₂ dn)

#print axioms derive_or_commutativity
#print axioms derive_excluded_middle

end Course1.Deduction
