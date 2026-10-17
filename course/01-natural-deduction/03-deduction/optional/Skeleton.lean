import Principia.NatDed.Basic

/-! Optional exercises; see the lesson for hints and corrections. -/
set_option warningAsError true
open Principia Principia.Form
open scoped Principia.Form Principia
namespace Course1.Deduction

def derive_or_commutativity (a b : Form) : [] ⊢ ((a ⋎ b) ⇒ (b ⋎ a)) := by
  sorry

def derive_excluded_middle (a : Form) : [] ⊢ (a ⋎ ∼a) := by
  sorry


end Course1.Deduction
