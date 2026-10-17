import Principia.NatDed.Completeness

/-! Optional exercises; see the lesson for hints and corrections. -/
set_option warningAsError true
open Principia Principia.Form
open scoped Principia.Form Principia
namespace Course1.Completeness

def derive_right_projection : [] ⊢ ((Form.var 0 ⋏ Form.var 1) ⇒ Form.var 1) := by
  sorry

theorem no_derivation_from_counterexample (a : Form) (v : Nat → Bool)
    (h : eval v a = false) : ¬Nonempty ([] ⊢ a) := by
  sorry


end Course1.Completeness
