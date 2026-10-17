import Principia.NatDed.Soundness

/-! Optional exercises; see the lesson for hints and corrections. -/
set_option warningAsError true
open Principia Principia.Form
open scoped Principia.Form Principia
namespace Course1.Soundness

theorem consistency : ([] ⊢ Form.falsum) → False := by
  sorry

theorem not_provable_var : ([] ⊢ Form.var 0) → False := by
  sorry


end Course1.Soundness
