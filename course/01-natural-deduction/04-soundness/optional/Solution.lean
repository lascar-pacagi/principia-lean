import Principia.NatDed.Soundness

/-! Optional exercises; see the lesson for hints and corrections. -/
set_option warningAsError true
open Principia Principia.Form
open scoped Principia.Form Principia
namespace Course1.Soundness

theorem consistency : ([] ⊢ Form.falsum) → False := by
  intro d
  have h := tautology_of_proof d (fun _ => false)
  simp [eval] at h

theorem not_provable_var : ([] ⊢ Form.var 0) → False := by
  intro d
  have h := tautology_of_proof d (fun _ => false)
  simp [eval] at h

#print axioms consistency
#print axioms not_provable_var

end Course1.Soundness
