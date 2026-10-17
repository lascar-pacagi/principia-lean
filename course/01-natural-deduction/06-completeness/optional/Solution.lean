import Principia.NatDed.Completeness

/-! Optional exercises; see the lesson for hints and corrections. -/
set_option warningAsError true
open Principia Principia.Form
open scoped Principia.Form Principia
namespace Course1.Completeness

def derive_right_projection : [] ⊢ ((Form.var 0 ⋏ Form.var 1) ⇒ Form.var 1) := by
  apply completeness
  intro v
  simp only [eval]
  cases v 0 <;> cases v 1 <;> rfl

theorem no_derivation_from_counterexample (a : Form) (v : Nat → Bool)
    (h : eval v a = false) : ¬Nonempty ([] ⊢ a) := by
  intro ⟨d⟩
  have ht := tautology_of_proof d v
  rw [h] at ht
  contradiction

#print axioms derive_right_projection
#print axioms no_derivation_from_counterexample

end Course1.Completeness
