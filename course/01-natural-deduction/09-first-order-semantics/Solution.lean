import Principia.FirstOrder

/-! See the explainer for worked steps and exercise corrections. -/
set_option warningAsError true
open Principia.FirstOrder
namespace Course1.FirstOrderSemantics

/-! GIVEN supporting definitions. -/
def trueAtTrueModel : Model Bool :=
  ⟨fun _ _ => false, fun _ args => args = [true]⟩

theorem semantic_specialization {D : Type} (M : Model D) (ρ : Nat → D)
    (body : Formula) (t : Term) (h : (Formula.universal body).evaluate M ρ) :
    (body.instantiate t).evaluate M ρ := by
  apply (Formula.evaluate_instantiate M ρ body t).mpr
  exact h (Term.evaluate M ρ t)

theorem semantic_witness {D : Type} (M : Model D) (ρ : Nat → D)
    (body : Formula) (t : Term) (h : (body.instantiate t).evaluate M ρ) :
    (Formula.existential body).evaluate M ρ := by
  exact ⟨Term.evaluate M ρ t, (Formula.evaluate_instantiate M ρ body t).mp h⟩

/-! ## Checks — dependencies of the completed proofs. -/
#print axioms semantic_specialization
#print axioms semantic_witness

end Course1.FirstOrderSemantics
