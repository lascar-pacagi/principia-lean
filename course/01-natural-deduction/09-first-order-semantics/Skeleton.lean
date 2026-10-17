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
  sorry

theorem semantic_witness {D : Type} (M : Model D) (ρ : Nat → D)
    (body : Formula) (t : Term) (h : (body.instantiate t).evaluate M ρ) :
    (Formula.existential body).evaluate M ρ := by
  sorry

end Course1.FirstOrderSemantics
