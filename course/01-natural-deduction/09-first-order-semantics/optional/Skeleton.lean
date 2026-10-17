import Principia.FirstOrder

/-! See the explainer for worked steps and exercise corrections. -/
set_option warningAsError true
open Principia.FirstOrder
namespace Course1.FirstOrderSemantics

/-! GIVEN supporting definitions. -/
def trueAtTrueModel : Model Bool :=
  ⟨fun _ _ => false, fun _ args => args = [true]⟩

theorem not_every_value_satisfies :
    ¬(Formula.universal (.predicate 0 [.variable 0])).evaluate trueAtTrueModel
      (fun _ => false) := by
  sorry

theorem some_value_satisfies :
    (Formula.existential (.predicate 0 [.variable 0])).evaluate trueAtTrueModel
      (fun _ => false) := by
  sorry

end Course1.FirstOrderSemantics
