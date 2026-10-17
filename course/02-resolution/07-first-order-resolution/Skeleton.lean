import Principia.FirstOrder

/-! See the explainer for worked steps and exercise corrections. -/
set_option warningAsError true
open Principia.FirstOrder
namespace Course2.FirstOrderResolution

/-! GIVEN supporting definitions. -/
def positive (p : Nat) (t : Term) : Literal := ⟨true, ⟨p, [t]⟩⟩

def negative (p : Nat) (t : Term) : Literal := ⟨false, ⟨p, [t]⟩⟩

def resolve_universal_unit (p : Nat) (t : Term) :
    ResolutionDerivation [[positive p (.variable 0)], [negative p t]] [] := by
  sorry

theorem resolution_stage_sound {S : ClauseSet} {stage : Nat}
    (h : (resolutionStage stage S).isSome = true) : Unsatisfiable S := by
  sorry

theorem empty_clause_has_no_model {D : Type} (M : Model D) (ρ : Nat → D) :
    ¬Clause.evaluate M ρ [] := by
  sorry

end Course2.FirstOrderResolution
