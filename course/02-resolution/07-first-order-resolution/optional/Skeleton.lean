import Principia.FirstOrder

/-! See the explainer for worked steps and exercise corrections. -/
set_option warningAsError true
open Principia.FirstOrder
namespace Course2.FirstOrderResolution

/-! GIVEN supporting definitions. -/
def positive (p : Nat) (t : Term) : Literal := ⟨true, ⟨p, [t]⟩⟩

def negative (p : Nat) (t : Term) : Literal := ⟨false, ⟨p, [t]⟩⟩

def factor_two_variables (p : Nat) :
    ResolutionDerivation [[positive p (.function 2 [.variable 0]),
        positive p (.function 2 [.variable 1])]]
      [positive p (.function 2 [.variable 1])] := by
  sorry

theorem freshening_renames_variable (p : Nat) :
    (freshenEntry 1 (S := [[positive p (.variable 0)]])
      ⟨[positive p (.variable 0)], .input (by simp)⟩).1 = [positive p (.variable 1)] := by
  sorry

end Course2.FirstOrderResolution
