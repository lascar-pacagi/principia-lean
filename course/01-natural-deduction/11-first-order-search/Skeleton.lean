import Principia.FirstOrder

/-! See the explainer for worked steps and exercise corrections. -/
set_option warningAsError true
open Principia.FirstOrder
namespace Course1.FirstOrderSearch

/-! GIVEN supporting definitions. -/
def unary (p : Nat) (t : Term) : Formula := .predicate p [t]

def closedSearch (fuel : Nat) (formulas : List Formula) (terms : List Term)
    (goal : Formula) : Option (Derivation [] goal) :=
  sorry

theorem closedSearch_sound {fuel : Nat} {formulas : List Formula} {terms : List Term}
    {goal : Formula} (h : (closedSearch fuel formulas terms goal).isSome = true) :
    Formula.Valid goal := by
  sorry

theorem stage_success_provides_derivation {stage : Nat} {Γ : List Formula} {goal : Formula}
    (h : (derivationStage stage Γ goal).isSome = true) : Nonempty (Derivation Γ goal) := by
  sorry

end Course1.FirstOrderSearch
