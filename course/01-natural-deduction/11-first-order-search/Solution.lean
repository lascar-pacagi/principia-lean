import Principia.FirstOrder

/-! See the explainer for worked steps and exercise corrections. -/
set_option warningAsError true
open Principia.FirstOrder
namespace Course1.FirstOrderSearch

/-! GIVEN supporting definitions. -/
def unary (p : Nat) (t : Term) : Formula := .predicate p [t]

def closedSearch (fuel : Nat) (formulas : List Formula) (terms : List Term)
    (goal : Formula) : Option (Derivation [] goal) :=
  searchDerivation formulas terms fuel [] goal

theorem closedSearch_sound {fuel : Nat} {formulas : List Formula} {terms : List Term}
    {goal : Formula} (h : (closedSearch fuel formulas terms goal).isSome = true) :
    Formula.Valid goal := by
  exact searchDerivation_sound h

theorem stage_success_provides_derivation {stage : Nat} {Γ : List Formula} {goal : Formula}
    (h : (derivationStage stage Γ goal).isSome = true) : Nonempty (Derivation Γ goal) := by
  cases hs : derivationStage stage Γ goal with
  | none => simp [hs] at h
  | some d => exact ⟨d⟩

/-! ## Checks — dependencies of the completed proofs. -/
#print axioms closedSearch
#print axioms closedSearch_sound
#print axioms stage_success_provides_derivation

end Course1.FirstOrderSearch
