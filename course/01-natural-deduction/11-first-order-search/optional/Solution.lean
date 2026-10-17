import Principia.FirstOrder

/-! See the explainer for worked steps and exercise corrections. -/
set_option warningAsError true
open Principia.FirstOrder
namespace Course1.FirstOrderSearch

/-! GIVEN supporting definitions. -/
def unary (p : Nat) (t : Term) : Formula := .predicate p [t]

theorem countermodel_prevents_success {D : Type} (inhabited : Nonempty D)
    (M : Model D) (ρ : Nat → D) (Γ : List Formula) (goal : Formula) (fuel : Nat)
    (hΓ : Satisfies M ρ Γ) (hnot : ¬goal.evaluate M ρ) :
    (proveFirstOrder fuel Γ goal).isSome = false := by
  cases hs : (proveFirstOrder fuel Γ goal).isSome with
  | false => rfl
  | true =>
    have he := proveFirstOrder_sound hs D inhabited M ρ hΓ
    exact False.elim (hnot he)

theorem zero_fuel_misses_quantified_identity (p : Nat) :
    (proveFirstOrder 0 [] (.universal (.implies (unary p (.variable 0))
      (unary p (.variable 0))))).isSome = false ∧
    Nonempty (Derivation [] (.universal (.implies (unary p (.variable 0))
      (unary p (.variable 0))))) := by
  constructor
  · rfl
  · exact ⟨.universalIntro (.implicationIntro (.assumption (by simp)))⟩

/-! ## Checks — dependencies of the completed proofs. -/
#print axioms countermodel_prevents_success
#print axioms zero_fuel_misses_quantified_identity

end Course1.FirstOrderSearch
