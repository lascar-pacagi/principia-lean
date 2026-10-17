import Principia.FirstOrder

set_option warningAsError true
open Principia.FirstOrder
namespace Course1.GeneralCompleteness

theorem closed_proof_iff_valid (a : Formula) :
    Nonempty (Derivation [] a) ↔ Formula.Valid a := deduction_iff_entails [] a

theorem provability_transfers (Γ Δ : List Formula) (a : Formula)
    (available : ∀ b ∈ Γ, Formula.Entails Δ b) (proof : Nonempty (Derivation Γ a)) :
    Nonempty (Derivation Δ a) := by
  apply deduction_complete
  intro D inhabited M ρ hΔ
  exact (deduction_iff_entails Γ a).mp proof D inhabited M ρ
    (fun b hb => available b hb D inhabited M ρ hΔ)

#print axioms closed_proof_iff_valid
#print axioms provability_transfers

end Course1.GeneralCompleteness
