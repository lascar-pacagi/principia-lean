/- Exercises: see the explainer for statements and hints. Optional status is separate. -/
import Principia.FirstOrder

set_option warningAsError true
open Principia.FirstOrder
namespace Course1.GeneralCompleteness

theorem closed_proof_iff_valid (a : Formula) :
    Nonempty (Derivation [] a) ↔ Formula.Valid a := by
  sorry

theorem provability_transfers (Γ Δ : List Formula) (a : Formula)
    (available : ∀ b ∈ Γ, Formula.Entails Δ b) (proof : Nonempty (Derivation Γ a)) :
    Nonempty (Derivation Δ a) := by
  sorry


end Course1.GeneralCompleteness
