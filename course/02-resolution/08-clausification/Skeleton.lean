/- Exercises: see the explainer for statements and hints. Optional status is separate. -/
import Principia.FirstOrder

set_option warningAsError true
open Principia.FirstOrder
namespace Course2.Clausification

theorem matrix_disjunction_clauses {D : Type} (M : Model D) (ρ : Nat → D) (a b : Matrix) :
    ClausesAt M ρ (Matrix.disjunction a b).toClauses ↔ a.evaluate M ρ ∨ b.evaluate M ρ := by
  sorry

theorem clausal_proof_valid (goal : Formula) (proof : ClausalProof [] goal) :
    Formula.Valid goal := by
  sorry


end Course2.Clausification
