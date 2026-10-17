import Principia.FirstOrder

set_option warningAsError true
open Principia.FirstOrder
namespace Course2.Clausification

theorem matrix_disjunction_clauses {D : Type} (M : Model D) (ρ : Nat → D) (a b : Matrix) :
    ClausesAt M ρ (Matrix.disjunction a b).toClauses ↔ a.evaluate M ρ ∨ b.evaluate M ρ :=
  matrix_toClauses_correct M ρ (.disjunction a b)

theorem clausal_proof_valid (goal : Formula) (proof : ClausalProof [] goal) :
    Formula.Valid goal := proof.sound

#print axioms matrix_disjunction_clauses
#print axioms clausal_proof_valid

end Course2.Clausification
