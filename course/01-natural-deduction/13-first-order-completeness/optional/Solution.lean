import Principia.FirstOrder

set_option warningAsError true
open Principia.FirstOrder
namespace Course1.GeneralCompleteness

theorem not_valid_iff_no_closed_proof (a : Formula) :
    ¬Formula.Valid a ↔ ¬Nonempty (Derivation [] a) :=
  not_congr (deduction_iff_entails [] a).symm

theorem quantified_left_projection (p q : Nat) :
    Nonempty (Derivation [] (.implies
      (.universal (.conjunction (.predicate p [.variable 0]) (.predicate q [.variable 0])))
      (.universal (.predicate p [.variable 0])))) := by
  apply deduction_complete
  intro D inhabited M ρ assumptions h x
  exact (h x).1

#print axioms not_valid_iff_no_closed_proof
#print axioms quantified_left_projection

end Course1.GeneralCompleteness
