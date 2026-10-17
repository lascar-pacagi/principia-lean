/- Exercises: see the explainer for statements and hints. Optional status is separate. -/
import Principia.FirstOrder

set_option warningAsError true
open Principia.FirstOrder
namespace Course1.GeneralCompleteness

theorem not_valid_iff_no_closed_proof (a : Formula) :
    ¬Formula.Valid a ↔ ¬Nonempty (Derivation [] a) := by
  sorry

theorem quantified_left_projection (p q : Nat) :
    Nonempty (Derivation [] (.implies
      (.universal (.conjunction (.predicate p [.variable 0]) (.predicate q [.variable 0])))
      (.universal (.predicate p [.variable 0])))) := by
  sorry


end Course1.GeneralCompleteness
