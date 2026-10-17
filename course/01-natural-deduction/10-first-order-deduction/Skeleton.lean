import Principia.FirstOrder

/-! See the explainer for worked steps and exercise corrections. -/
set_option warningAsError true
open Principia.FirstOrder
namespace Course1.FirstOrderDeduction

/-! GIVEN supporting definitions. -/
def unary (p : Nat) (t : Term) : Formula := .predicate p [t]

def universal_to_existential (p : Nat) (t : Term) :
    Derivation [.universal (unary p (.variable 0))]
      (.existential (unary p (.variable 0))) := by
  sorry

def universal_identity (p : Nat) :
    Derivation [] (.universal
      (.implies (unary p (.variable 0)) (unary p (.variable 0)))) := by
  sorry

def existential_conjunction_left (p q : Nat) :
    Derivation [.existential (.conjunction (unary p (.variable 0)) (unary q (.variable 0)))]
      (.existential (unary p (.variable 0))) := by
  sorry

end Course1.FirstOrderDeduction
