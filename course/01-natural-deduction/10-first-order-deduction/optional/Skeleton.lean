import Principia.FirstOrder

/-! See the explainer for worked steps and exercise corrections. -/
set_option warningAsError true
open Principia.FirstOrder
namespace Course1.FirstOrderDeduction

/-! GIVEN supporting definitions. -/
def unary (p : Nat) (t : Term) : Formula := .predicate p [t]

def quantified_double_negation (body : Formula) :
    Derivation [] (.implies (Formula.universal body).negation.negation (.universal body)) := by
  sorry

theorem universal_instance_semantics (body : Formula) (t : Term) :
    Formula.Entails [.universal body] (body.instantiate t) := by
  sorry

end Course1.FirstOrderDeduction
