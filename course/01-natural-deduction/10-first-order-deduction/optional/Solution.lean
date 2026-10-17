import Principia.FirstOrder

/-! See the explainer for worked steps and exercise corrections. -/
set_option warningAsError true
open Principia.FirstOrder
namespace Course1.FirstOrderDeduction

/-! GIVEN supporting definitions. -/
def unary (p : Nat) (t : Term) : Formula := .predicate p [t]

def quantified_double_negation (body : Formula) :
    Derivation [] (.implies (Formula.universal body).negation.negation (.universal body)) := by
  apply Derivation.implicationIntro
  apply Derivation.contradiction
  apply Derivation.implicationElim (a := (Formula.universal body).negation)
  · exact Derivation.assumption (a := (Formula.universal body).negation.negation) (by simp)
  · exact Derivation.assumption (a := (Formula.universal body).negation) (by simp)

theorem universal_instance_semantics (body : Formula) (t : Term) :
    Formula.Entails [.universal body] (body.instantiate t) := by
  exact derivation_sound (Derivation.universalElim t (.assumption (by simp)))

/-! ## Checks — dependencies of the completed proofs. -/
#print axioms quantified_double_negation
#print axioms universal_instance_semantics

end Course1.FirstOrderDeduction
