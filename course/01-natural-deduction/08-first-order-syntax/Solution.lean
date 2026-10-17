import Principia.FirstOrder

/-! See the explainer for worked steps and exercise corrections. -/
set_option warningAsError true
open Principia.FirstOrder
namespace Course1.FirstOrderSyntax

theorem substitute_variable (σ : Nat → Term) (i : Nat) :
    Term.substitute σ (.variable i) = σ i := by
  simp [Term.substitute]

theorem instantiate_unary (p : Nat) (t : Term) :
    (Formula.predicate p [.variable 0]).instantiate t = .predicate p [t] := by
  simp [Formula.instantiate, Formula.substitute, Term.substitute, extend]

/-! ## Checks — dependencies of the completed proofs. -/
#print axioms substitute_variable
#print axioms instantiate_unary

end Course1.FirstOrderSyntax
