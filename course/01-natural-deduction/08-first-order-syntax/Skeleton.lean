import Principia.FirstOrder

/-! See the explainer for worked steps and exercise corrections. -/
set_option warningAsError true
open Principia.FirstOrder
namespace Course1.FirstOrderSyntax

theorem substitute_variable (σ : Nat → Term) (i : Nat) :
    Term.substitute σ (.variable i) = σ i := by
  sorry

theorem instantiate_unary (p : Nat) (t : Term) :
    (Formula.predicate p [.variable 0]).instantiate t = .predicate p [t] := by
  sorry

end Course1.FirstOrderSyntax
