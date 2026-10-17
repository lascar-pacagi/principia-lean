import Principia.FirstOrder

/-! See the explainer for worked steps and exercise corrections. -/
set_option warningAsError true
open Principia.FirstOrder
namespace Course1.FirstOrderSyntax

theorem capture_avoiding_example :
    (Formula.universal (.universal
      (.predicate 2 [.variable 2, .variable 0]))).substitute
      (fun _ => .variable 3) = .universal (.universal
        (.predicate 2 [.variable 5, .variable 0])) := by
  simp [Formula.substitute, liftSubstitution, Term.rename, Term.substitute]

theorem instantiate_unused (p : Nat) (t : Term) :
    (Formula.predicate p [.variable 1]).instantiate t = .predicate p [.variable 0] := by
  simp [Formula.instantiate, Formula.substitute, Term.substitute, extend]

/-! ## Checks — dependencies of the completed proofs. -/
#print axioms capture_avoiding_example
#print axioms instantiate_unused

end Course1.FirstOrderSyntax
