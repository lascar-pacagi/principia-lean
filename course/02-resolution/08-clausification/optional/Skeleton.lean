/- Exercises: see the explainer for statements and hints. Optional status is separate. -/
import Principia.FirstOrder

set_option warningAsError true
open Principia.FirstOrder
namespace Course2.Clausification

theorem negative_universal {D : Type} (M : Model D) (ρ : Nat → D) (body : Formula) :
    ((Formula.universal body).toNnf false).evaluate M ρ ↔
      ∃ x, ¬body.evaluate M (extend x ρ) := by
  sorry

theorem two_universal_dependencies :
    (clausify (.universal (.universal (.existential
      (.predicate 0 [.variable 2, .variable 0, .variable 1]))))).skolemSymbols =
      [⟨0, [0, 1]⟩] := by
  sorry


end Course2.Clausification
