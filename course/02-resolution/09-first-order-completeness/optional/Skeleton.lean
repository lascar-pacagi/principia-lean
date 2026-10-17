/- Exercises: see the explainer for statements and hints. Optional status is separate. -/
import Principia.FirstOrder

set_option warningAsError true
open Principia.FirstOrder
namespace Course2.ResolutionCompleteness

theorem incompatible_units_inconsistent (T : Clause → Prop) (l : Literal)
    (positive : T [l]) (negative : T [l.complement]) : ¬Propositional.Consistent T := by
  sorry

theorem semantic_refutability_invariant (s t : ClauseSet)
    (sameModels : ∀ (D : Type) (_ : Nonempty D) (M : Model D),
      SatisfiesClauses M s ↔ SatisfiesClauses M t) :
    Nonempty (ResolutionDerivation s []) ↔ Nonempty (ResolutionDerivation t []) := by
  sorry


end Course2.ResolutionCompleteness
