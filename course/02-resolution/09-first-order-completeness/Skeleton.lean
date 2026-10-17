/- Exercises: see the explainer for statements and hints. Optional status is separate. -/
import Principia.FirstOrder

set_option warningAsError true
open Principia.FirstOrder
namespace Course2.ResolutionCompleteness

theorem refutation_of_unsatisfiable_subsystem (s t : ClauseSet)
    (included : ∀ c ∈ s, c ∈ t) (h : Unsatisfiable s) :
    Nonempty (ResolutionDerivation t []) := by
  sorry

theorem consistent_source_has_term_model (s : ClauseSet)
    (h : ¬Nonempty (ResolutionDerivation s [])) :
    ∃ M : Model Term, SatisfiesClauses M s := by
  sorry


end Course2.ResolutionCompleteness
