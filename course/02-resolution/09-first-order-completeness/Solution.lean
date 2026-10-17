import Principia.FirstOrder

set_option warningAsError true
open Principia.FirstOrder
namespace Course2.ResolutionCompleteness

theorem refutation_of_unsatisfiable_subsystem (s t : ClauseSet)
    (included : ∀ c ∈ s, c ∈ t) (h : Unsatisfiable s) :
    Nonempty (ResolutionDerivation t []) := by
  apply resolution_complete
  intro D inhabited M ht
  exact h D inhabited M (fun c hc => ht c (included c hc))

theorem consistent_source_has_term_model (s : ClauseSet)
    (h : ¬Nonempty (ResolutionDerivation s [])) :
    ∃ M : Model Term, SatisfiesClauses M s :=
  ⟨canonicalModel s, model_of_no_refutation h⟩

#print axioms refutation_of_unsatisfiable_subsystem
#print axioms consistent_source_has_term_model

end Course2.ResolutionCompleteness
