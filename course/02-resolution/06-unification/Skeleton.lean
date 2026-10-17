import Principia.FirstOrder

/-! See the explainer for worked steps and exercise corrections. -/
set_option warningAsError true
open Principia.FirstOrder
namespace Course2.Unification

def certifyCandidate (σ : Substitution) (equations : List (Term × Term)) :
    Option (CheckedUnifier equations) :=
  sorry

theorem accepted_candidate_solves (σ : Substitution) (equations : List (Term × Term))
    (h : (certifyCandidate σ equations).isSome = true) :
    ∀ pair ∈ equations, σ.apply pair.1 = σ.apply pair.2 := by
  sorry

end Course2.Unification
