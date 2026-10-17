import Principia.FirstOrder

/-! See the explainer for worked steps and exercise corrections. -/
set_option warningAsError true
open Principia.FirstOrder
namespace Course2.Unification

def certifyCandidate (σ : Substitution) (equations : List (Term × Term)) :
    Option (CheckedUnifier equations) :=
  if h : equations.all (fun pair => decide (σ.apply pair.1 = σ.apply pair.2)) = true then
    some ⟨σ, by
      intro pair hp
      exact of_decide_eq_true (List.all_eq_true.mp h pair hp)⟩
  else none

theorem accepted_candidate_solves (σ : Substitution) (equations : List (Term × Term))
    (h : (certifyCandidate σ equations).isSome = true) :
    ∀ pair ∈ equations, σ.apply pair.1 = σ.apply pair.2 := by
  intro pair hp
  by_cases hc : equations.all (fun p => decide (σ.apply p.1 = σ.apply p.2)) = true
  · exact of_decide_eq_true (List.all_eq_true.mp hc pair hp)
  · simp [certifyCandidate, hc] at h

/-! ## Checks — dependencies of the completed proofs. -/
#print axioms certifyCandidate
#print axioms accepted_candidate_solves

end Course2.Unification
