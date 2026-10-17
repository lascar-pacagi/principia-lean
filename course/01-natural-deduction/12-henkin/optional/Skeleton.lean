/- Exercises: see the explainer for statements and hints. Optional status is separate. -/
import Principia.FirstOrder

set_option warningAsError true
open Principia.FirstOrder
namespace Course1.HenkinExtensions

theorem no_both_in_theory (Γ : List Formula) (hΓ : Henkin.Consistent Γ) (a : Formula) :
    ¬(Henkin.Theory Γ a ∧ Henkin.Theory Γ a.negation) := by
  sorry

theorem witnessed_second_part (Γ : List Formula) (hΓ : Henkin.Consistent Γ)
    (a b : Formula) (h : Henkin.Theory Γ (.existential (.conjunction a b))) :
    ∃ t, Henkin.Theory Γ (b.instantiate t) := by
  sorry


end Course1.HenkinExtensions
