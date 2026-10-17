/- Exercises: see the explainer for statements and hints. Optional status is separate. -/
import Principia.FirstOrder

set_option warningAsError true
open Principia.FirstOrder
namespace Course1.HenkinExtensions

theorem consistent_subcontext (Γ Δ : List Formula) (h : Henkin.Consistent Δ)
    (included : ∀ a ∈ Γ, a ∈ Δ) : Henkin.Consistent Γ := by
  sorry

theorem theory_pair_reverse (Γ : List Formula) (a b : Formula)
    (ha : Henkin.Theory Γ a) (hb : Henkin.Theory Γ b) :
    Henkin.Theory Γ (.conjunction b a) := by
  sorry


end Course1.HenkinExtensions
