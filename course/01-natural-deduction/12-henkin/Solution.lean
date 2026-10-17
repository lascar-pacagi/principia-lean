import Principia.FirstOrder

set_option warningAsError true
open Principia.FirstOrder
namespace Course1.HenkinExtensions

theorem consistent_subcontext (Γ Δ : List Formula) (h : Henkin.Consistent Δ)
    (included : ∀ a ∈ Γ, a ∈ Δ) : Henkin.Consistent Γ := by
  intro proofOfFalse
  exact h (Henkin.weaken included proofOfFalse)

theorem theory_pair_reverse (Γ : List Formula) (a b : Formula)
    (ha : Henkin.Theory Γ a) (hb : Henkin.Theory Γ b) :
    Henkin.Theory Γ (.conjunction b a) := by
  obtain ⟨n, ⟨proofA⟩, ⟨proofB⟩⟩ := Henkin.common ha hb
  exact ⟨n, ⟨.conjunctionIntro proofB proofA⟩⟩

#print axioms consistent_subcontext
#print axioms theory_pair_reverse

end Course1.HenkinExtensions
