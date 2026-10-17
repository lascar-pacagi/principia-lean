import Principia.FirstOrder

set_option warningAsError true
open Principia.FirstOrder
namespace Course1.HenkinExtensions

theorem no_both_in_theory (Γ : List Formula) (hΓ : Henkin.Consistent Γ) (a : Formula) :
    ¬(Henkin.Theory Γ a ∧ Henkin.Theory Γ a.negation) := by
  intro ⟨positive, negative⟩
  exact (Henkin.theory_negation hΓ a).mp negative positive

theorem witnessed_second_part (Γ : List Formula) (hΓ : Henkin.Consistent Γ)
    (a b : Formula) (h : Henkin.Theory Γ (.existential (.conjunction a b))) :
    ∃ t, Henkin.Theory Γ (b.instantiate t) := by
  obtain ⟨t, ht⟩ := Henkin.theory_witness hΓ h
  have pair : Henkin.Theory Γ (.conjunction (a.instantiate t) (b.instantiate t)) := ht
  exact ⟨t, (Henkin.theory_conjunction _ _).mp pair |>.2⟩

#print axioms no_both_in_theory
#print axioms witnessed_second_part

end Course1.HenkinExtensions
