import Principia.FirstOrder

set_option warningAsError true
open Principia.FirstOrder
namespace Course2.ResolutionCompleteness

theorem incompatible_units_inconsistent (T : Clause → Prop) (l : Literal)
    (positive : T [l]) (negative : T [l.complement]) : ¬Propositional.Consistent T := by
  intro consistent
  apply consistent
  exact ⟨by simpa [resolvent] using
    Propositional.Proof.resolve l (.input positive) (.input negative)⟩

theorem semantic_refutability_invariant (s t : ClauseSet)
    (sameModels : ∀ (D : Type) (_ : Nonempty D) (M : Model D),
      SatisfiesClauses M s ↔ SatisfiesClauses M t) :
    Nonempty (ResolutionDerivation s []) ↔ Nonempty (ResolutionDerivation t []) := by
  rw [resolution_iff_unsatisfiable, resolution_iff_unsatisfiable]
  constructor
  · intro hs D inhabited M ht
    exact hs D inhabited M ((sameModels D inhabited M).mpr ht)
  · intro ht D inhabited M hs
    exact ht D inhabited M ((sameModels D inhabited M).mp hs)

#print axioms incompatible_units_inconsistent
#print axioms semantic_refutability_invariant

end Course2.ResolutionCompleteness
