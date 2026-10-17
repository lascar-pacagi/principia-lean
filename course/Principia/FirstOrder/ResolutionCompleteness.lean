import Principia.FirstOrder.PropositionalCompactness
import Principia.FirstOrder.Enumeration

/-! Refutation completeness for arbitrary finite first-order clause sets, including function
symbols. All substitution instances are treated propositionally; a canonical term model gives the
contrapositive. The proof uses the explicit structural rules of ResolutionDerivation. -/
namespace Principia.FirstOrder


/-- Every substitution instance of an input clause is an available propositional source. -/
def InstanceSource (S : ClauseSet) (c : Clause) : Prop :=
  ∃ original ∈ S, ∃ σ : Nat → Term, c = Clause.substitute σ original

theorem resolution_of_propositional {S : ClauseSet} {c : Clause}
    (d : Propositional.Proof (InstanceSource S) c) : Nonempty (ResolutionDerivation S c) := by
  induction d with
  | input h =>
    obtain ⟨original, hm, σ, he⟩ := h
    subst he
    exact ⟨.substitution σ (.input hm)⟩
  | tautology l => exact ⟨.tautology l⟩
  | weakening d hd ih => obtain ⟨d'⟩ := ih; exact ⟨.weakening d' hd⟩
  | resolve l d e ihd ihe =>
    obtain ⟨d'⟩ := ihd
    obtain ⟨e'⟩ := ihe
    exact ⟨.resolution l d' e'⟩

/-- The canonical domain contains finite terms; its variable leaves act as additional objects. -/
noncomputable def canonicalModel (S : ClauseSet) : Model Term :=
  ⟨Term.function, fun p args => Propositional.valuation Enumeration.atoms (InstanceSource S) ⟨p, args⟩⟩

theorem evaluate_canonical_term (S : ClauseSet) (ρ : Nat → Term) (t : Term) :
    Term.evaluate (canonicalModel S) ρ t = t.substitute ρ := by
  cases t with
  | «variable» i => simp [Term.evaluate, Term.substitute]
  | function f args =>
    simp only [Term.evaluate, canonicalModel, Term.substitute]
    congr 1
    apply List.map_congr_left
    intro a ha
    exact evaluate_canonical_term S ρ a
termination_by sizeOf t
decreasing_by
  have hs := List.sizeOf_lt_of_mem ha
  simp only [Term.function.sizeOf_spec]
  omega

theorem evaluate_canonical_literal (S : ClauseSet) (ρ : Nat → Term) (l : Literal) :
    l.evaluate (canonicalModel S) ρ ↔
      Propositional.Holds (Propositional.valuation Enumeration.atoms (InstanceSource S))
        (l.substitute ρ) := by
  have ht : Term.evaluate (canonicalModel S) ρ = Term.substitute ρ := by
    funext t
    exact evaluate_canonical_term S ρ t
  simp only [Literal.evaluate, Atom.evaluate, Propositional.Holds,
    Literal.substitute, Atom.substitute, ht]
  rfl

theorem model_of_no_refutation {S : ClauseSet}
    (h : ¬Nonempty (ResolutionDerivation S [])) : SatisfiesClauses (canonicalModel S) S := by
  have consistent : Propositional.Consistent (InstanceSource S) := by
    intro ⟨d⟩
    exact h (resolution_of_propositional d)
  intro c hc ρ
  obtain ⟨l, hl, ht⟩ := Propositional.model_of_consistent consistent
    Enumeration.atoms Enumeration.covers_atom (Clause.substitute ρ c) ⟨c, hc, ρ, rfl⟩
  obtain ⟨k, hk, he⟩ := List.mem_map.mp hl
  subst l
  exact ⟨k, hk, (evaluate_canonical_literal S ρ k).mpr ht⟩

/-- General first-order refutation completeness; not restricted to a finite term universe. -/
theorem resolution_complete {S : ClauseSet} (h : Unsatisfiable S) :
    Nonempty (ResolutionDerivation S []) := by
  apply Classical.byContradiction
  intro hn
  exact h Term ⟨.variable 0⟩ (canonicalModel S) (model_of_no_refutation hn)

theorem resolution_iff_unsatisfiable (S : ClauseSet) :
    Nonempty (ResolutionDerivation S []) ↔ Unsatisfiable S :=
  ⟨fun ⟨d⟩ => refutation_unsatisfiable d, resolution_complete⟩

end Principia.FirstOrder
