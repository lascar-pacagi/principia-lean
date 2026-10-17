import Principia.FirstOrder

/-! See the explainer for worked steps and exercise corrections. -/
set_option warningAsError true
open Principia.FirstOrder
namespace Course2.FirstOrderResolution

/-! GIVEN supporting definitions. -/
def positive (p : Nat) (t : Term) : Literal := ⟨true, ⟨p, [t]⟩⟩

def negative (p : Nat) (t : Term) : Literal := ⟨false, ⟨p, [t]⟩⟩

def resolve_universal_unit (p : Nat) (t : Term) :
    ResolutionDerivation [[positive p (.variable 0)], [negative p t]] [] := by
  have first : ResolutionDerivation [[positive p (.variable 0)], [negative p t]]
      [positive p (.variable 0)] := .input (by simp)
  have instanceProof := ResolutionDerivation.substitution (extend t Term.variable) first
  have he : Clause.substitute (extend t Term.variable) [positive p (.variable 0)] =
      [positive p t] := by
    simp [Clause.substitute, Literal.substitute, Atom.substitute, positive,
      Term.substitute, extend]
  have instantiated : ResolutionDerivation [[positive p (.variable 0)], [negative p t]]
      [positive p t] := he ▸ instanceProof
  have second : ResolutionDerivation [[positive p (.variable 0)], [negative p t]]
      [negative p t] := .input (by simp)
  simpa [resolvent, positive, negative, Literal.complement] using
    (ResolutionDerivation.resolution (positive p t) instantiated second)

theorem resolution_stage_sound {S : ClauseSet} {stage : Nat}
    (h : (resolutionStage stage S).isSome = true) : Unsatisfiable S := by
  exact refuteFirstOrder_sound h

theorem empty_clause_has_no_model {D : Type} (M : Model D) (ρ : Nat → D) :
    ¬Clause.evaluate M ρ [] := by
  intro ⟨l, hl, ht⟩
  cases hl

/-! ## Checks — dependencies of the completed proofs. -/
#print axioms resolve_universal_unit
#print axioms resolution_stage_sound
#print axioms empty_clause_has_no_model

end Course2.FirstOrderResolution
