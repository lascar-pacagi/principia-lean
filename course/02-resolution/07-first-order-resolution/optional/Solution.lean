import Principia.FirstOrder

/-! See the explainer for worked steps and exercise corrections. -/
set_option warningAsError true
open Principia.FirstOrder
namespace Course2.FirstOrderResolution

/-! GIVEN supporting definitions. -/
def positive (p : Nat) (t : Term) : Literal := ⟨true, ⟨p, [t]⟩⟩

def negative (p : Nat) (t : Term) : Literal := ⟨false, ⟨p, [t]⟩⟩

def factor_two_variables (p : Nat) :
    ResolutionDerivation [[positive p (.function 2 [.variable 0]),
        positive p (.function 2 [.variable 1])]]
      [positive p (.function 2 [.variable 1])] := by
  have initial : ResolutionDerivation [[positive p (.function 2 [.variable 0]),
        positive p (.function 2 [.variable 1])]]
      [positive p (.function 2 [.variable 0]),
        positive p (.function 2 [.variable 1])] := .input (by simp)
  let σ := fun i => if i = 0 then Term.variable 1 else Term.variable i
  have instanceProof := ResolutionDerivation.substitution σ initial
  have he : Clause.substitute σ [positive p (.function 2 [.variable 0]),
        positive p (.function 2 [.variable 1])] =
      [positive p (.function 2 [.variable 1]), positive p (.function 2 [.variable 1])] := by
    simp [Clause.substitute, Literal.substitute, Atom.substitute, positive, σ, Term.substitute]
  have doubled := he ▸ instanceProof
  simpa [List.eraseDups_cons] using ResolutionDerivation.contraction doubled

theorem freshening_renames_variable (p : Nat) :
    (freshenEntry 1 (S := [[positive p (.variable 0)]])
      ⟨[positive p (.variable 0)], .input (by simp)⟩).1 = [positive p (.variable 1)] := by
  simp [freshenEntry, Clause.substitute, Literal.substitute, Atom.substitute,
    positive, Term.substitute]

/-! ## Checks — dependencies of the completed proofs. -/
#print axioms factor_two_variables
#print axioms freshening_renames_variable

end Course2.FirstOrderResolution
