import Principia.FirstOrder

/-! See the explainer for worked steps and exercise corrections. -/
set_option warningAsError true
open Principia.FirstOrder
namespace Course1.FirstOrderDeduction

/-! GIVEN supporting definitions. -/
def unary (p : Nat) (t : Term) : Formula := .predicate p [t]

def universal_to_existential (p : Nat) (t : Term) :
    Derivation [.universal (unary p (.variable 0))]
      (.existential (unary p (.variable 0))) := by
  apply Derivation.existentialIntro t
  exact Derivation.universalElim t (.assumption (by simp))

def universal_identity (p : Nat) :
    Derivation [] (.universal
      (.implies (unary p (.variable 0)) (unary p (.variable 0)))) := by
  apply Derivation.universalIntro
  apply Derivation.implicationIntro
  exact Derivation.assumption (by simp)

def existential_conjunction_left (p q : Nat) :
    Derivation [.existential (.conjunction (unary p (.variable 0)) (unary q (.variable 0)))]
      (.existential (unary p (.variable 0))) := by
  apply Derivation.existentialElim
    (body := .conjunction (unary p (.variable 0)) (unary q (.variable 0)))
  · exact Derivation.assumption (by simp)
  · have he : (Formula.existential (unary p (.variable 0))).shift =
        .existential (unary p (.variable 0)) := by
      simp [unary, Formula.shift, Formula.rename, Formula.substitute,
        liftSubstitution, Term.substitute]
    rw [he]
    apply Derivation.existentialIntro (.variable 0)
    have whole : Derivation
        (.conjunction (unary p (.variable 0)) (unary q (.variable 0)) ::
          [Formula.existential (.conjunction (unary p (.variable 0))
            (unary q (.variable 0)))].map Formula.shift)
        (.conjunction (unary p (.variable 0)) (unary q (.variable 0))) :=
      .assumption (by simp)
    have part := Derivation.conjunctionLeft whole
    simpa [unary, Formula.instantiate, Formula.substitute, Term.substitute, extend]
      using part

/-! ## Checks — dependencies of the completed proofs. -/
#print axioms universal_to_existential
#print axioms universal_identity
#print axioms existential_conjunction_left

end Course1.FirstOrderDeduction
