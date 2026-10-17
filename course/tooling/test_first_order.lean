import Principia.FirstOrder.NaturalDeductionSearch
import Principia.FirstOrder.ResolutionSearch

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

open Principia.FirstOrder
namespace FirstOrderChecks

def socrates : Term := .function 0 []
def human (t : Term) : Formula := .predicate 0 [t]
def mortal (t : Term) : Formula := .predicate 1 [t]
def mortalityBody : Formula := .implies (human (.variable 0)) (mortal (.variable 0))
def mortalityLaw : Formula := .universal mortalityBody

def socratesDerivation : Derivation [mortalityLaw, human socrates] (mortal socrates) := by
  have law : Derivation [mortalityLaw, human socrates] mortalityLaw := .assumption (by simp)
  have instantiated := Derivation.universalElim socrates law
  have he : mortalityBody.instantiate socrates = .implies (human socrates) (mortal socrates) := by
    simp [mortalityBody, human, mortal, Formula.instantiate, Formula.substitute,
      Term.substitute, extend]
  exact .implicationElim (he ▸ instantiated) (.assumption (by simp))

#guard socratesDerivation.nodeCount = 4
#guard (searchDerivation [human socrates] [socrates] 2
  [mortalityLaw, human socrates] (mortal socrates)).isSome

#guard (proveFirstOrder 2 [mortalityLaw, human socrates] (mortal socrates)).isSome


def unary (p : Nat) (t : Term) : Formula := .predicate p [t]

def universal_to_existential (p : Nat) (t : Term) :
    Derivation [.universal (unary p (.variable 0))]
      (.existential (unary p (.variable 0))) := by
  apply Derivation.existentialIntro t
  exact Derivation.universalElim t (.assumption (by simp))

def universal_identity (p : Nat) :
    Derivation [] (.universal (.implies (unary p (.variable 0)) (unary p (.variable 0)))) := by
  apply Derivation.universalIntro
  apply Derivation.implicationIntro
  exact Derivation.assumption (by simp)

def existential_conjunction_left (p q : Nat) :
    Derivation [.existential (.conjunction (unary p (.variable 0)) (unary q (.variable 0)))]
      (.existential (unary p (.variable 0))) := by
  apply Derivation.existentialElim (body := .conjunction (unary p (.variable 0)) (unary q (.variable 0)))
  · exact Derivation.assumption (by simp)
  · have he : (Formula.existential (unary p (.variable 0))).shift =
        .existential (unary p (.variable 0)) := by
      simp [unary, Formula.shift, Formula.rename, Formula.substitute,
        liftSubstitution, Term.substitute]
    rw [he]
    apply Derivation.existentialIntro (.variable 0)
    have whole : Derivation
        (.conjunction (unary p (.variable 0)) (unary q (.variable 0)) ::
          [Formula.existential (.conjunction (unary p (.variable 0)) (unary q (.variable 0)))].map Formula.shift)
        (.conjunction (unary p (.variable 0)) (unary q (.variable 0))) :=
      .assumption (by simp)
    have part := Derivation.conjunctionLeft whole
    simpa [unary, Formula.instantiate, Formula.substitute, Term.substitute, extend] using part

#guard (universal_to_existential 0 socrates).nodeCount = 3
#guard (universal_identity 0).nodeCount = 3
#guard (existential_conjunction_left 0 1).nodeCount = 5
#guard (proveFirstOrder 2 [.universal (unary 0 (.variable 0))]
  (.existential (unary 0 (.variable 0)))).isSome

-- Capture avoidance: the formerly free variable stays outside the new binder.
#guard (Formula.universal (human (.variable 1))).substitute
  (fun _ => .variable 0) = .universal (human (.variable 1))
#guard (Formula.universal (.predicate 0 [.variable 1, .variable 0])).instantiate socrates =
  .universal (.predicate 0 [socrates, .variable 0])

-- Unification checks original equations, rejects cycles, symbols and arities.
#guard (unify? 20 [(.variable 0, socrates)]).isSome
#guard (unify? 20 [(.variable 0, .variable 1), (.variable 1, socrates)]).isSome
#guard (unify? 20 [(.variable 0, .variable 1),
  (.variable 1, .function 1 [.variable 0])]).isNone
#guard (unify? 20 [(.variable 0, .function 1 [.variable 0])]).isNone
#guard (unify? 20 [(.function 0 [], .function 1 [])]).isNone
#guard (unify? 20 [(.function 0 [], .function 0 [socrates])]).isNone
#guard (unify? 0 [(.variable 0, socrates)]).isNone
#guard (unify? 20 [(.function 1 [.variable 0], .function 1 [socrates])]).isSome

def positive (p : Nat) (t : Term) : Literal := ⟨true, ⟨p, [t]⟩⟩
def negative (p : Nat) (t : Term) : Literal := ⟨false, ⟨p, [t]⟩⟩
def mortalityClauses : ClauseSet :=
  [[negative 0 (.variable 0), positive 1 (.variable 0)],
   [positive 0 socrates], [negative 1 socrates]]

#guard (refuteFirstOrder 2 20 mortalityClauses).isSome
-- Inspect the actual computational certificate, rather than only its success tag.
#guard ((refuteFirstOrder 2 20 mortalityClauses).map
  ResolutionDerivation.nodeCount).getD 0 > 3
#guard (refuteFirstOrder 0 20 mortalityClauses).isNone
#guard (refuteFirstOrder 2 20 [[positive 0 socrates]]).isNone

-- Renaming apart avoids the spurious cycle x = f(x) between different clauses.
#guard (refuteFirstOrder 1 20
  [[positive 0 (.variable 0)], [negative 0 (.function 1 [.variable 0])]]).isSome

-- Factoring is required in addition to binary resolution.
def factoringClauses : ClauseSet :=
  [[positive 0 (.variable 0), positive 0 (.variable 1)],
   [negative 0 (.variable 0), negative 0 (.variable 1)]]
#guard (refuteFirstOrder 2 20 factoringClauses).isSome
#guard (factoringCandidates 20
  (S := factoringClauses) ⟨[positive 0 (.variable 0), positive 0 (.variable 1)], .input (by simp [factoringClauses])⟩).any
  (fun entry => entry.1.length == 1)

-- A model refutes the illegal inference P(x) / forall x P(x).
def boolModel : Model Bool :=
  ⟨fun _ _ => false, fun _ args => args = [true]⟩

theorem no_illegal_generalization :
    ¬Nonempty (Derivation [human (.variable 0)] (.universal (human (.variable 0)))) := by
  intro ⟨d⟩
  have h := derivation_sound_in_model boolModel d (fun _ => true) (by
    intro a ha
    simp only [List.mem_singleton] at ha
    subst a
    simp [human, Formula.evaluate, Term.evaluate, boolModel])
  have hf := h false
  simp [human, Formula.evaluate, Term.evaluate, extend, boolModel] at hf

-- An existential witness cannot escape its local branch.
theorem no_escaping_witness :
    ¬Nonempty (Derivation [.existential (human (.variable 0))] (human socrates)) := by
  intro ⟨d⟩
  have h := derivation_sound_in_model boolModel d (fun _ => false) (by
    intro a ha
    simp only [List.mem_singleton] at ha
    subst a
    exact ⟨true, by simp [human, Formula.evaluate, Term.evaluate, extend, boolModel]⟩)
  simp [human, socrates, Formula.evaluate, Term.evaluate, boolModel] at h

#print axioms Formula.evaluate_substitute
#print axioms derivation_sound
#print axioms resolution_sound
#print axioms refutation_unsatisfiable
#print axioms searchDerivation_sound
#print axioms refuteFirstOrder_sound
#print axioms no_illegal_generalization
#print axioms no_escaping_witness
end FirstOrderChecks
