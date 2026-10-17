import Principia.FirstOrder
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
open Principia.FirstOrder
namespace GeneralFirstOrderChecks

-- These statements quantify over every input, not just the examples below.
example (Γ : List Formula) (a : Formula) (h : Formula.Entails Γ a) :
    Nonempty (Derivation Γ a) := deduction_complete h
example (S : ClauseSet) (h : Unsatisfiable S) :
    Nonempty (ResolutionDerivation S []) := resolution_complete h
example (Γ : List Formula) (a : Formula) :
    Nonempty (Derivation Γ a) ↔ Formula.Entails Γ a := deduction_iff_entails Γ a
example (S : ClauseSet) : Nonempty (ResolutionDerivation S []) ↔ Unsatisfiable S :=
  resolution_iff_unsatisfiable S

-- General compiler theorems, with no finite-domain or quantifier-depth restriction.
example {D : Type} (inhabited : Nonempty D) (M : Model D) (ρ : Nat → D)
    (a : Formula) (h : a.evaluate M ρ) :
    ∃ N : Model D, AgreeBelow M N a.functionBound ∧
      SatisfiesClauses N (clausify a).clauses :=
  clausify_model_expansion inhabited M ρ a h
example {D : Type} (inhabited : Nonempty D) (M : Model D) (a : Formula)
    (h : SatisfiesClauses M (clausify a).clauses) : ∃ ρ, a.evaluate M ρ :=
  clausify_model_recovery inhabited M a h
example (a : Formula) : a.Satisfiable ↔ ClausesSatisfiable (clausify a).clauses :=
  clausify_equisatisfiable a
example (Γ : List Formula) (goal : Formula) :
    Nonempty (Derivation Γ goal) ↔
      Nonempty (ResolutionDerivation (clausify (counterexampleFormula Γ goal)).clauses []) :=
  deduction_iff_clausal_refutation Γ goal

-- A finite model oracle independent of the compiler, for regression tests only.
def vectors : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (vectors n).flatMap fun xs => [false :: xs, true :: xs]
def environment (xs : List Bool) : Nat → Bool := fun i => xs[i]?.getD false
def argumentIndex : List Bool → Nat
  | [] => 0
  | b :: rest => (if b then 1 else 0) + 2 * argumentIndex rest

def termValue (fn : Nat → List Bool → Bool) (ρ : Nat → Bool) : Term → Bool
  | .variable i => ρ i
  | .function f args => fn f (args.map (termValue fn ρ))
def formulaValue (fn pred : Nat → List Bool → Bool) (ρ : Nat → Bool) : Formula → Bool
  | .predicate p args => pred p (args.map (termValue fn ρ))
  | .falsum => false
  | .implies a b => !formulaValue fn pred ρ a || formulaValue fn pred ρ b
  | .conjunction a b => formulaValue fn pred ρ a && formulaValue fn pred ρ b
  | .disjunction a b => formulaValue fn pred ρ a || formulaValue fn pred ρ b
  | .universal a => formulaValue fn pred (extend false ρ) a &&
      formulaValue fn pred (extend true ρ) a
  | .existential a => formulaValue fn pred (extend false ρ) a ||
      formulaValue fn pred (extend true ρ) a

def originalFunctions : Nat → List Bool → Bool := fun _ args => args.headD false
def expansions : List SkolemSymbol → List (List (Nat × Nat))
  | [] => [[]]
  | s :: rest => (List.range (2 ^ (2 ^ s.dependencies.length))).flatMap fun mask =>
      (expansions rest).map ((s.symbol, mask) :: ·)
def extendedFunctions (tables : List (Nat × Nat)) (f : Nat) (args : List Bool) : Bool :=
  match tables.find? (fun pair => pair.1 == f) with
  | none => originalFunctions f args
  | some (_, mask) => mask.testBit (argumentIndex args)
def clauseValue (fn pred : Nat → List Bool → Bool) (ρ : Nat → Bool) (c : Clause) : Bool :=
  c.any fun l =>
    let atom := pred l.atom.symbol (l.atom.arguments.map (termValue fn ρ))
    if l.positive then atom else !atom

def agreesInBoolModel (pred : Nat → List Bool → Bool) (a : Formula) : Bool :=
  let result := clausify a
  let freeCount := (a.support.map (· + 1)).foldl max 0
  let inputSat := (vectors freeCount).any fun xs =>
    formulaValue originalFunctions pred (environment xs) a
  let outputSat := (expansions result.skolemSymbols).any fun tables =>
    (vectors result.nextVariable).all fun xs =>
      result.clauses.all (clauseValue (extendedFunctions tables) pred (environment xs))
  inputSat == outputSat

def relation (args : List Term) : Formula := .predicate 0 args
def alternating : Formula := .universal (.existential
  (relation [.variable 1, .variable 0]))
def fixedWitness : Formula := .existential (.universal
  (relation [.variable 1, .variable 0]))
def twoWitnesses : Formula := .universal (.existential (.universal (.existential
  (.conjunction (relation [.variable 3, .variable 2])
    (relation [.variable 1, .variable 0])))))
def separateBranches : Formula := .disjunction
  (.universal (.predicate 0 [.variable 0]))
  (.universal (.predicate 1 [.variable 0]))
def freeCounterexample : Formula := .conjunction
  (.predicate 0 [.variable 0]) (Formula.predicate 0 [.variable 1]).negation

def dependentBranches : Formula := .universal (.disjunction
  (.existential (.predicate 0 [.variable 1, .variable 0]))
  (.universal (.predicate 1 [.variable 1, .variable 0])))
def successiveWitnesses : Formula := .universal (.existential (.existential
  (.conjunction (.predicate 0 [.variable 2, .variable 1])
    (.predicate 0 [.variable 1, .variable 0]))))

def predicates : List (Nat → List Bool → Bool) :=
  [fun _ _ => false, fun _ _ => true,
   fun _ xs => xs.headD false,
   fun _ xs => !(xs.headD false),
   fun _ xs => xs[0]?.getD false == xs[1]?.getD false,
   fun p xs => if p == 0 then xs.headD false else !(xs.headD false)]
def inputs : List Formula :=
  [alternating, fixedWitness, twoWitnesses, separateBranches, freeCounterexample,
   dependentBranches, successiveWitnesses, dependentBranches.negation,
   successiveWitnesses.negation, .predicate 0 [.variable 3],
   alternating.negation, fixedWitness.negation, separateBranches.negation,
   .falsum, Formula.falsum.negation,
   .existential (.predicate 0 [.function 7 [], .variable 0])]
#guard predicates.all (fun p => inputs.all (agreesInBoolModel p))

#guard (clausify alternating).skolemSymbols = [⟨0, [0]⟩]
#guard (clausify fixedWitness).skolemSymbols = [⟨0, []⟩]
#guard (clausify twoWitnesses).skolemSymbols = [⟨0, [0]⟩, ⟨1, [0, 1]⟩]
#guard (clausify separateBranches).nextVariable = 2
#guard (clausify freeCounterexample).skolemSymbols = [⟨0, []⟩, ⟨1, []⟩]
#guard (clausify (.existential (.predicate 0 [.function 7 [], .variable 0]))).skolemSymbols =
  [⟨8, []⟩]

-- The executable frontend returns the resolution certificate directly, with no ND search.
def c : Term := .function 0 []
def p (t : Term) : Formula := .predicate 0 [t]
def q (t : Term) : Formula := .predicate 1 [t]
def rule : Formula := .universal (.implies (p (.variable 0)) (q (.variable 0)))
#guard (proveViaClauses 2 20 [rule, p c] (q c)).isSome
#guard ((proveViaClauses 2 20 [rule, p c] (q c)).map
  (fun proof => proof.refutation.nodeCount)).getD 0 > 3
#guard (proveViaClauses 1 20 [] (.disjunction (p (.variable 0))
  (p (.variable 1)).negation)).isNone

#print axioms deduction_complete
#print axioms resolution_complete
#print axioms deduction_iff_entails
#print axioms resolution_iff_unsatisfiable
#print axioms toNnf_correct
#print axioms matrix_toClauses_correct
#print axioms clausify_model_expansion
#print axioms clausify_model_recovery
#print axioms clausify_equisatisfiable
#print axioms clausify_unsatisfiable
#print axioms clausal_refutation_sound
#print axioms entails_iff_clausal_refutation
#print axioms deduction_iff_clausal_refutation
#print axioms proveViaClauses_sound
end GeneralFirstOrderChecks
