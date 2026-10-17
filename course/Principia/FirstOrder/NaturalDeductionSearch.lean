import Principia.FirstOrder.NaturalDeduction

namespace Principia.FirstOrder

/-- Finite search over logical introduction and elimination rules. Pools supply intermediate
formulas and witnesses. The explicit weakening and fresh-index variants used in the completeness
construction are not separate search branches. Fixed pools need not find every proof. -/
def searchDerivation (formulas : List Formula) (terms : List Term) :
    Nat → (Γ : List Formula) → (goal : Formula) → Option (Derivation Γ goal)
  | 0, _, _ => none
  | fuel + 1, Γ, goal =>
    let recurse := searchDerivation formulas terms fuel
    let assumption := if h : goal ∈ Γ then some (Derivation.assumption h) else none
    assumption.orElse fun _ =>
    let introduce : Option (Derivation Γ goal) :=
      match goal with
      | .implies a b => (recurse (a :: Γ) b).map Derivation.implicationIntro
      | .conjunction a b => do
        let da ← recurse Γ a
        let db ← recurse Γ b
        pure (Derivation.conjunctionIntro da db)
      | .disjunction a b =>
        ((recurse Γ a).map Derivation.disjunctionLeft).orElse
          (fun _ => (recurse Γ b).map Derivation.disjunctionRight)
      | .universal body =>
        (recurse (Γ.map Formula.shift) body).map Derivation.universalIntro
      | .existential body => terms.findSome? fun t =>
        (recurse Γ (body.instantiate t)).map (Derivation.existentialIntro t)
      | _ => none
    introduce.orElse fun _ =>
    let useContext : Option (Derivation Γ goal) := Γ.attach.findSome? fun entry =>
      match entry with
      | ⟨.implies a b, hm⟩ =>
        if he : b = goal then
          (recurse Γ a).map (fun da => he ▸ Derivation.implicationElim (.assumption hm) da)
        else none
      | ⟨.conjunction a b, hm⟩ =>
        if he : a = goal then some (he ▸ Derivation.conjunctionLeft (.assumption hm))
        else if he : b = goal then some (he ▸ Derivation.conjunctionRight (.assumption hm))
        else none
      | ⟨.universal body, hm⟩ => terms.findSome? fun t =>
        if he : body.instantiate t = goal then
          some (he ▸ Derivation.universalElim t (.assumption hm))
        else none
      | ⟨.falsum, hm⟩ => some (Derivation.falseElim (.assumption hm))
      | _ => none
    useContext.orElse fun _ =>
    let implicationUse : Option (Derivation Γ goal) := formulas.findSome? fun a => do
      let df ← recurse Γ (.implies a goal)
      let da ← recurse Γ a
      pure (Derivation.implicationElim df da)
    implicationUse.orElse fun _ =>
    let conjunctionUse : Option (Derivation Γ goal) := formulas.findSome? fun a =>
      ((recurse Γ (.conjunction goal a)).map Derivation.conjunctionLeft).orElse
        (fun _ => (recurse Γ (.conjunction a goal)).map Derivation.conjunctionRight)
    conjunctionUse.orElse fun _ =>
    let universalUse : Option (Derivation Γ goal) := formulas.findSome? fun body =>
      terms.findSome? fun t =>
        if he : body.instantiate t = goal then
          (recurse Γ (.universal body)).map (fun d => he ▸ Derivation.universalElim t d)
        else none
    universalUse.orElse fun _ =>
    let existentialUse : Option (Derivation Γ goal) := formulas.findSome? fun body => do
      let de ← recurse Γ (.existential body)
      let branch ← recurse (body :: Γ.map Formula.shift) goal.shift
      pure (Derivation.existentialElim de branch)
    existentialUse.orElse fun _ =>
    let disjunctionUse : Option (Derivation Γ goal) := formulas.findSome? fun a =>
      formulas.findSome? fun b => do
        let dor ← recurse Γ (.disjunction a b)
        let dl ← recurse (a :: Γ) goal
        let dr ← recurse (b :: Γ) goal
        pure (Derivation.disjunctionElim dor dl dr)
    disjunctionUse.orElse fun _ =>
    ((recurse Γ .falsum).map Derivation.falseElim).orElse fun _ =>
      (recurse (goal.negation :: Γ) .falsum).map Derivation.contradiction

theorem searchDerivation_sound {formulas : List Formula} {terms : List Term}
    {fuel : Nat} {Γ : List Formula} {goal : Formula}
    (h : (searchDerivation formulas terms fuel Γ goal).isSome = true) :
    Formula.Entails Γ goal := by
  cases hs : searchDerivation formulas terms fuel Γ goal with
  | none => simp [hs] at h
  | some d => exact derivation_sound d

/-- Enumerate finite argument lists of length at most n from a finite alphabet. -/
def argumentLists {α : Type} (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => [] :: alphabet.flatMap (fun a => (argumentLists alphabet n).map (a :: ·))

/-- Finite term pool: bound symbol names, variable names, depth and arity together. -/
def enumerateTerms (bound : Nat) : Nat → List Term
  | 0 => (List.range (bound + 1)).map Term.variable ++
      (List.range (bound + 1)).map (fun f => .function f [])
  | depth + 1 => (List.range (bound + 1)).map Term.variable ++
      (List.range (bound + 1)).flatMap (fun f =>
        (argumentLists (enumerateTerms bound depth) bound).map (Term.function f))

/-- Finite formula pool covering a growing alphabet, arity and formula depth. -/
def enumerateFormulas (bound : Nat) (terms : List Term) : Nat → List Formula
  | 0 => .falsum :: (List.range (bound + 1)).flatMap (fun p =>
      (argumentLists terms bound).map (Formula.predicate p))
  | depth + 1 =>
    let previous := enumerateFormulas bound terms depth
    enumerateFormulas bound terms 0 ++
      previous.flatMap (fun a => previous.flatMap (fun b =>
        [.implies a b, .conjunction a b, .disjunction a b])) ++
      previous.flatMap (fun a => [.universal a, .existential a])

/-- Stage n expands proof depth AND both finite pools. It may be very expensive; `none`
means only that this stage found nothing. Every individual stage terminates. -/
def derivationStage (n : Nat) (Γ : List Formula) (goal : Formula) :
    Option (Derivation Γ goal) :=
  let terms := enumerateTerms n n
  let formulas := enumerateFormulas n terms n
  searchDerivation formulas terms (n + 1) Γ goal

end Principia.FirstOrder

namespace Principia.FirstOrder

def Term.subterms : Term → List Term
  | .variable i => [.variable i]
  | .function f args => .function f args :: (args.map Term.subterms).flatten

def Formula.subformulas (a : Formula) : List Formula :=
  a :: match a with
  | .predicate _ _ | .falsum => []
  | .implies b c | .conjunction b c | .disjunction b c => b.subformulas ++ c.subformulas
  | .universal b | .existential b => b.subformulas

def Formula.terms : Formula → List Term
  | .predicate _ args => (args.map Term.subterms).flatten
  | .falsum => []
  | .implies a b | .conjunction a b | .disjunction a b => a.terms ++ b.terms
  | .universal a | .existential a => a.terms

/-- Convenient bounded search using terms and subformulas already present in the problem.
This heuristic pool is deliberately separate from the exhaustive staged interface. -/
def proveFirstOrder (fuel : Nat) (Γ : List Formula) (goal : Formula) : Option (Derivation Γ goal) :=
  let terms := ((Γ ++ [goal]).flatMap Formula.terms ++ [Term.variable 0, Term.function 0 []]).eraseDups
  let seed := (Γ ++ [goal]).flatMap Formula.subformulas
  let instances := seed.flatMap fun a => match a with
    | .universal body | .existential body => terms.map body.instantiate
    | _ => []
  let formulas := (seed ++ instances).eraseDups.filter (fun a => decide (a ≠ goal))
  searchDerivation formulas terms fuel Γ goal

theorem proveFirstOrder_sound {fuel : Nat} {Γ : List Formula} {goal : Formula}
    (h : (proveFirstOrder fuel Γ goal).isSome = true) : Formula.Entails Γ goal :=
  searchDerivation_sound h

theorem derivationStage_sound {n : Nat} {Γ : List Formula} {goal : Formula}
    (h : (derivationStage n Γ goal).isSome = true) : Formula.Entails Γ goal :=
  searchDerivation_sound h

end Principia.FirstOrder
