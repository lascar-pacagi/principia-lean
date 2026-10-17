import Principia.FirstOrder.Unification

namespace Principia.FirstOrder

abbrev ResolutionEntry (S : ClauseSet) := Σ c : Clause, ResolutionDerivation S c

def clauseVariableBound (c : Clause) : Nat :=
  (c.map (fun l => (l.atom.arguments.map Term.variableBound).foldl max 0)).foldl max 0

/-- Rename the second parent's variables apart before attempting a binary inference. -/
def freshenEntry {S : ClauseSet} (offset : Nat) (entry : ResolutionEntry S) : ResolutionEntry S :=
  let rename := fun i => Term.variable (i + offset)
  ⟨Clause.substitute rename entry.1, .substitution rename entry.2⟩

def resolutionCandidates {S : ClauseSet} (unificationFuel : Nat)
    (left right : ResolutionEntry S) : List (ResolutionEntry S) :=
  let fresh := freshenEntry (clauseVariableBound left.1) right
  left.1.flatMap fun l => fresh.1.filterMap fun k => do
    if l.positive == k.positive then none else do
    let checked ← unifyAtoms? unificationFuel l.atom k.atom
    let σ := checked.1.lookup
    let c := Clause.substitute σ left.1
    let d := Clause.substitute σ fresh.1
    let pivot := l.substitute σ
    let proof : ResolutionDerivation S (resolvent c d pivot) :=
      .resolution pivot (.substitution σ left.2) (.substitution σ fresh.2)
    pure ⟨(resolvent c d pivot).eraseDups, .contraction proof⟩

/-- Unify two literals of the same sign, then contract identical instances (factoring). -/
def factoringCandidates {S : ClauseSet} (unificationFuel : Nat)
    (entry : ResolutionEntry S) : List (ResolutionEntry S) :=
  entry.1.flatMap fun l => entry.1.filterMap fun k => do
    if l.positive != k.positive then none else do
    let checked ← unifyAtoms? unificationFuel l.atom k.atom
    let σ := checked.1.lookup
    let c := (Clause.substitute σ entry.1).eraseDups
    if c = entry.1 then none
    else pure ⟨c, .contraction (.substitution σ entry.2)⟩

def findRefutation {S : ClauseSet} : List (ResolutionEntry S) → Option (ResolutionDerivation S [])
  | [] => none
  | entry :: rest =>
    if h : entry.1 = [] then some (h ▸ entry.2) else findRefutation rest

/-- Keep one certificate for each syntactically identical clause. -/
def addNewEntries {S : ClauseSet} (old fresh : List (ResolutionEntry S)) : List (ResolutionEntry S) :=
  fresh.foldl (fun entries candidate =>
    if entries.any (fun e => decide (e.1 = candidate.1)) then entries
    else entries ++ [candidate]) old

def resolutionRounds {S : ClauseSet} (unificationFuel : Nat) :
    Nat → List (ResolutionEntry S) → Option (ResolutionDerivation S [])
  | 0, entries => findRefutation entries
  | rounds + 1, entries =>
    (findRefutation entries).orElse fun _ =>
      let factors := entries.flatMap (factoringCandidates unificationFuel)
      let pairs := entries.flatMap (fun a => entries.flatMap (resolutionCandidates unificationFuel a))
      resolutionRounds unificationFuel rounds (addNewEntries entries (factors ++ pairs))

/-- A finite stage: lack of a refutation means unknown, never satisfiable. -/
def refuteFirstOrder (rounds unificationFuel : Nat) (S : ClauseSet) :
    Option (ResolutionDerivation S []) :=
  let inputs := S.attach.map (fun c => ⟨c.1, ResolutionDerivation.input c.2⟩)
  resolutionRounds unificationFuel rounds inputs

/-- Increase both the saturation and unification budgets instead of fixing either forever. -/
def resolutionStage (stage : Nat) (S : ClauseSet) : Option (ResolutionDerivation S []) :=
  refuteFirstOrder stage stage S

theorem refuteFirstOrder_sound {rounds unificationFuel : Nat} {S : ClauseSet}
    (h : (refuteFirstOrder rounds unificationFuel S).isSome = true) : Unsatisfiable S := by
  cases hs : refuteFirstOrder rounds unificationFuel S with
  | none => simp [hs] at h
  | some d => exact refutation_unsatisfiable d

end Principia.FirstOrder
