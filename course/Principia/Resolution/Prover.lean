import Principia.Resolution.Rule

/-!
# Principia.Resolution.Prover — saturation search (Course 2, slice 2.3)

A **saturation** prover: keep all derived clauses (each paired with its `Refut` proof), and each round add
*every* pairwise resolvent; stop when the empty clause `□` appears. Like the slice-1.5 prover, it returns
a **typed** `Refut S []`, so a "yes" carries a real refutation — `refute?_refutable` just reads it off.
Bounded by `fuel`; intentionally naive (no subsumption/dedup), so its "no" only means "not found in this
many rounds". (`refute?_unsat`, in slice 2.4, gives "yes" its semantic meaning.)
-/
namespace Principia

/-- A derived clause together with its resolution proof from `S`. -/
abbrev Entry (S : Cnf) := Σ c : Clause, Refut S c

/-- The hypotheses of `S`, each with its one-step `hyp` derivation. -/
def Cnf.entries (S : Cnf) : List (Entry S) := S.attach.map (fun x => ⟨x.1, .hyp x.2⟩)

/-- Find the empty clause among derived entries (returning its refutation). -/
def findEmpty {S : Cnf} : List (Entry S) → Option (Refut S [])
  | [] => none
  | e :: rest => if h : e.1 = [] then some (h ▸ e.2) else findEmpty rest

/-- All resolvents of `e1` with `e2` — one per literal of `e1` whose complement is in `e2`. -/
def pairResolvents {S : Cnf} (e1 e2 : Entry S) : List (Entry S) :=
  e1.1.filterMap fun l =>
    if l.neg ∈ e2.1 then some ⟨resolvent e1.1 e2.1 l, .res l e1.2 e2.2⟩ else none

def allResolvents {S : Cnf} (es : List (Entry S)) : List (Entry S) :=
  es.flatMap fun e1 => es.flatMap fun e2 => pairResolvents e1 e2

/-- Saturate: each round look for `□`; otherwise add all pairwise resolvents and recurse. -/
def search {S : Cnf} : Nat → List (Entry S) → Option (Refut S [])
  | 0,        es => findEmpty es
  | fuel + 1, es =>
    match findEmpty es with
    | some d => some d
    | none   => search fuel (es ++ allResolvents es)

/-- Search for a refutation of `S` within `fuel` saturation rounds. -/
def refute? (S : Cnf) (fuel : Nat) : Option (Refut S []) := search fuel S.entries

/-- The prover is correct by construction: a successful search yields a genuine refutation. -/
theorem refute?_refutable {S : Cnf} {fuel : Nat} (h : (refute? S fuel).isSome) : S.Refutable := by
  cases hp : refute? S fuel with
  | none   => rw [hp] at h; simp at h
  | some d => exact ⟨d⟩

end Principia
