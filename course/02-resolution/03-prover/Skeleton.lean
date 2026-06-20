import Principia.Resolution.Rule

/-!
# 03-prover — Skeleton  (THIS IS YOUR FILE)

The saturation search (`refute?` and helpers) is GIVEN. Prove `refute?_refutable` — replace the `sorry`.
The point (as in slice 1.5): the search returns a *typed* `Refut S []`, so refutability is read straight
off the result.

Run:  make lab C=02-resolution/03-prover
Stuck? See §5 "Prove it" and §6 "Hints for the skeleton" in `explainer.qmd`.
-/
set_option warningAsError true

namespace Principia

abbrev Entry (S : Cnf) := Σ c : Clause, Refut S c
def Cnf.entries (S : Cnf) : List (Entry S) := S.attach.map (fun x => ⟨x.1, .hyp x.2⟩)
def findEmpty {S : Cnf} : List (Entry S) → Option (Refut S [])
  | [] => none
  | e :: rest => if h : e.1 = [] then some (h ▸ e.2) else findEmpty rest
def pairResolvents {S : Cnf} (e1 e2 : Entry S) : List (Entry S) :=
  e1.1.filterMap fun l =>
    if l.neg ∈ e2.1 then some ⟨resolvent e1.1 e2.1 l, .res l e1.2 e2.2⟩ else none
def allResolvents {S : Cnf} (es : List (Entry S)) : List (Entry S) :=
  es.flatMap fun e1 => es.flatMap fun e2 => pairResolvents e1 e2
def search {S : Cnf} : Nat → List (Entry S) → Option (Refut S [])
  | 0,        es => findEmpty es
  | fuel + 1, es =>
    match findEmpty es with
    | some d => some d
    | none   => search fuel (es ++ allResolvents es)
def refute? (S : Cnf) (fuel : Nat) : Option (Refut S []) := search fuel S.entries

/-! Your theorem. -/

-- A successful search is a real refutation. (Pattern-match the `Option`: `none` contradicts `h`,
-- `some d` gives the derivation — wrap it in `Nonempty`.)
theorem refute?_refutable {S : Cnf} {fuel : Nat} (h : (refute? S fuel).isSome) : S.Refutable := by
  sorry

end Principia
