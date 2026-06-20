import Principia.Resolution.Rule

/-!
# 03-prover — Solution  (verified answer key)

`make test` kernel-checks this; `make axioms` audits it. Graduates into `Principia.Resolution.Prover`.
Read to understand *why*, not to copy.
-/
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

theorem refute?_refutable {S : Cnf} {fuel : Nat} (h : (refute? S fuel).isSome) : S.Refutable := by
  cases hp : refute? S fuel with
  | none   => rw [hp] at h; simp at h
  | some d => exact ⟨d⟩

/-! ## Checks (Tier-2 computational + honesty audit) -/

-- the prover finds refutations of unsatisfiable sets…
#guard (refute? [[⟨0,true⟩], [⟨0,false⟩]] 3).isSome == true
#guard (refute? [[⟨0,true⟩, ⟨1,true⟩], [⟨0,false⟩], [⟨1,false⟩]] 4).isSome == true
-- …and gives up on a satisfiable one (no □ to find):
#guard (refute? [[⟨0,true⟩]] 5).isSome == false

-- run + certify in one step: a successful search proves refutability automatically
example : Cnf.Refutable [[⟨0,true⟩], [⟨0,false⟩]] := refute?_refutable (fuel := 3) (by decide)

#print axioms refute?_refutable

end Principia
