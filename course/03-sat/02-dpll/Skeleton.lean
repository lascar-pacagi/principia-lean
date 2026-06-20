import Principia.Sat.Basic

/-!
# 02-dpll — Skeleton  (THIS IS YOUR FILE)

The solver `dpll` and the satisfaction predicate `satBy` are GIVEN. Prove `satBy_of_assign` (mirrors
slice 3.1's `sat_of_assign`) and `dpll_sound` (model soundness, by induction on `fuel`).

Run:  make lab C=03-sat/02-dpll
Stuck? See §5 "Prove it" and §6 "Hints for the skeleton" in `explainer.qmd`.
-/
set_option warningAsError true
namespace Principia

def dpll : Nat → Cnf → Option (List Lit)
  | 0, _ => none
  | _, [] => some []
  | fuel + 1, cnf =>
    if ([] : Clause) ∈ cnf then none
    else
      match cnf with
      | (l :: _) :: _ =>
        match dpll fuel (assign cnf l) with
        | some ls => some (l :: ls)
        | none    => (dpll fuel (assign cnf l.neg)).map (fun ls => l.neg :: ls)
      | _ => none

def Clause.satBy (ls : List Lit) (c : Clause) : Bool := c.any (fun lit => decide (lit ∈ ls))
def Cnf.satBy (ls : List Lit) (cnf : Cnf) : Bool := cnf.all (Clause.satBy ls)

/-! Your two theorems. -/

-- committing to `l` lifts satisfaction from the simplified CNF to the original (mirror `sat_of_assign`)
theorem satBy_of_assign (ls : List Lit) (cnf : Cnf) (l : Lit)
    (h : Cnf.satBy ls (assign cnf l) = true) : Cnf.satBy (l :: ls) cnf = true := by
  sorry

-- model soundness: whatever DPLL returns satisfies the clause set
theorem dpll_sound : ∀ (fuel : Nat) (cnf : Cnf) (ls : List Lit),
    dpll fuel cnf = some ls → Cnf.satBy ls cnf = true := by
  sorry

end Principia
