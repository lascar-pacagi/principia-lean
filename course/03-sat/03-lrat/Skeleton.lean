import Principia.Resolution.Soundness

/-!
# 03-lrat — Skeleton  (THIS IS YOUR FILE)

The checker (`Step`, `checkStep`, `runProof`, `check`, `Entailed`) is GIVEN. Prove `runProof_preserves`
(every database clause stays entailed by the input) and `check_unsat` (acceptance ⟹ unsatisfiable).

Run:  make lab C=03-sat/03-lrat
Stuck? See §5 "Prove it" and §6 "Hints for the skeleton" in `explainer.qmd`.
-/
set_option warningAsError true
namespace Principia

structure Step where
  c   : Clause
  i   : Nat
  j   : Nat
  lit : Lit
def checkStep (db : List Clause) (s : Step) : Bool :=
  match db[s.i]?, db[s.j]? with
  | some ci, some cj => decide (resolvent ci cj s.lit = s.c)
  | _, _ => false
def runProof : List Clause → List Step → Option (List Clause)
  | db, [] => some db
  | db, s :: rest => if checkStep db s then runProof (db ++ [s.c]) rest else none
def check (cnf : Cnf) (proof : List Step) : Bool :=
  match runProof cnf proof with
  | some db => decide (([] : Clause) ∈ db)
  | none    => false
def Entailed (cnf : Cnf) (c : Clause) : Prop := ∀ v, Cnf.eval v cnf = true → Clause.eval v c = true

/-! Your two theorems. -/

-- replaying preserves "every database clause is entailed by cnf"
theorem runProof_preserves {cnf : Cnf} : ∀ (proof : List Step) (db db' : List Clause),
    (∀ c ∈ db, Entailed cnf c) → runProof db proof = some db' → (∀ c ∈ db', Entailed cnf c) := by
  sorry

-- the keystone: if the checker accepts, the CNF is unsatisfiable
theorem check_unsat {cnf : Cnf} {proof : List Step} (h : check cnf proof = true) : cnf.Unsat := by
  sorry

end Principia
