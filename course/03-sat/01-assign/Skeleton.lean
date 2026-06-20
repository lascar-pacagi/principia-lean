import Principia.Resolution.Rule

/-!
# 01-assign — Skeleton  (THIS IS YOUR FILE)

`assign` is GIVEN. Prove `eval_of_erase` and `sat_of_assign` — replace each `sorry`.

Run:  make lab C=03-sat/01-assign
Stuck? See §5 "Prove it" and §6 "Hints for the skeleton" in `explainer.qmd`.
-/
set_option warningAsError true
namespace Principia

/-- Simplify `cnf` under "`l` is true": drop clauses containing `l`, erase `∼l` from the rest. GIVEN. -/
def assign (cnf : Cnf) (l : Lit) : Cnf :=
  (cnf.filter (fun c => decide (l ∉ c))).map (fun c => c.erase l.neg)

-- satisfying a clause after erasing a literal implies satisfying the original
theorem eval_of_erase (v) (c : Clause) (x : Lit) (h : Clause.eval v (c.erase x) = true) :
    Clause.eval v c = true := by
  sorry

-- if `v` makes `l` true and satisfies the simplified CNF, it satisfies the original
theorem sat_of_assign (v) (cnf : Cnf) (l : Lit) (hl : l.eval v = true)
    (h : Cnf.eval v (assign cnf l) = true) : Cnf.eval v cnf = true := by
  sorry

end Principia
