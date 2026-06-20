import Principia.Resolution.Prover
import Principia.Resolution.Soundness
import Principia.NatDed.Completeness

/-!
# 05-completeness — Skeleton  (THIS IS YOUR FILE)

Compose the course's theorems into a verified decision procedure and the tie to Course 1 — replace each
`sorry`. (Each is a short `cases`/apply, like slice 2.3's `refute?_refutable`.)

Run:  make lab C=02-resolution/05-completeness
Stuck? See §5 "Prove it" and §6 "Hints for the skeleton" in `explainer.qmd`.
-/
set_option warningAsError true
open scoped Principia.Form

namespace Principia

-- if the saturation prover succeeds, the clause set really is unsatisfiable
theorem refute?_unsat {S : Cnf} {fuel : Nat} (h : (refute? S fuel).isSome) : S.Unsat := by
  sorry

-- refuting the clauses of ∼φ certifies φ is a tautology (a verified resolution tautology-prover)
theorem prove_taut_by_resolution {φ : Form} {fuel : Nat}
    (h : (refute? (toCnf false φ) fuel).isSome) : Form.Tautology φ := by
  sorry

-- the achievable half of the tie to Course 1: a refutation of ∼φ gives a natural-deduction proof of φ
theorem refutable_to_provable {φ : Form} (d : Refut (toCnf false φ) []) : Nonempty ([] ⊢ φ) := by
  sorry

end Principia
