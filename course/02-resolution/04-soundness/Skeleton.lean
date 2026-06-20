import Principia.Resolution.Rule

/-!
# 04-soundness — Skeleton  (THIS IS YOUR FILE)

The per-step lemmas (`Lit.neg_eval`, `erase_eval`, `resolvent_sound`) are GIVEN. Prove `refut_sound`
(induction on the refutation), `refut_unsat` (soundness), and `taut_of_refut`.

Run:  make lab C=02-resolution/04-soundness
Stuck? See §5 "Prove it" and §6 "Hints for the skeleton" in `explainer.qmd`.
-/
set_option warningAsError true
open scoped Principia.Form

namespace Principia

theorem Lit.neg_eval (v) (l : Lit) : l.neg.eval v = !l.eval v := by
  simp [Lit.eval, Lit.neg]; cases l.pol <;> simp
theorem erase_eval (v) (c : Clause) (l : Lit) (hc : Clause.eval v c = true) (hl : Lit.eval v l = false) :
    Clause.eval v (c.erase l) = true := by
  rw [Clause.eval, List.any_eq_true] at hc ⊢
  obtain ⟨x, hx_mem, hx⟩ := hc
  refine ⟨x, ?_, hx⟩
  have hne : x ≠ l := by intro h; subst h; rw [hl] at hx; exact Bool.noConfusion hx
  exact (List.mem_erase_of_ne hne).mpr hx_mem
theorem resolvent_sound (v) (c d : Clause) (l : Lit)
    (hc : Clause.eval v c = true) (hd : Clause.eval v d = true) :
    Clause.eval v (resolvent c d l) = true := by
  rw [resolvent, clause_eval_append]
  cases hl : Lit.eval v l with
  | false => have := erase_eval v c l hc hl; simp [this]
  | true =>
      have hln : l.neg.eval v = false := by simp [Lit.neg_eval, hl]
      have := erase_eval v d l.neg hd hln; simp [this]

/-! Your three theorems. -/

-- every derived clause holds in every model of S (induct on the refutation `d`)
theorem refut_sound {S : Cnf} : ∀ {c}, Refut S c → ∀ v, Cnf.eval v S = true → Clause.eval v c = true := by
  sorry

-- soundness: a refutation witnesses unsatisfiability
theorem refut_unsat {S : Cnf} (d : Refut S []) : S.Unsat := by
  sorry

-- the full chain: refuting the clauses of ∼φ proves φ is a tautology
theorem taut_of_refut {φ : Form} (d : Refut (toCnf false φ) []) : Form.Tautology φ := by
  sorry

end Principia
