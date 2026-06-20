import Principia.Resolution.Rule

/-!
# Principia.Resolution.Soundness — resolution soundness (Course 2, slice 2.4)

`Refut S [] → S.Unsat`: deriving the empty clause witnesses unsatisfiability. The engine is that the
**resolvent preserves models** — any valuation satisfying both parents satisfies the resolvent — so by
induction every derived clause holds in every model of `S`; for the empty clause (satisfied by nobody)
that's a contradiction, hence no model exists. The corollary `taut_of_refut` closes the chain:
refuting the clauses of `∼φ` proves `φ` valid.
-/
namespace Principia

open scoped Principia.Form

/-- A literal and its complement have opposite truth values. -/
theorem Lit.neg_eval (v) (l : Lit) : l.neg.eval v = !l.eval v := by
  simp [Lit.eval, Lit.neg]; cases l.pol <;> simp

/-- If a clause is satisfied and literal `l` is false under `v`, erasing `l` keeps it satisfied
    (the witnessing literal, being true, differs from `l` and so survives the erase). -/
theorem erase_eval (v) (c : Clause) (l : Lit) (hc : Clause.eval v c = true) (hl : Lit.eval v l = false) :
    Clause.eval v (c.erase l) = true := by
  rw [Clause.eval, List.any_eq_true] at hc ⊢
  obtain ⟨x, hx_mem, hx⟩ := hc
  refine ⟨x, ?_, hx⟩
  have hne : x ≠ l := by intro h; subst h; rw [hl] at hx; exact Bool.noConfusion hx
  exact (List.mem_erase_of_ne hne).mpr hx_mem

/-- **Resolvent preserves models.** -/
theorem resolvent_sound (v) (c d : Clause) (l : Lit)
    (hc : Clause.eval v c = true) (hd : Clause.eval v d = true) :
    Clause.eval v (resolvent c d l) = true := by
  rw [resolvent, clause_eval_append]
  cases hl : Lit.eval v l with
  | false => have := erase_eval v c l hc hl; simp [this]            -- l false ⇒ c.erase l satisfied
  | true =>
      have hln : l.neg.eval v = false := by simp [Lit.neg_eval, hl]  -- l true ⇒ ∼l false
      have := erase_eval v d l.neg hd hln; simp [this]               -- ⇒ d.erase ∼l satisfied

/-- Every clause derivable by resolution holds in every model of `S`. -/
theorem refut_sound {S : Cnf} : ∀ {c}, Refut S c → ∀ v, Cnf.eval v S = true → Clause.eval v c = true := by
  intro c d
  induction d with
  | hyp h => intro v hS; rw [Cnf.eval] at hS; exact List.all_eq_true.mp hS _ h
  | res l dc dd ihc ihd => intro v hS; exact resolvent_sound v _ _ l (ihc v hS) (ihd v hS)

/-- **Soundness.** A refutation of `S` witnesses that `S` is unsatisfiable. -/
theorem refut_unsat {S : Cnf} (d : Refut S []) : S.Unsat := by
  intro v
  cases hv : Cnf.eval v S with
  | false => rfl
  | true => have := refut_sound d v hv; simp [Clause.eval] at this   -- `□` can't be satisfied

/-- The full chain: refuting the clauses of `∼φ` proves `φ` is a tautology. -/
theorem taut_of_refut {φ : Form} (d : Refut (toCnf false φ) []) : Form.Tautology φ :=
  (taut_iff_cnf_unsat φ).mpr (refut_unsat d)

end Principia
