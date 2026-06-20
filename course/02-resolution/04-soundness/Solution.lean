import Principia.Resolution.Rule

/-!
# 04-soundness — Solution  (verified answer key)

`make test` kernel-checks this; `make axioms` audits it. Graduates into `Principia.Resolution.Soundness`.
Read to understand *why*, not to copy.
-/
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

-- induction on the refutation: `hyp` reads the clause off a model of S; `res` invokes resolvent_sound.
theorem refut_sound {S : Cnf} : ∀ {c}, Refut S c → ∀ v, Cnf.eval v S = true → Clause.eval v c = true := by
  intro c d
  induction d with
  | hyp h => intro v hS; rw [Cnf.eval] at hS; exact List.all_eq_true.mp hS _ h
  | res l dc dd ihc ihd => intro v hS; exact resolvent_sound v _ _ l (ihc v hS) (ihd v hS)

theorem refut_unsat {S : Cnf} (d : Refut S []) : S.Unsat := by
  intro v
  cases hv : Cnf.eval v S with
  | false => rfl
  | true => have := refut_sound d v hv; simp [Clause.eval] at this

theorem taut_of_refut {φ : Form} (d : Refut (toCnf false φ) []) : Form.Tautology φ :=
  (taut_iff_cnf_unsat φ).mpr (refut_unsat d)

/-! ## Checks (Tier-1 + honesty audit) -/

-- soundness in action: the hand refutation of {p, ¬p} certifies its unsatisfiability
example : Cnf.Unsat [[⟨0,true⟩], [⟨0,false⟩]] :=
  refut_unsat (.res ⟨0,true⟩ (.hyp (c := [⟨0,true⟩]) (by decide)) (.hyp (c := [⟨0,false⟩]) (by decide)))

#print axioms refut_unsat
#print axioms taut_of_refut

end Principia
