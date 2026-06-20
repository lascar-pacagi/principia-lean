import Principia.Resolution.Rule

/-!
# Principia.Sat.Basic — assignments and the `assign` operation (Course 3, slice 3.1)

A SAT solver searches for a model of a clause set, simplifying as it goes. The core operation is
`assign cnf l` — commit to making literal `l` true: drop the clauses it satisfies, and erase the now-false
`∼l` from the rest. The key invariant (`sat_of_assign`) is that this **preserves satisfiability** under
assignments that make `l` true — which is what lets DPLL (slice 3.2) reconstruct a model.

Reuses the clause representation from `Resolution.Cnf` (`Lit`/`Clause`/`Cnf`/`eval`/`Sat`/`Unsat`).
-/
namespace Principia

/-- Simplify `cnf` under "`l` is true": drop clauses containing `l`, erase `∼l` from the rest. -/
def assign (cnf : Cnf) (l : Lit) : Cnf :=
  (cnf.filter (fun c => decide (l ∉ c))).map (fun c => c.erase l.neg)

/-- Satisfying a clause after erasing a literal implies satisfying the original (erasing only weakens). -/
theorem eval_of_erase (v) (c : Clause) (x : Lit) (h : Clause.eval v (c.erase x) = true) :
    Clause.eval v c = true := by
  rw [Clause.eval, List.any_eq_true] at h ⊢
  obtain ⟨lit, hmem, hlit⟩ := h
  exact ⟨lit, List.mem_of_mem_erase hmem, hlit⟩

/-- If `v` makes `l` true and satisfies the simplified CNF, it satisfies the original. -/
theorem sat_of_assign (v) (cnf : Cnf) (l : Lit) (hl : l.eval v = true)
    (h : Cnf.eval v (assign cnf l) = true) : Cnf.eval v cnf = true := by
  rw [Cnf.eval, List.all_eq_true] at h ⊢
  intro c hc
  cases hlc : decide (l ∈ c) with
  | true =>
      have hin : l ∈ c := of_decide_eq_true hlc
      rw [Clause.eval, List.any_eq_true]; exact ⟨l, hin, hl⟩      -- c contains the true literal l
  | false =>
      have hnotin : l ∉ c := of_decide_eq_false hlc
      have hmem : (c.erase l.neg) ∈ assign cnf l := by
        simp only [assign, List.mem_map, List.mem_filter]
        exact ⟨c, ⟨hc, by simpa using hnotin⟩, rfl⟩
      exact eval_of_erase v c l.neg (h (c.erase l.neg) hmem)       -- c survives; its erase is satisfied

end Principia
