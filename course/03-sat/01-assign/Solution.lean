import Principia.Resolution.Rule

/-!
# 01-assign — Solution  (verified answer key)

`make test` kernel-checks this; `make axioms` audits it. Graduates into `Principia.Sat.Basic`.
-/
namespace Principia

def assign (cnf : Cnf) (l : Lit) : Cnf :=
  (cnf.filter (fun c => decide (l ∉ c))).map (fun c => c.erase l.neg)

theorem eval_of_erase (v) (c : Clause) (x : Lit) (h : Clause.eval v (c.erase x) = true) :
    Clause.eval v c = true := by
  rw [Clause.eval, List.any_eq_true] at h ⊢
  obtain ⟨lit, hmem, hlit⟩ := h
  exact ⟨lit, List.mem_of_mem_erase hmem, hlit⟩

theorem sat_of_assign (v) (cnf : Cnf) (l : Lit) (hl : l.eval v = true)
    (h : Cnf.eval v (assign cnf l) = true) : Cnf.eval v cnf = true := by
  rw [Cnf.eval, List.all_eq_true] at h ⊢
  intro c hc
  cases hlc : decide (l ∈ c) with
  | true =>
      have hin : l ∈ c := of_decide_eq_true hlc
      rw [Clause.eval, List.any_eq_true]; exact ⟨l, hin, hl⟩
  | false =>
      have hnotin : l ∉ c := of_decide_eq_false hlc
      have hmem : (c.erase l.neg) ∈ assign cnf l := by
        simp only [assign, List.mem_map, List.mem_filter]
        exact ⟨c, ⟨hc, by simpa using hnotin⟩, rfl⟩
      exact eval_of_erase v c l.neg (h (c.erase l.neg) hmem)

/-! ## Checks (Tier-2 computational + honesty audit) -/

#eval assign [[⟨0,true⟩, ⟨1,true⟩], [⟨0,false⟩], [⟨2,true⟩]] ⟨0,true⟩   -- ⇒ [[], [+2]]
#guard assign [[⟨0,true⟩]] ⟨0,true⟩ == ([] : Cnf)                        -- {p} | p=true ⇒ no clauses (SAT)
#guard assign [[⟨0,false⟩]] ⟨0,true⟩ == [([] : Clause)]                   -- {¬p} | p=true ⇒ □ (UNSAT here)

#print axioms sat_of_assign

end Principia
