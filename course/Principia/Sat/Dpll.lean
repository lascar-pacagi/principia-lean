import Principia.Sat.Basic

/-!
# Principia.Sat.Dpll — the DPLL solver, and model soundness (Course 3, slices 3.2–3.3)

`dpll` is the classic Davis–Putnam–Logemann–Loveland search: no clauses ⇒ satisfiable (`[]`); the empty
clause `□` present ⇒ this branch is unsatisfiable; otherwise pick a literal and branch on `assign cnf l` /
`assign cnf l.neg`, recording the chosen literal. Bounded by `fuel`.

**Model soundness** (`dpll_sound`): the list of literals the solver returns *satisfies* every clause
(`Cnf.satBy`). The engine is `satBy_of_assign` — committing to `l` and then satisfying the simplified CNF
gives satisfaction of the original (the `Cnf.satBy` analogue of `sat_of_assign`, needing no
consistency/congruence because `satBy` is monotone in the literal list).
-/
namespace Principia

/-- DPLL: search for a satisfying list of literals. -/
def dpll : Nat → Cnf → Option (List Lit)
  | 0, _ => none
  | _, [] => some []                                   -- no clauses: satisfiable
  | fuel + 1, cnf =>
    if ([] : Clause) ∈ cnf then none                   -- □ present: unsatisfiable on this branch
    else
      match cnf with
      | (l :: _) :: _ =>                               -- pick the first literal and branch
        match dpll fuel (assign cnf l) with
        | some ls => some (l :: ls)
        | none    => (dpll fuel (assign cnf l.neg)).map (fun ls => l.neg :: ls)
      | _ => none

/-- A clause is satisfied by a literal list if it contains one of them. -/
def Clause.satBy (ls : List Lit) (c : Clause) : Bool := c.any (fun lit => decide (lit ∈ ls))
/-- A clause set is satisfied by a literal list if every clause is. -/
def Cnf.satBy (ls : List Lit) (cnf : Cnf) : Bool := cnf.all (Clause.satBy ls)

/-- Committing to `l` lifts `satBy`: a list satisfying `assign cnf l` is extended by `l` to satisfy `cnf`. -/
theorem satBy_of_assign (ls : List Lit) (cnf : Cnf) (l : Lit)
    (h : Cnf.satBy ls (assign cnf l) = true) : Cnf.satBy (l :: ls) cnf = true := by
  rw [Cnf.satBy, List.all_eq_true] at h ⊢
  intro c hc
  cases hlc : decide (l ∈ c) with
  | true =>
      rw [Clause.satBy, List.any_eq_true]; exact ⟨l, of_decide_eq_true hlc, by simp⟩
  | false =>
      have hnotin : l ∉ c := of_decide_eq_false hlc
      have hmem : (c.erase l.neg) ∈ assign cnf l := by
        simp only [assign, List.mem_map, List.mem_filter]; exact ⟨c, ⟨hc, by simpa using hnotin⟩, rfl⟩
      have hsat := h (c.erase l.neg) hmem
      rw [Clause.satBy, List.any_eq_true] at hsat; rw [Clause.satBy, List.any_eq_true]
      obtain ⟨lit, hlitmem, hlitin⟩ := hsat
      refine ⟨lit, List.mem_of_mem_erase hlitmem, ?_⟩
      simp only [decide_eq_true_eq] at hlitin ⊢; exact List.mem_cons_of_mem _ hlitin

/-- **Model soundness.** Whatever literal list DPLL returns satisfies the clause set. -/
theorem dpll_sound : ∀ (fuel : Nat) (cnf : Cnf) (ls : List Lit),
    dpll fuel cnf = some ls → Cnf.satBy ls cnf = true := by
  intro fuel
  induction fuel with
  | zero => intro cnf ls h; simp [dpll] at h
  | succ k ih =>
      intro cnf ls h
      cases cnf with
      | nil => simp_all [dpll, Cnf.satBy]
      | cons c cs =>
          cases c with
          | nil => simp only [dpll] at h; split at h <;> simp_all
          | cons l c' =>
              simp only [dpll] at h
              split at h
              · simp at h
              · split at h
                · rename_i ls' heq
                  injection h with h; subst h
                  exact satBy_of_assign ls' ((l :: c') :: cs) l (ih _ _ heq)
                · rename_i heq
                  rw [Option.map_eq_some_iff] at h
                  obtain ⟨ls'', hls'', hmap⟩ := h; subst hmap
                  exact satBy_of_assign ls'' ((l :: c') :: cs) l.neg (ih _ _ hls'')

end Principia
