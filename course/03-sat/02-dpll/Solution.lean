import Principia.Sat.Basic

/-!
# 02-dpll — Solution  (verified answer key)

`make test` kernel-checks this; `make axioms` audits it. Graduates into `Principia.Sat.Dpll`.
-/
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

-- mirror of `sat_of_assign`: split on whether `l ∈ c`; if so `l` (now in `l :: ls`) satisfies it;
-- otherwise the kept clause's erase is satisfied, and the witness survives both the erase and the cons.
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

-- induction on fuel, following the solver's branches; each `assign` recursion is lifted by satBy_of_assign.
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

/-! ## Checks (Tier-2 computational + honesty audit) -/

#eval dpll 10 [[⟨0,true⟩, ⟨1,true⟩], [⟨0,false⟩]]                  -- SAT → a model
#guard (dpll 10 [[⟨0,true⟩, ⟨1,true⟩], [⟨0,false⟩], [⟨1,false⟩]]).isNone   -- UNSAT
#guard (dpll 10 [[⟨0,true⟩], [⟨0,false⟩]]).isNone                  -- UNSAT
-- soundness in action: the model DPLL returns really satisfies the clause set
#guard match dpll 10 [[⟨0,true⟩, ⟨1,true⟩], [⟨0,false⟩]] with
       | some ls => Cnf.satBy ls [[⟨0,true⟩, ⟨1,true⟩], [⟨0,false⟩]]
       | none => false

#print axioms dpll_sound

end Principia
