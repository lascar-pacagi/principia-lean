import Principia.Resolution.Soundness

/-!
# 03-lrat — Solution  (verified answer key)

`make test` kernel-checks this; `make axioms` audits it. Graduates into `Principia.Sat.Lrat`.
-/
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

-- induction on the proof; each accepted step is a resolvent of two entailed clauses (resolvent_sound).
theorem runProof_preserves {cnf : Cnf} : ∀ (proof : List Step) (db db' : List Clause),
    (∀ c ∈ db, Entailed cnf c) → runProof db proof = some db' → (∀ c ∈ db', Entailed cnf c) := by
  intro proof
  induction proof with
  | nil => intro db db' hinv h; simp only [runProof] at h; injection h with h; subst h; exact hinv
  | cons s rest ih =>
      intro db db' hinv h
      simp only [runProof] at h
      split at h
      · rename_i hcheck
        refine ih (db ++ [s.c]) db' ?_ h
        intro c hc
        rw [List.mem_append] at hc
        cases hc with
        | inl hc => exact hinv c hc
        | inr hc =>
            simp only [List.mem_singleton] at hc; subst hc
            simp only [checkStep] at hcheck
            split at hcheck
            · rename_i ci cj hi hj
              have heq : resolvent ci cj s.lit = s.c := of_decide_eq_true hcheck
              intro v hv
              rw [← heq]
              exact resolvent_sound v ci cj s.lit
                (hinv ci (List.mem_of_getElem? hi) v hv) (hinv cj (List.mem_of_getElem? hj) v hv)
            · exact absurd hcheck (by simp)
      · exact absurd h (by simp)

theorem check_unsat {cnf : Cnf} {proof : List Step} (h : check cnf proof = true) : cnf.Unsat := by
  simp only [check] at h
  split at h
  · rename_i db hrun
    have hempty : ([] : Clause) ∈ db := of_decide_eq_true h
    have hinv : ∀ c ∈ db, Entailed cnf c :=
      runProof_preserves proof cnf db
        (by intro c hc v hv; rw [Cnf.eval, List.all_eq_true] at hv; exact hv c hc) hrun
    intro v
    cases hv : Cnf.eval v cnf with
    | false => rfl
    | true  => have := hinv [] hempty v hv; simp [Clause.eval] at this
  · exact absurd h (by simp)

/-! ## Checks (Tier-2 computational + honesty audit)

A certificate refuting `{p∨q, ¬p, ¬q}`: resolve clauses 0,1 on `+0` → `[+1]` (index 3); then 3,2 on
`+1` → `□`. -/

def egProof : List Step :=
  [ { c := [⟨1,true⟩], i := 0, j := 1, lit := ⟨0,true⟩ },
    { c := [],         i := 3, j := 2, lit := ⟨1,true⟩ } ]

#guard check [[⟨0,true⟩,⟨1,true⟩], [⟨0,false⟩], [⟨1,false⟩]] egProof == true   -- certificate accepted
#guard check [[⟨0,true⟩]] egProof == false                                      -- bogus cert rejected

#print axioms check_unsat

end Principia
