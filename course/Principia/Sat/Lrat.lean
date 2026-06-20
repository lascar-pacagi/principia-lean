import Principia.Resolution.Soundness

/-!
# Principia.Sat.Lrat — a verified UNSAT-certificate checker (Course 3, slice 3.6; the keystone)

The trustworthy-UNSAT pattern: don't verify a fast solver — have it emit a **certificate** and check
that with a small *verified* checker. Here a certificate is a flat, hint-carrying resolution proof (the
core of the LRAT format): each line names two earlier database clauses and a literal, and claims their
resolvent. `check` replays the lines against a growing database (starting from the input clauses) and
confirms the empty clause `□` was derived.

**`check_unsat`**: if `check` accepts, the CNF is unsatisfiable. The proof maintains the invariant that
every database clause is *entailed* by the input — true initially, preserved by each step via Course 2's
`resolvent_sound` — so deriving `□` (entailed, but satisfiable by nobody) forces unsatisfiability. This
mirrors Lean core's own `Std.Tactic.BVDecide.LRAT.check_sound` (behind `bv_decide`); real LRAT hints
encode reverse-unit-propagation chains rather than single resolutions, but the soundness skeleton is the
same.
-/
namespace Principia

/-- One proof line: clause `c` is claimed to be the resolvent of database clauses `i` and `j` on `lit`. -/
structure Step where
  c   : Clause
  i   : Nat
  j   : Nat
  lit : Lit

/-- Validate a line: the two referenced clauses exist and resolve (on `lit`) to exactly `c`. -/
def checkStep (db : List Clause) (s : Step) : Bool :=
  match db[s.i]?, db[s.j]? with
  | some ci, some cj => decide (resolvent ci cj s.lit = s.c)
  | _, _ => false

/-- Replay the certificate, appending each validated clause to the database; `none` on a bad line. -/
def runProof : List Clause → List Step → Option (List Clause)
  | db, [] => some db
  | db, s :: rest => if checkStep db s then runProof (db ++ [s.c]) rest else none

/-- The checker: replay from the input clauses, then confirm `□` is in the final database. -/
def check (cnf : Cnf) (proof : List Step) : Bool :=
  match runProof cnf proof with
  | some db => decide (([] : Clause) ∈ db)
  | none    => false

/-- `c` is a logical consequence of `cnf`. -/
def Entailed (cnf : Cnf) (c : Clause) : Prop := ∀ v, Cnf.eval v cnf = true → Clause.eval v c = true

/-- Replaying preserves the invariant "every database clause is entailed by `cnf`". -/
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

/-- **Checker soundness.** If `check` accepts the certificate, the CNF is unsatisfiable. -/
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
    | true  => have := hinv [] hempty v hv; simp [Clause.eval] at this   -- `□` entailed yet false: absurd
  · exact absurd h (by simp)

end Principia
