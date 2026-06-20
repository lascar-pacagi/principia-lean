import Principia.Logic.Semantics

/-!
# 01-cnf — Skeleton  (THIS IS YOUR FILE)

The structures, semantics, plumbing lemmas, `distribute` (with `distribute_eval`), and `toCnf` are GIVEN.
Prove `toCnf_eval` (the conversion preserves truth) and `taut_iff_cnf_unsat` (the bridge).

Run:  make lab C=02-resolution/01-cnf
Stuck? See §5 "Prove it" and §6 "Hints for the skeleton" in `explainer.qmd`.
-/
set_option warningAsError true
open scoped Principia.Form

namespace Principia

structure Lit where
  var : Nat
  pol : Bool
deriving DecidableEq, Repr
abbrev Clause := List Lit
abbrev Cnf := List Clause

def Lit.eval (v : Nat → Bool) (l : Lit) : Bool := if l.pol then v l.var else !(v l.var)
def Clause.eval (v : Nat → Bool) (c : Clause) : Bool := c.any (Lit.eval v)
def Cnf.eval (v : Nat → Bool) (s : Cnf) : Bool := s.all (Clause.eval v)
def Cnf.Unsat (s : Cnf) : Prop := ∀ v, Cnf.eval v s = false

theorem cnf_eval_cons (v) (c) (s : Cnf) : Cnf.eval v (c :: s) = (Clause.eval v c && Cnf.eval v s) := by
  simp [Cnf.eval]
theorem clause_eval_append (v) (c1 c2 : Clause) :
    Clause.eval v (c1 ++ c2) = (Clause.eval v c1 || Clause.eval v c2) := by simp [Clause.eval, List.any_append]
theorem cnf_eval_append (v) (s1 s2 : Cnf) :
    Cnf.eval v (s1 ++ s2) = (Cnf.eval v s1 && Cnf.eval v s2) := by simp [Cnf.eval, List.all_append]
def distribute (s1 s2 : Cnf) : Cnf := s1.flatMap (fun c1 => s2.map (fun c2 => c1 ++ c2))
theorem distribute_cons (c1) (s1' s2 : Cnf) :
    distribute (c1 :: s1') s2 = (s2.map (fun c2 => c1 ++ c2)) ++ distribute s1' s2 := by
  simp [distribute, List.flatMap_cons]
theorem map_cons_eval (v) (c1 : Clause) (s2 : Cnf) :
    Cnf.eval v (s2.map (fun c2 => c1 ++ c2)) = (Clause.eval v c1 || Cnf.eval v s2) := by
  induction s2 with
  | nil => simp [Cnf.eval]
  | cons c2 s2' ih =>
      rw [List.map_cons, cnf_eval_cons, clause_eval_append, ih, cnf_eval_cons]
      cases Clause.eval v c1 <;> simp
theorem distribute_eval (v) (s1 s2 : Cnf) :
    Cnf.eval v (distribute s1 s2) = (Cnf.eval v s1 || Cnf.eval v s2) := by
  induction s1 with
  | nil => simp [distribute, Cnf.eval]
  | cons c1 s1' ih =>
      rw [distribute_cons, cnf_eval_append, map_cons_eval, ih, cnf_eval_cons]
      cases Clause.eval v c1 <;> cases Cnf.eval v s1' <;> cases Cnf.eval v s2 <;> rfl

def toCnf : Bool → Form → Cnf
  | b, .var n   => [[{var := n, pol := b}]]
  | b, .fls     => if b then [[]] else []
  | b, .and a c => if b then toCnf true a ++ toCnf true c else distribute (toCnf false a) (toCnf false c)
  | b, .or a c  => if b then distribute (toCnf true a) (toCnf true c) else toCnf false a ++ toCnf false c
  | b, .imp a c => if b then distribute (toCnf false a) (toCnf true c) else toCnf true a ++ toCnf false c

/-! Your two theorems. -/

-- the conversion preserves truth (induct on φ, generalizing the polarity flag `b`)
theorem toCnf_eval (v : Nat → Bool) : ∀ (b : Bool) (φ : Form),
    Cnf.eval v (toCnf b φ) = (if b then Form.eval v φ else !Form.eval v φ) := by
  sorry

-- the bridge: φ is valid  ↔  the clauses of ∼φ are unsatisfiable
theorem taut_iff_cnf_unsat (φ : Form) : Form.Tautology φ ↔ (toCnf false φ).Unsat := by
  sorry

end Principia
