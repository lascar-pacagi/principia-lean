import Principia.Logic.Semantics

/-!
# Principia.Resolution.Cnf — clauses, CNF, and conversion (Course 2, slice 2.1)

Resolution works on **clause sets**. A `Lit`eral is a variable with a polarity; a `Clause` is a
disjunction of literals (a `List Lit`); a `Cnf` is a conjunction of clauses (a `List Clause`). The empty
clause `[]` is unsatisfiable (`□`); the empty clause set `[]` is trivially true.

`toCnf` converts a `Form` to an equivalent clause set (with a polarity flag that pushes negations to the
leaves), and `toCnf_eval` proves the conversion preserves truth. The payoff is the bridge to refutation:
`Tautology φ ↔ (toCnf false φ).Unsat` — *φ is valid iff the clauses of ¬φ are unsatisfiable*.
-/
namespace Principia

open scoped Principia.Form

/-- A literal: variable `var` with polarity `pol` (`true` = positive). -/
structure Lit where
  var : Nat
  pol : Bool
deriving DecidableEq, Repr

/-- A clause is a disjunction of literals. -/
abbrev Clause := List Lit
/-- A CNF is a conjunction of clauses. -/
abbrev Cnf := List Clause

def Lit.eval (v : Nat → Bool) (l : Lit) : Bool := if l.pol then v l.var else !(v l.var)
/-- A clause is true when *some* literal is. (Empty clause `□` is false — unsatisfiable.) -/
def Clause.eval (v : Nat → Bool) (c : Clause) : Bool := c.any (Lit.eval v)
/-- A clause set is true when *every* clause is. (Empty set is true.) -/
def Cnf.eval (v : Nat → Bool) (s : Cnf) : Bool := s.all (Clause.eval v)

def Cnf.Sat (s : Cnf) : Prop := ∃ v, Cnf.eval v s = true
def Cnf.Unsat (s : Cnf) : Prop := ∀ v, Cnf.eval v s = false

/-! ### List/Bool plumbing -/

theorem cnf_eval_cons (v) (c) (s : Cnf) : Cnf.eval v (c :: s) = (Clause.eval v c && Cnf.eval v s) := by
  simp [Cnf.eval]
theorem clause_eval_append (v) (c1 c2 : Clause) :
    Clause.eval v (c1 ++ c2) = (Clause.eval v c1 || Clause.eval v c2) := by
  simp [Clause.eval, List.any_append]
theorem cnf_eval_append (v) (s1 s2 : Cnf) :
    Cnf.eval v (s1 ++ s2) = (Cnf.eval v s1 && Cnf.eval v s2) := by
  simp [Cnf.eval, List.all_append]

/-- Distribute `∨` over the conjunctions: `distribute s1 s2` is the CNF of `s1 ∨ s2`. -/
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

/-- Distribution computes the disjunction of the two clause sets. -/
theorem distribute_eval (v) (s1 s2 : Cnf) :
    Cnf.eval v (distribute s1 s2) = (Cnf.eval v s1 || Cnf.eval v s2) := by
  induction s1 with
  | nil => simp [distribute, Cnf.eval]
  | cons c1 s1' ih =>
      rw [distribute_cons, cnf_eval_append, map_cons_eval, ih, cnf_eval_cons]
      cases Clause.eval v c1 <;> cases Cnf.eval v s1' <;> cases Cnf.eval v s2 <;> rfl

/-! ### Conversion

`toCnf b φ` is a clause set for `φ` (when `b = true`) or for `∼φ` (when `b = false`); the flag carries
negation down to the literals (so `¬` never appears as a connective in the output). -/
def toCnf : Bool → Form → Cnf
  | b, .var n   => [[{var := n, pol := b}]]
  | b, .fls     => if b then [[]] else []
  | b, .and a c => if b then toCnf true a ++ toCnf true c else distribute (toCnf false a) (toCnf false c)
  | b, .or a c  => if b then distribute (toCnf true a) (toCnf true c) else toCnf false a ++ toCnf false c
  | b, .imp a c => if b then distribute (toCnf false a) (toCnf true c) else toCnf true a ++ toCnf false c

/-- The conversion preserves truth: `toCnf true φ` evaluates like `φ`, `toCnf false φ` like `∼φ`. -/
theorem toCnf_eval (v : Nat → Bool) : ∀ (b : Bool) (φ : Form),
    Cnf.eval v (toCnf b φ) = (if b then Form.eval v φ else !Form.eval v φ) := by
  intro b φ
  induction φ generalizing b with
  | var n => cases b <;> simp [toCnf, Cnf.eval, Clause.eval, Lit.eval, Form.eval]
  | fls => cases b <;> simp [toCnf, Cnf.eval, Clause.eval, Form.eval]
  | and a c iha ihc =>
      cases b <;> simp [toCnf, distribute_eval, cnf_eval_append, iha, ihc, Form.eval] <;>
        (cases Form.eval v a <;> cases Form.eval v c <;> rfl)
  | or a c iha ihc =>
      cases b <;> simp [toCnf, distribute_eval, cnf_eval_append, iha, ihc, Form.eval] <;>
        (cases Form.eval v a <;> cases Form.eval v c <;> rfl)
  | imp a c iha ihc =>
      cases b <;> simp [toCnf, distribute_eval, cnf_eval_append, iha, ihc, Form.eval] <;>
        (cases Form.eval v a <;> cases Form.eval v c <;> rfl)

/-- **The bridge to refutation.** `φ` is valid iff the clauses of `∼φ` are unsatisfiable — so to *prove*
    `φ`, it suffices to *refute* `toCnf false φ`. -/
theorem taut_iff_cnf_unsat (φ : Form) : Form.Tautology φ ↔ (toCnf false φ).Unsat := by
  constructor
  · intro h v; rw [toCnf_eval]; simp [h v]
  · intro h v; have hv := h v; rw [toCnf_eval] at hv; simp at hv; exact hv

end Principia
