import Principia.Logic.Syntax

/-!
# 02-semantics — Your exercises

Run: make lab C=01-natural-deduction/02-semantics
See §6 for statements, §7 for hints, and §8 for worked corrections.
Optional exercises have their own skeleton and answer key under optional/.
-/
set_option warningAsError true
open scoped Principia.Form

namespace Principia.Form

/-- Truth value of a formula under a valuation `v`. GIVEN. -/
def eval (v : Nat → Bool) : Form → Bool
  | .var n   => v n
  | .falsum  => false
  | .imp a b => (!eval v a) || eval v b
  | .and a b => eval v a && eval v b
  | .or a b  => eval v a || eval v b

/-- `φ` is a tautology: true under every valuation. GIVEN. -/
def Tautology (φ : Form) : Prop := ∀ v, eval v φ = true

/-- `Γ ⊨ φ`: every valuation satisfying all of `Γ` satisfies `φ`. GIVEN. -/
def Entails (Γ : List Form) (φ : Form) : Prop :=
  ∀ v, (∀ ψ ∈ Γ, eval v ψ = true) → eval v φ = true

/-- A runnable truth-table checker (GIVEN; we `#eval` it below). -/
def maxVar : Form → Nat
  | .var n   => n + 1
  | .falsum     => 0
  | .imp a b => max (maxVar a) (maxVar b)
  | .and a b => max (maxVar a) (maxVar b)
  | .or a b  => max (maxVar a) (maxVar b)
def allEnvs : Nat → List (Nat → Bool)
  | 0     => [fun _ => false]
  | n + 1 => (allEnvs n).flatMap (fun v => [v, fun k => if k == n then true else v k])
def taut? (φ : Form) : Bool := (allEnvs (maxVar φ)).all (fun v => eval v φ)

/-! Your first three facts. -/

theorem eval_neg (v : Nat → Bool) (φ : Form) : eval v (∼φ) = !eval v φ := by
  rw [neg, eval, eval]
  simp


theorem taut_imp_self (φ : Form) : Tautology (φ ⇒ φ) := by
  rw [Tautology]
  intro v
  rw [eval]
  simp

theorem taut_excluded_middle (φ : Form) : Tautology (φ ⋎ ∼φ) := by
  rw [Tautology]
  intro v
  rw [neg, eval, eval, eval]
  simp

/-! Final exercise: implement a transformation, then prove its meaning. -/

/-- Reverse every atom's Boolean value. GIVEN. -/
def flipValuation (v : Nat → Bool) : Nat → Bool := fun i => !(v i)

/-- Build the Boolean dual. See §6 for all five transformation rules.
Replace `:= sorry` with equations beginning with `|`, as in `eval` above. -/
def dual : Form → Form
  | .var i => .var i
  | .falsum => Form.top
  | .imp a b => .and (Form.neg (dual a)) (dual b)
  | .and a b => .or (dual a) (dual b)
  | .or a b => .and (dual a) (dual b)

/-- Relate the transformed formula to the original under the flipped valuation. -/
theorem eval_dual (v : Nat → Bool) (φ : Form) :
    eval v (dual φ) = !eval (flipValuation v) φ := by
  induction φ with
  | var i => rw [dual, eval, eval, flipValuation]; simp
  | falsum =>
    rw [dual, top, neg, eval, eval]
    simp
  | imp a b iha ihb =>
    rw [dual, neg, eval, eval, eval, iha, ihb, eval]
    simp
  | and a b iha ihb =>
    rw [dual, eval, eval, iha, ihb]
    simp
  | or a b iha ihb =>
    rw [dual, eval, eval, iha, ihb]
    simp


end Principia.Form
