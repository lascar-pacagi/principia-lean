import Principia.Logic.Syntax

/-!
# Principia.Logic.Semantics — truth-value semantics (Course 1, slice 1.2)

A valuation is a function `Nat → Bool` on the atoms. `eval` is the truth table as code; `Tautology` and
`Entails` (`⊨`) are validity and semantic entailment; `taut?` is a runnable decision procedure.
-/
namespace Principia.Form

open scoped Principia.Form

/-- Truth value of a formula under a valuation `v` of the atoms. -/
def eval (v : Nat → Bool) : Form → Bool
  | .var n   => v n
  | .fls     => false
  | .imp a b => (!eval v a) || eval v b
  | .and a b => eval v a && eval v b
  | .or a b  => eval v a || eval v b

/-- `φ` is a tautology: true under *every* valuation. (Semantic `⊨ φ`.) -/
def Tautology (φ : Form) : Prop := ∀ v, eval v φ = true

/-- `Γ ⊨ φ`: every valuation satisfying all of `Γ` also satisfies `φ`. -/
def Entails (Γ : List Form) (φ : Form) : Prop :=
  ∀ v, (∀ ψ ∈ Γ, eval v ψ = true) → eval v φ = true

@[inherit_doc] scoped notation:40 Γ " ⊨ " φ => Entails Γ φ

/-! ### A runnable tautology checker

`eval` only depends on atoms below `maxVar φ`, so checking all `2^(maxVar φ)` valuations decides
tautology-hood. (The formal equivalence `taut? φ = true ↔ Tautology φ` is left to a later slice; here it
is a *runnable* oracle we `#eval`.) -/
def maxVar : Form → Nat
  | .var n   => n + 1
  | .fls     => 0
  | .imp a b => max (maxVar a) (maxVar b)
  | .and a b => max (maxVar a) (maxVar b)
  | .or a b  => max (maxVar a) (maxVar b)

/-- All valuations that differ only on atoms `< n` (others default to `false`). -/
def allEnvs : Nat → List (Nat → Bool)
  | 0     => [fun _ => false]
  | n + 1 => (allEnvs n).flatMap (fun v => [v, fun k => if k == n then true else v k])

/-- Decide tautology-hood by exhausting the (finite) relevant valuations. -/
def taut? (φ : Form) : Bool := (allEnvs (maxVar φ)).all (fun v => eval v φ)

/-! ### Basic semantic facts -/

theorem eval_neg (v : Nat → Bool) (φ : Form) : eval v (∼φ) = !eval v φ := by
  simp [Form.neg, eval]

theorem eval_top (v : Nat → Bool) : eval v Form.top = true := by
  simp [Form.top, Form.neg, eval]

/-- `φ ⇒ φ` is valid. -/
theorem taut_imp_self (φ : Form) : Tautology (φ ⇒ φ) := by
  intro v; simp only [eval]; cases eval v φ <;> rfl

/-- Excluded middle is *semantically* valid (contrast `04-logic`, where `p ∨ ¬p` needed a classical
    axiom to *prove* — here it's just a truth table). -/
theorem taut_em (φ : Form) : Tautology (φ ⋎ ∼φ) := by
  intro v; simp only [eval, Form.neg]; cases eval v φ <;> rfl

end Principia.Form
