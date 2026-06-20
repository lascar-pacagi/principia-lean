import Principia.Logic.Syntax

/-!
# 02-semantics — Skeleton  (THIS IS YOUR FILE)

`eval`, `Tautology`, `Entails`, and the checker `taut?` are GIVEN. Prove the three semantic facts —
replace each `sorry`.

Run:  make lab C=01-natural-deduction/02-semantics
Stuck? See §5 "Prove it" and §6 "Hints for the skeleton" in `explainer.qmd`.
-/
set_option warningAsError true
open scoped Principia.Form

namespace Principia.Form

/-- Truth value of a formula under a valuation `v`. GIVEN. -/
def eval (v : Nat → Bool) : Form → Bool
  | .var n   => v n
  | .fls     => false
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
  | .fls     => 0
  | .imp a b => max (maxVar a) (maxVar b)
  | .and a b => max (maxVar a) (maxVar b)
  | .or a b  => max (maxVar a) (maxVar b)
def allEnvs : Nat → List (Nat → Bool)
  | 0     => [fun _ => false]
  | n + 1 => (allEnvs n).flatMap (fun v => [v, fun k => if k == n then true else v k])
def taut? (φ : Form) : Bool := (allEnvs (maxVar φ)).all (fun v => eval v φ)

/-! Your three facts. -/

-- the value of `∼φ` is the boolean negation of the value of `φ`
theorem eval_neg (v : Nat → Bool) (φ : Form) : eval v (∼φ) = !eval v φ := by
  sorry

-- `φ ⇒ φ` is valid
theorem taut_imp_self (φ : Form) : Tautology (φ ⇒ φ) := by
  sorry

-- excluded middle is valid (it's just a truth table — contrast 04-logic)
theorem taut_em (φ : Form) : Tautology (φ ⋎ ∼φ) := by
  sorry

end Principia.Form
