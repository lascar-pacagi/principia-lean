import Principia.Logic.Syntax

/-!
# 02-semantics — Solution  (verified answer key)

`make test` kernel-checks this; `make axioms` audits the keystones. Graduates into
`Principia.Logic.Semantics`. Read to understand *why*, not to copy.
-/
open scoped Principia.Form

namespace Principia.Form

def eval (v : Nat → Bool) : Form → Bool
  | .var n   => v n
  | .fls     => false
  | .imp a b => (!eval v a) || eval v b
  | .and a b => eval v a && eval v b
  | .or a b  => eval v a || eval v b

def Tautology (φ : Form) : Prop := ∀ v, eval v φ = true

def Entails (Γ : List Form) (φ : Form) : Prop :=
  ∀ v, (∀ ψ ∈ Γ, eval v ψ = true) → eval v φ = true

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

-- `∼φ = φ ⇒ ⊥`, and `eval … (imp φ ⊥) = !eval φ || false = !eval φ`. `simp` unfolds and tidies the Bool.
theorem eval_neg (v : Nat → Bool) (φ : Form) : eval v (∼φ) = !eval v φ := by
  simp [Form.neg, eval]

-- unfold to `(!eval v φ || eval v φ) = true`, then a two-row Bool case split closes it.
theorem taut_imp_self (φ : Form) : Tautology (φ ⇒ φ) := by
  intro v; simp only [eval]; cases eval v φ <;> rfl

theorem taut_em (φ : Form) : Tautology (φ ⋎ ∼φ) := by
  intro v; simp only [eval, Form.neg]; cases eval v φ <;> rfl

/-! ## Checks (Tier-2 computational + honesty audit) -/

#eval taut? (Form.var 0 ⇒ Form.var 0)         -- ⇒ true
#guard taut? (Form.var 0 ⇒ Form.var 0) == true
#guard taut? (Form.var 0) == false             -- a bare atom is not a tautology
#guard taut? (Form.var 0 ⋎ ∼Form.var 0) == true

#print axioms eval_neg
#print axioms taut_imp_self
#print axioms taut_em

end Principia.Form
