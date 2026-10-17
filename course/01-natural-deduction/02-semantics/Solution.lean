import Principia.Logic.Syntax

/-!
# 02-semantics — Solution  (verified answer key)

`make test` kernel-checks this; `make axioms` audits the keystones. Graduates into
`Principia.Logic.Semantics`. Read to understand *why*, not to copy.
-/
set_option warningAsError true

open scoped Principia.Form

namespace Principia.Form

def eval (v : Nat → Bool) : Form → Bool
  | .var n   => v n
  | .falsum     => false
  | .imp a b => (!eval v a) || eval v b
  | .and a b => eval v a && eval v b
  | .or a b  => eval v a || eval v b

def Tautology (φ : Form) : Prop := ∀ v, eval v φ = true

def Entails (Γ : List Form) (φ : Form) : Prop :=
  ∀ v, (∀ ψ ∈ Γ, eval v ψ = true) → eval v φ = true

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

-- `∼φ = φ ⇒ ⊥`, and `eval … (imp φ ⊥) = !eval φ || false = !eval φ`. `simp` unfolds and tidies the Bool.
theorem eval_neg (v : Nat → Bool) (φ : Form) : eval v (∼φ) = !eval v φ := by
  simp [Form.neg, eval]

-- unfold to `(!eval v φ || eval v φ) = true`, then a two-row Bool case split closes it.
theorem taut_imp_self (φ : Form) : Tautology (φ ⇒ φ) := by
  intro v; simp only [eval]; cases eval v φ <;> rfl

theorem taut_excluded_middle (φ : Form) : Tautology (φ ⋎ ∼φ) := by
  intro v; simp only [eval, Form.neg]; cases eval v φ <;> rfl

/-- Reverse every atom's Boolean value. GIVEN. -/
def flipValuation (v : Nat → Bool) : Nat → Bool := fun i => !(v i)

def dual : Form → Form
  | .var i => .var i
  | .falsum => Form.top
  | .imp a b => ∼(dual a) ⋏ dual b
  | .and a b => dual a ⋎ dual b
  | .or a b => dual a ⋏ dual b

theorem eval_dual (v : Nat → Bool) (φ : Form) :
    eval v (dual φ) = !eval (flipValuation v) φ := by
  induction φ with
  | var i => simp [dual, eval, flipValuation]
  | falsum => rfl
  | imp a b ihA ihB =>
    simp only [dual, Form.neg, eval]
    rw [ihA, ihB]
    cases eval (flipValuation v) a <;> cases eval (flipValuation v) b <;> rfl
  | and a b ihA ihB =>
    simp only [dual, eval]
    rw [ihA, ihB]
    cases eval (flipValuation v) a <;> cases eval (flipValuation v) b <;> rfl
  | or a b ihA ihB =>
    simp only [dual, eval]
    rw [ihA, ihB]
    cases eval (flipValuation v) a <;> cases eval (flipValuation v) b <;> rfl

/-! ## Checks (Tier-2 computational + honesty audit) -/

#eval taut? (Form.var 0 ⇒ Form.var 0)         -- ⇒ true
#guard taut? (Form.var 0 ⇒ Form.var 0) == true
#guard taut? (Form.var 0) == false             -- a bare atom is not a tautology
#guard taut? (Form.var 0 ⋎ ∼Form.var 0) == true

-- Shape checks include every constructor, including the implication case.
#guard dual (Form.var 0) = Form.var 0
#guard dual Form.falsum = Form.top
#guard dual (Form.var 0 ⋏ Form.var 1) = (Form.var 0 ⋎ Form.var 1)
#guard dual (Form.var 0 ⋎ Form.var 1) = (Form.var 0 ⋏ Form.var 1)
#guard dual (Form.var 0 ⇒ Form.var 1) = (∼Form.var 0 ⋏ Form.var 1)
#guard dual ((Form.var 0 ⇒ Form.var 1) ⋎ Form.falsum) =
  ((∼Form.var 0 ⋏ Form.var 1) ⋏ Form.top)

#eval eval (fun _ => true) (dual (Form.var 0 ⋎ Form.var 1)) -- true
#guard eval (fun _ => true) (dual (Form.var 0 ⋎ Form.var 1)) = true
#guard eval (flipValuation (fun _ => true)) (Form.var 0 ⋎ Form.var 1) = false

#print axioms dual
#print axioms eval_dual
#print axioms eval_neg
#print axioms taut_imp_self
#print axioms taut_excluded_middle

end Principia.Form
