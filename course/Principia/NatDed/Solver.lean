import Principia.NatDed.Completeness

/-!
# A total, complete propositional solver

The finite truth table decides validity. On a positive result, the executable Kalmár construction
builds a natural-deduction derivation. On a negative result, the solver certifies invalidity.
Every recursion is structural: on formulas, finite lists, or the variable bound. There is no fuel,
partial definition, external oracle, or noncomputable proof extraction.
-/
namespace Principia
open scoped Principia.Form Principia

/-- A positive result carries a derivation; a negative result certifies semantic invalidity. -/
inductive SolveResult (φ : Form) where
  | valid : ([] ⊢ φ) → SolveResult φ
  | invalid : (¬Form.Tautology φ) → SolveResult φ

/-- Project a result to a Boolean for display and computational checks. -/
def SolveResult.isValid {φ : Form} : SolveResult φ → Bool
  | .valid _ => true
  | .invalid _ => false

/-- Exhaustive, certified decision procedure for closed propositional validity. -/
def solve (φ : Form) : SolveResult φ :=
  if h : Form.taut? φ = true then
    .valid (Form.completeness ((Form.taut?_eq_true_iff φ).mp h))
  else
    .invalid (fun ht => h ((Form.taut?_eq_true_iff φ).mpr ht))

/-- A returned derivation establishes validity. -/
theorem solve_sound {φ : Form} (h : (solve φ).isValid = true) : Form.Tautology φ := by
  cases hs : solve φ with
  | valid d => exact Form.tautology_of_proof d
  | invalid hn => simp [hs, SolveResult.isValid] at h

/-- The algorithm succeeds on every tautology. -/
theorem solve_complete {φ : Form} (h : Form.Tautology φ) : (solve φ).isValid = true := by
  simp [solve, (Form.taut?_eq_true_iff φ).mpr h, SolveResult.isValid]

/-- The Boolean observation agrees exactly with semantic validity. -/
theorem solve_iff (φ : Form) : (solve φ).isValid = true ↔ Form.Tautology φ :=
  ⟨solve_sound, solve_complete⟩

/-- A negative result means there is no derivation, rather than that search gave up. -/
theorem solve_invalid_iff (φ : Form) :
    (solve φ).isValid = false ↔ ¬Nonempty ([] ⊢ φ) := by
  constructor
  · intro h ⟨d⟩
    have ht := solve_complete (Form.tautology_of_proof d)
    rw [h] at ht
    contradiction
  · intro hn
    cases hs : solve φ with
    | valid d => exact False.elim (hn ⟨d⟩)
    | invalid h => rfl

/-- Option-valued interface, retaining the actual derivation on success. -/
def proveComplete (φ : Form) : Option ([] ⊢ φ) :=
  match solve φ with
  | .valid d => some d
  | .invalid _ => none

theorem proveComplete_iff (φ : Form) :
    (proveComplete φ).isSome = true ↔ Form.Tautology φ := by
  have he : (proveComplete φ).isSome = (solve φ).isValid := by
    unfold proveComplete
    cases solve φ <;> rfl
  rw [he]
  exact solve_iff φ

end Principia

namespace Principia
/-- Count rule applications, making an actual generated certificate observable. -/
def Deriv.nodeCount : {Γ : List Form} → {φ : Form} → Deriv Γ φ → Nat
  | _, _, .ax _ => 1
  | _, _, .impI d => 1 + d.nodeCount
  | _, _, .impE d e => 1 + d.nodeCount + e.nodeCount
  | _, _, .andI d e => 1 + d.nodeCount + e.nodeCount
  | _, _, .andE₁ d => 1 + d.nodeCount
  | _, _, .andE₂ d => 1 + d.nodeCount
  | _, _, .orI₁ d => 1 + d.nodeCount
  | _, _, .orI₂ d => 1 + d.nodeCount
  | _, _, .orE d e f => 1 + d.nodeCount + e.nodeCount + f.nodeCount
  | _, _, .flsE d => 1 + d.nodeCount
  | _, _, .raa d => 1 + d.nodeCount
end Principia
