import Principia.NatDed.Completeness

/-!
# 07-complete-solver — Your exercises

Run: make lab C=01-natural-deduction/07-complete-solver
See §6 for statements, §7 for hints, and §8 for worked corrections.
Optional exercises have their own skeleton and answer key under optional/.
-/
set_option warningAsError true
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
def solve (φ : Form) : SolveResult φ := by
  sorry

/-- A returned derivation establishes validity. -/
theorem solve_sound {φ : Form} (h : (solve φ).isValid = true) : Form.Tautology φ := by
  sorry

/-- The algorithm succeeds on every tautology. -/
theorem solve_complete {φ : Form} (h : Form.Tautology φ) : (solve φ).isValid = true := by
  sorry

/-- The Boolean observation agrees exactly with semantic validity. -/
theorem solve_iff (φ : Form) : (solve φ).isValid = true ↔ Form.Tautology φ :=
  ⟨solve_sound, solve_complete⟩

/-- A negative result means there is no derivation, rather than that search gave up. -/
theorem solve_invalid_iff (φ : Form) :
    (solve φ).isValid = false ↔ ¬Nonempty ([] ⊢ φ) := by
  sorry

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
