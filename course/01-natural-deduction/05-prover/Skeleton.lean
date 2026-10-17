import Principia.NatDed.Soundness

/-!
# 05-prover — Your exercises

Run: make lab C=01-natural-deduction/05-prover
See §6 for statements, §7 for hints, and §8 for worked corrections.
Optional exercises have their own skeleton and answer key under optional/.
-/
set_option warningAsError true
open scoped Principia.Form Principia

namespace Principia

/-- GIVEN. Close the goal directly from an assumption. -/
def assumption? (Γ : List Form) (φ : Form) : Option (Γ ⊢ φ) :=
  if h : φ ∈ Γ then some (.ax h) else none

/-- GIVEN. Goal-directed search (introduction rules + assumption), bounded by `fuel`. -/
def prove? : Nat → (Γ : List Form) → (φ : Form) → Option (Γ ⊢ φ)
  | 0, _, _ => none
  | fuel + 1, Γ, φ =>
    match assumption? Γ φ with
    | some d => some d
    | none =>
      match φ with
      | .imp a b => (prove? fuel (a :: Γ) b).map (·.impI)
      | .and a b =>
        match prove? fuel Γ a, prove? fuel Γ b with
        | some da, some db => some (da.andI db)
        | _, _ => none
      | .or a b =>
        match prove? fuel Γ a with
        | some da => some da.orI₁
        | none => (prove? fuel Γ b).map (·.orI₂)
      | _ => none

/-- GIVEN. Top-level search for a closed proof. -/
def prove (φ : Form) : Option ([] ⊢ φ) := prove? (φ.size + 1) [] φ

/-! Your two theorems. -/

theorem prove_sound {Γ : List Form} {φ : Form} {fuel : Nat}
    (h : (prove? fuel Γ φ).isSome = true) : Form.Entails Γ φ := by
  sorry

theorem prove_tautology {φ : Form} (h : (prove φ).isSome = true) : Form.Tautology φ := by
  sorry

end Principia
