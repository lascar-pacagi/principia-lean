import Principia.NatDed.Soundness

/-!
# 05-prover — Skeleton  (THIS IS YOUR FILE)

The search (`assumption?`, `prove?`, `prove`) is GIVEN. Prove the two correctness theorems — replace
each `sorry`. The point: because `prove?` returns a *typed* `Deriv`, soundness gives you correctness
almost for free.

Run:  make lab C=01-natural-deduction/05-prover
Stuck? See §5 "Prove it" and §6 "Hints for the skeleton" in `explainer.qmd`.
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

-- If the search succeeds, the formula is entailed. (Read the derivation off the `Option`, then `soundness`.)
theorem prove_sound {Γ : List Form} {φ : Form} {fuel : Nat}
    (h : (prove? fuel Γ φ).isSome) : Form.Entails Γ φ := by
  sorry

-- A successful closed search certifies a tautology.
theorem prove_tautology {φ : Form} (h : (prove φ).isSome) : Form.Tautology φ := by
  sorry

end Principia
