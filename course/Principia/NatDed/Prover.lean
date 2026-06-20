import Principia.NatDed.Soundness

/-!
# Principia.NatDed.Prover — a proof search (Course 1, slice 1.5)

A goal-directed search that returns a **typed derivation** `Γ ⊢ φ`. Because the result *is* a `Deriv`,
anything the prover returns is correct *by construction* — no separate soundness proof for the prover
itself; the type is the certificate, and `prove_sound` just reads it off via `soundness`.

The search applies the *introduction* rules driven by the goal's shape, plus the assumption rule, bounded
by `fuel`. It is intentionally **incomplete** (it does no elimination and no classical `raa` search): its
"yes" is always right, but a "no" only means *this* search gave up. Completeness — every valid formula
*has* a derivation — is slice 1.6.
-/
namespace Principia

open scoped Principia.Form Principia

/-- Close the goal directly from an assumption (`φ ∈ Γ` is decidable since `Form` has `DecidableEq`). -/
def assumption? (Γ : List Form) (φ : Form) : Option (Γ ⊢ φ) :=
  if h : φ ∈ Γ then some (.ax h) else none

/-- Goal-directed proof search (introduction rules + assumption), bounded by `fuel`. -/
def prove? : Nat → (Γ : List Form) → (φ : Form) → Option (Γ ⊢ φ)
  | 0, _, _ => none
  | fuel + 1, Γ, φ =>
    match assumption? Γ φ with
    | some d => some d
    | none =>
      match φ with
      | .imp a b => (prove? fuel (a :: Γ) b).map (·.impI)           -- assume a, prove b
      | .and a b =>                                                  -- prove both conjuncts
        match prove? fuel Γ a, prove? fuel Γ b with
        | some da, some db => some (da.andI db)
        | _, _ => none
      | .or a b =>                                                   -- try the left disjunct, else right
        match prove? fuel Γ a with
        | some da => some da.orI₁
        | none => (prove? fuel Γ b).map (·.orI₂)
      | _ => none

/-- Top-level: search for a closed proof of `φ` (fuel scaled to the formula's size). -/
def prove (φ : Form) : Option ([] ⊢ φ) := prove? (φ.size + 1) [] φ

/-- **The prover is sound by construction.** If the search succeeds, the formula is entailed. -/
theorem prove_sound {Γ : List Form} {φ : Form} {fuel : Nat}
    (h : (prove? fuel Γ φ).isSome) : Form.Entails Γ φ := by
  cases hp : prove? fuel Γ φ with
  | none   => rw [hp] at h; simp at h
  | some d => exact Form.soundness d

/-- A successful closed search certifies a tautology. -/
theorem prove_tautology {φ : Form} (h : (prove φ).isSome) : Form.Tautology φ := by
  cases hp : prove φ with
  | none   => rw [hp] at h; simp at h
  | some d => exact Form.tautology_of_proof d

end Principia
