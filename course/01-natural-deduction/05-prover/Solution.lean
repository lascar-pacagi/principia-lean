import Principia.NatDed.Soundness

/-!
# 05-prover — Solution  (verified answer key)

`make test` kernel-checks this; `make axioms` audits it. Graduates into `Principia.NatDed.Prover`.
Read to understand *why*, not to copy.
-/
open scoped Principia.Form Principia

namespace Principia

def assumption? (Γ : List Form) (φ : Form) : Option (Γ ⊢ φ) :=
  if h : φ ∈ Γ then some (.ax h) else none

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

def prove (φ : Form) : Option ([] ⊢ φ) := prove? (φ.size + 1) [] φ

-- The `none` branch is impossible (it contradicts `h`); the `some d` branch hands us a real derivation,
-- and `soundness` turns it into the entailment. The type was the certificate all along.
theorem prove_sound {Γ : List Form} {φ : Form} {fuel : Nat}
    (h : (prove? fuel Γ φ).isSome) : Form.Entails Γ φ := by
  cases hp : prove? fuel Γ φ with
  | none   => rw [hp] at h; simp at h
  | some d => exact Form.soundness d

theorem prove_tautology {φ : Form} (h : (prove φ).isSome) : Form.Tautology φ := by
  cases hp : prove φ with
  | none   => rw [hp] at h; simp at h
  | some d => exact Form.tautology_of_proof d

/-! ## Checks (Tier-2 computational + honesty audit) -/

-- the prover finds proofs of intro-shaped goals…
#guard (prove (Form.var 0 ⇒ Form.var 0)).isSome == true
#guard (prove (Form.var 0 ⇒ Form.var 1 ⇒ Form.var 0)).isSome == true                 -- K
#guard (prove (Form.var 0 ⇒ Form.var 1 ⇒ (Form.var 0 ⋏ Form.var 1))).isSome == true
-- …and honestly gives up where elimination is needed (even though the formula IS valid):
#guard (prove ((Form.var 0 ⋏ Form.var 1) ⇒ Form.var 0)).isSome == false
#guard Form.taut? ((Form.var 0 ⋏ Form.var 1) ⇒ Form.var 0) == true   -- valid, yet the prover missed it

-- the headline: the prover DECIDES and CERTIFIES a tautology automatically (no hand-built tree!)
example : Form.Tautology (Form.var 0 ⇒ Form.var 0) := prove_tautology (by decide)

#print axioms prove_sound
#print axioms prove_tautology

end Principia
