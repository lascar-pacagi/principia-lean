import Principia.Resolution.Prover
import Principia.Resolution.Soundness
import Principia.NatDed.Completeness

/-!
# 05-completeness — Solution  (verified answer key)

`make test` kernel-checks this; `make axioms` audits it. Graduates into `Principia.Resolution.Completeness`.
Read to understand *why*, not to copy.
-/
open scoped Principia.Form

namespace Principia

theorem refute?_unsat {S : Cnf} {fuel : Nat} (h : (refute? S fuel).isSome) : S.Unsat := by
  cases hp : refute? S fuel with
  | none   => rw [hp] at h; simp at h
  | some d => exact refut_unsat d

theorem prove_taut_by_resolution {φ : Form} {fuel : Nat}
    (h : (refute? (toCnf false φ) fuel).isSome) : Form.Tautology φ := by
  cases hp : refute? (toCnf false φ) fuel with
  | none   => rw [hp] at h; simp at h
  | some d => exact taut_of_refut d

theorem refutable_to_provable {φ : Form} (d : Refut (toCnf false φ) []) : Nonempty ([] ⊢ φ) :=
  Form.provable_iff_tautology.mpr (taut_of_refut d)

/-! ## Checks (Tier-1 + honesty audit) -/

-- a verified resolution-based tautology prover, running automatically:
example : Form.Tautology (Form.var 0 ⇒ Form.var 0) := prove_taut_by_resolution (fuel := 4) (by decide)

-- it even dispatches Peirce's law (which the slice-1.5 ND search could not find!):
example : Form.Tautology (((Form.var 0 ⇒ Form.var 1) ⇒ Form.var 0) ⇒ Form.var 0) :=
  prove_taut_by_resolution (fuel := 8) (by decide)

#print axioms prove_taut_by_resolution
#print axioms refutable_to_provable

end Principia
