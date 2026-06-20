import Principia.Resolution.Prover
import Principia.Resolution.Soundness
import Principia.NatDed.Completeness

/-!
# Principia.Resolution.Completeness — the verified decision direction, and the tie to Course 1
# (Course 2, slice 2.5)

Resolution **soundness** (2.4) makes the prover's *yes* meaningful, and this module cashes that out:
* `refute?_unsat` — if the saturation prover finds `□`, the clause set is unsatisfiable;
* `prove_taut_by_resolution` — refuting the clauses of `∼φ` certifies `φ` is a tautology (a verified,
  resolution-based tautology prover — it even dispatches Peirce's law automatically);
* `refutable_to_provable` — a resolution refutation of `∼φ` yields a natural-deduction proof of `φ`,
  closing the achievable half of the tie to Course 1.

**Flagged hard keystone (not proved here).** Full *refutation-completeness* — `S.Unsat → Refut S []`,
that *every* unsatisfiable set has a refutation — is research-grade with our `List`-based clauses (it
needs set-like clause handling — permutation/subsumption — plus a restriction-and-lifting or
semantic-tree induction over the variables). We treat it as the marked stretch (cf. FOL completeness);
see the lesson's study and `references/` (FFL-Foundation) for a full account. Note Course 1's natural-
deduction prover *does* have full completeness (`provable_iff_tautology`), so the project's
proof-and-validity coincidence is established there.
-/
namespace Principia

open scoped Principia.Form

/-- If the saturation prover succeeds, the clause set is genuinely unsatisfiable (soundness, applied to
    whatever refutation the search returned). -/
theorem refute?_unsat {S : Cnf} {fuel : Nat} (h : (refute? S fuel).isSome) : S.Unsat := by
  cases hp : refute? S fuel with
  | none   => rw [hp] at h; simp at h
  | some d => exact refut_unsat d

/-- **A verified resolution tautology-prover.** If resolution refutes the clauses of `∼φ`, then `φ` is
    valid. (`by decide` on a concrete `φ` runs the search and certifies the result.) -/
theorem prove_taut_by_resolution {φ : Form} {fuel : Nat}
    (h : (refute? (toCnf false φ) fuel).isSome) : Form.Tautology φ := by
  cases hp : refute? (toCnf false φ) fuel with
  | none   => rw [hp] at h; simp at h
  | some d => exact taut_of_refut d

/-- The achievable half of the tie to Course 1: a resolution refutation of `∼φ` yields a
    natural-deduction proof of `φ`. (The converse needs refutation-completeness — the flagged keystone.) -/
theorem refutable_to_provable {φ : Form} (d : Refut (toCnf false φ) []) : Nonempty ([] ⊢ φ) :=
  Form.provable_iff_tautology.mpr (taut_of_refut d)

end Principia
