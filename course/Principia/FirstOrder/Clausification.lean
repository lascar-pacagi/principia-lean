import Principia.FirstOrder.SkolemCorrectness
import Principia.FirstOrder.NaturalDeductionCompleteness
import Principia.FirstOrder.ResolutionCompleteness

/-!
# Certified first-order clausification and resolution frontend

The actual NNF/Skolem/CNF compiler is equisatisfiable with the input, including free variables.
A refutation of the counterexample clauses therefore certifies the original entailment.
The executable frontend runs resolution once; no independent ND search is needed.
-/
namespace Principia.FirstOrder

theorem contextFormula_correct {D : Type} (M : Model D) (ρ : Nat → D) (Γ : List Formula) :
    (contextFormula Γ).evaluate M ρ ↔ Satisfies M ρ Γ := by
  induction Γ with
  | nil => simp [contextFormula, Formula.negation, Formula.evaluate, Satisfies]
  | cons a rest ih =>
    simp [contextFormula, Formula.evaluate, ih, Satisfies, List.mem_cons]

theorem counterexampleFormula_correct {D : Type} (M : Model D) (ρ : Nat → D)
    (Γ : List Formula) (goal : Formula) :
    (counterexampleFormula Γ goal).evaluate M ρ ↔
      Satisfies M ρ Γ ∧ ¬goal.evaluate M ρ :=
  and_congr (contextFormula_correct M ρ Γ) Iff.rfl

theorem entails_iff_no_countermodel (Γ : List Formula) (goal : Formula) :
    Formula.Entails Γ goal ↔ ¬(counterexampleFormula Γ goal).Satisfiable := by
  constructor
  · intro h ⟨D, inhabited, M, ρ, hc⟩
    have pair := (counterexampleFormula_correct M ρ Γ goal).mp hc
    exact pair.2 (h D inhabited M ρ pair.1)
  · intro h D inhabited M ρ hΓ
    apply Classical.byContradiction
    intro negative
    exact h ⟨D, inhabited, M, ρ,
      (counterexampleFormula_correct M ρ Γ goal).mpr ⟨hΓ, negative⟩⟩

/-- Original-goal soundness uses model expansion and resolution soundness alone. -/
theorem clausal_refutation_sound {Γ : List Formula} {goal : Formula}
    (proof : ResolutionDerivation (clausify (counterexampleFormula Γ goal)).clauses []) :
    Formula.Entails Γ goal := by
  intro D inhabited M ρ assumptions
  apply Classical.byContradiction
  intro negative
  have counterexample := (counterexampleFormula_correct M ρ Γ goal).mpr ⟨assumptions, negative⟩
  obtain ⟨expanded, _, satisfied⟩ := clausify_model_expansion inhabited M ρ
    (counterexampleFormula Γ goal) counterexample
  exact refutation_unsatisfiable proof D inhabited expanded satisfied

/-- Full semantic bridge: arbitrary first-order entailment is equivalent to existence of a
finite resolution refutation of the AUTOMATICALLY generated counterexample clauses. -/
theorem entails_iff_clausal_refutation (Γ : List Formula) (goal : Formula) :
    Formula.Entails Γ goal ↔
      Nonempty (ResolutionDerivation (clausify (counterexampleFormula Γ goal)).clauses []) := by
  rw [resolution_iff_unsatisfiable, clausify_unsatisfiable]
  exact entails_iff_no_countermodel Γ goal

theorem deduction_iff_clausal_refutation (Γ : List Formula) (goal : Formula) :
    Nonempty (Derivation Γ goal) ↔
      Nonempty (ResolutionDerivation (clausify (counterexampleFormula Γ goal)).clauses []) :=
  (deduction_iff_entails Γ goal).trans (entails_iff_clausal_refutation Γ goal)

/-- The returned computational certificate is the clause refutation. Its interpretation
as a proof of the original goal follows from the verified conversion and resolution. -/
structure ClausalProof (Γ : List Formula) (goal : Formula) where
  refutation : ResolutionDerivation (clausify (counterexampleFormula Γ goal)).clauses []

theorem ClausalProof.sound {Γ : List Formula} {goal : Formula} (proof : ClausalProof Γ goal) :
    Formula.Entails Γ goal := clausal_refutation_sound proof.refutation

/-- Optional mathematical view, extracted noncomputably using ND completeness.
It is not a second executable search and is not stored in the returned certificate. -/
noncomputable def ClausalProof.derivation {Γ : List Formula} {goal : Formula}
    (proof : ClausalProof Γ goal) : Derivation Γ goal :=
  Classical.choice (deduction_complete proof.sound)

def proveViaClauses (rounds unificationFuel : Nat)
    (Γ : List Formula) (goal : Formula) : Option (ClausalProof Γ goal) :=
  (refuteFirstOrder rounds unificationFuel (clausify (counterexampleFormula Γ goal)).clauses).map
    (fun refutation => ⟨refutation⟩)

theorem proveViaClauses_sound {rounds unificationFuel : Nat}
    {Γ : List Formula} {goal : Formula}
    (h : (proveViaClauses rounds unificationFuel Γ goal).isSome = true) :
    Formula.Entails Γ goal := by
  cases hs : proveViaClauses rounds unificationFuel Γ goal with
  | none => simp [hs] at h
  | some proof => exact proof.sound

end Principia.FirstOrder
