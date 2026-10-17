import Principia.FirstOrder.SkolemSemantics

set_option warningAsError true

namespace Principia.FirstOrder

/-- A universally satisfied compiled matrix recovers the original quantified formula.
The prefix fixes only previously allocated variables; fresh ones remain arbitrary. -/
theorem skolemize_recover {D : Type} (a : Nnf) :
    ∀ (M : Model D) (ρ : Nat → Term) (U : List Nat) (f v : Nat) (σ₀ : Nat → D),
    a.functionBound ≤ f → SubstitutionBound a ρ f → Covered a ρ U →
    (∀ i ∈ U, i < v) →
    (∀ σ, (∀ i, i < v → σ i = σ₀ i) → (skolemize ρ U a f v).matrix.evaluate M σ) →
    Translated M ρ a σ₀ := by
  classical
  induction a with
  | literal l =>
    intro M ρ U f v σ₀ ha hρ hc hu ht
    exact (Literal.evaluate_substitute M σ₀ ρ l).mp (ht σ₀ (fun _ _ => rfl))
  | verum => intro M ρ U f v σ₀ ha hρ hc hu ht; trivial
  | falsum => intro M ρ U f v σ₀ ha hρ hc hu ht; exact ht σ₀ (fun _ _ => rfl)
  | conjunction a b iha ihb =>
    intro M ρ U f v σ₀ ha hρ hc hu ht
    have hfa : a.functionBound ≤ f := Nat.le_trans (Nat.le_max_left ..) ha
    have hfb : b.functionBound ≤ f := Nat.le_trans (Nat.le_max_right ..) ha
    have hra : SubstitutionBound a ρ f := fun i hi => hρ i (List.mem_append_left _ hi)
    have hrb : SubstitutionBound b ρ f := fun i hi => hρ i (List.mem_append_right _ hi)
    have hca : Covered a ρ U := fun i hi => hc i (List.mem_append_left _ hi)
    have hcb : Covered b ρ U := fun i hi => hc i (List.mem_append_right _ hi)
    have bounds := skolemize_bounds a ρ U f v hfa hra hca hu
    constructor
    · exact iha M ρ U f v σ₀ hfa hra hca hu (fun σ h => (ht σ h).1)
    · exact ihb M ρ U _ _ σ₀ (Nat.le_trans hfb bounds.functions)
        (fun i hi => Nat.le_trans (hrb i hi) bounds.functions) hcb
        (fun i hi => Nat.lt_of_lt_of_le (hu i hi) bounds.variables)
        (fun σ h => (ht σ (fun i hi => h i (Nat.lt_of_lt_of_le hi bounds.variables))).2)
  | disjunction a b iha ihb =>
    intro M ρ U f v σ₀ ha hρ hc hu ht
    have hfa : a.functionBound ≤ f := Nat.le_trans (Nat.le_max_left ..) ha
    have hfb : b.functionBound ≤ f := Nat.le_trans (Nat.le_max_right ..) ha
    have hra : SubstitutionBound a ρ f := fun i hi => hρ i (List.mem_append_left _ hi)
    have hrb : SubstitutionBound b ρ f := fun i hi => hρ i (List.mem_append_right _ hi)
    have hca : Covered a ρ U := fun i hi => hc i (List.mem_append_left _ hi)
    have hcb : Covered b ρ U := fun i hi => hc i (List.mem_append_right _ hi)
    have bounds := skolemize_bounds a ρ U f v hfa hra hca hu
    by_cases left : Translated M ρ a σ₀
    · exact Or.inl left
    · have counter : ∃ τ, (∀ i, i < v → τ i = σ₀ i) ∧
          ¬(skolemize ρ U a f v).matrix.evaluate M τ := by
        apply Classical.byContradiction
        intro hn
        apply left
        apply iha M ρ U f v σ₀ hfa hra hca hu
        intro τ hτ
        apply Classical.byContradiction
        intro hfalse
        exact hn ⟨τ, hτ, hfalse⟩
      obtain ⟨τ, same, leftFalse⟩ := counter
      have right : Translated M ρ b τ := by
        apply ihb M ρ U _ _ τ (Nat.le_trans hfb bounds.functions)
          (fun i hi => Nat.le_trans (hrb i hi) bounds.functions) hcb
          (fun i hi => Nat.lt_of_lt_of_le (hu i hi) bounds.variables)
        intro σ hσ
        have whole := ht σ (fun i hi =>
          (hσ i (Nat.lt_of_lt_of_le hi bounds.variables)).trans (same i hi))
        apply whole.resolve_left
        intro hl
        exact leftFalse ((Matrix.evaluate_congr M _ σ τ
          (fun i hi => hσ i (bounds.matrixVariables i hi))).mp hl)
      exact Or.inr ((depends_translated M ρ b hcb τ σ₀
        (fun i hi => same i (hu i hi))).mp right)
  | universal body ih =>
    intro M ρ U f v σ₀ ha hρ hc hu ht x
    let τ := updateEnvironment σ₀ v x
    have hu' : ∀ i ∈ U ++ [v], i < v+1 := by
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact Nat.lt_succ_of_lt (hu i hi)
      · simp only [List.mem_singleton] at hi; subst i; omega
    have instanceTruth := ih M (extend (.variable v) ρ) (U ++ [v]) f (v+1) τ ha
      (bound_universal hρ) (covered_universal hc) hu' (by
        intro σ hσ
        apply ht σ
        intro i hi
        have he := hσ i (by omega)
        simpa [τ, updateEnvironment, show i ≠ v by omega] using he)
    change body.evaluate M (fun i => (extend (.variable v) ρ i).evaluate M τ) at instanceTruth
    rw [evaluate_extended_substitution] at instanceTruth
    have value : Term.evaluate M τ (.variable v) = x := by simp [Term.evaluate, τ, updateEnvironment]
    rw [value] at instanceTruth
    apply (body_congr M body _ _ x ?_).mp instanceTruth
    intro i hi
    apply Term.evaluate_congr
    intro j hj
    have hjv := hu j (hc i hi j hj)
    simp [τ, updateEnvironment, show j ≠ v by omega]
  | existential body ih =>
    intro M ρ U f v σ₀ ha hρ hc hu ht
    let term := Term.function f (U.map Term.variable)
    have instanceTruth := ih M (extend term ρ) U (f+1) v σ₀ (Nat.le_succ_of_le ha)
      (bound_existential hρ) (covered_existential hc) hu ht
    change body.evaluate M (fun i => (extend term ρ i).evaluate M σ₀) at instanceTruth
    rw [evaluate_extended_substitution] at instanceTruth
    exact ⟨term.evaluate M σ₀, instanceTruth⟩

end Principia.FirstOrder
