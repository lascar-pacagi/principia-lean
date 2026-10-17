import Principia.FirstOrder.SkolemSemantics

set_option warningAsError true

namespace Principia.FirstOrder

/-- Uniform model expansion. A precondition may depend on the enclosing universals only;
newly allocated universal variables are unconstrained. This handles disjunction without
incorrectly exchanging a universal quantifier with a varying branch choice. -/
theorem skolemize_expand {D : Type} (inhabited : Nonempty D) (a : Nnf) :
    ∀ (M : Model D) (ρ : Nat → Term) (U : List Nat) (f v : Nat)
      (P : (Nat → D) → Prop),
    a.functionBound ≤ f → SubstitutionBound a ρ f → Covered a ρ U →
    (∀ i ∈ U, i < v) → DependsOn P U →
    (∀ σ, P σ → Translated M ρ a σ) →
    ∃ N : Model D, AgreeBelow M N f ∧
      ∀ σ, P σ → (skolemize ρ U a f v).matrix.evaluate N σ := by
  classical
  induction a with
  | literal l =>
    intro M ρ U f v P ha hρ hc hu hp ht
    exact ⟨M, AgreeBelow.refl M f, fun σ h =>
      (Literal.evaluate_substitute M σ ρ l).mpr (ht σ h)⟩
  | verum =>
    intro M ρ U f v P ha hρ hc hu hp ht
    exact ⟨M, AgreeBelow.refl M f, fun _ _ => True.intro⟩
  | falsum =>
    intro M ρ U f v P ha hρ hc hu hp ht
    exact ⟨M, AgreeBelow.refl M f, ht⟩
  | conjunction a b iha ihb =>
    intro M ρ U f v P ha hρ hc hu hp ht
    have hfa : a.functionBound ≤ f := Nat.le_trans (Nat.le_max_left ..) ha
    have hfb : b.functionBound ≤ f := Nat.le_trans (Nat.le_max_right ..) ha
    have hra : SubstitutionBound a ρ f := fun i hi => hρ i (List.mem_append_left _ hi)
    have hrb : SubstitutionBound b ρ f := fun i hi => hρ i (List.mem_append_right _ hi)
    have hca : Covered a ρ U := fun i hi => hc i (List.mem_append_left _ hi)
    have hcb : Covered b ρ U := fun i hi => hc i (List.mem_append_right _ hi)
    have bounds := skolemize_bounds a ρ U f v hfa hra hca hu
    obtain ⟨N, old, left⟩ := iha M ρ U f v P hfa hra hca hu hp (fun σ h => (ht σ h).1)
    obtain ⟨Q, newer, right⟩ := ihb N ρ U _ _ P (Nat.le_trans hfb bounds.functions)
      (fun i hi => Nat.le_trans (hrb i hi) bounds.functions) hcb
      (fun i hi => Nat.lt_of_lt_of_le (hu i hi) bounds.variables) hp
      (fun σ h => (translated_agree old b ρ σ hfb hrb).mp (ht σ h).2)
    refine ⟨Q, old.trans (newer.mono bounds.functions), ?_⟩
    intro σ h
    exact ⟨(Matrix.evaluate_agree newer _ bounds.matrixFunctions σ).mp (left σ h), right σ h⟩
  | disjunction a b iha ihb =>
    intro M ρ U f v P ha hρ hc hu hp ht
    have hfa : a.functionBound ≤ f := Nat.le_trans (Nat.le_max_left ..) ha
    have hfb : b.functionBound ≤ f := Nat.le_trans (Nat.le_max_right ..) ha
    have hra : SubstitutionBound a ρ f := fun i hi => hρ i (List.mem_append_left _ hi)
    have hrb : SubstitutionBound b ρ f := fun i hi => hρ i (List.mem_append_right _ hi)
    have hca : Covered a ρ U := fun i hi => hc i (List.mem_append_left _ hi)
    have hcb : Covered b ρ U := fun i hi => hc i (List.mem_append_right _ hi)
    have bounds := skolemize_bounds a ρ U f v hfa hra hca hu
    let PL := fun σ => P σ ∧ Translated M ρ a σ
    let PR := fun σ => P σ ∧ ¬Translated M ρ a σ
    have hPL : DependsOn PL U := fun σ τ he =>
      and_congr (hp σ τ he) (depends_translated M ρ a hca σ τ he)
    have hPR : DependsOn PR U := fun σ τ he =>
      and_congr (hp σ τ he) (not_congr (depends_translated M ρ a hca σ τ he))
    obtain ⟨N, old, left⟩ := iha M ρ U f v PL hfa hra hca hu hPL (fun _ h => h.2)
    obtain ⟨Q, newer, right⟩ := ihb N ρ U _ _ PR (Nat.le_trans hfb bounds.functions)
      (fun i hi => Nat.le_trans (hrb i hi) bounds.functions) hcb
      (fun i hi => Nat.lt_of_lt_of_le (hu i hi) bounds.variables) hPR
      (fun σ h => (translated_agree old b ρ σ hfb hrb).mp ((ht σ h.1).resolve_left h.2))
    refine ⟨Q, old.trans (newer.mono bounds.functions), ?_⟩
    intro σ h
    by_cases hl : Translated M ρ a σ
    · exact Or.inl ((Matrix.evaluate_agree newer _ bounds.matrixFunctions σ).mp (left σ ⟨h, hl⟩))
    · exact Or.inr (right σ ⟨h, hl⟩)
  | universal body ih =>
    intro M ρ U f v P ha hρ hc hu hp ht
    have hu' : ∀ i ∈ U ++ [v], i < v+1 := by
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact Nat.lt_succ_of_lt (hu i hi)
      · simp only [List.mem_singleton] at hi; subst i; omega
    have hp' : DependsOn P (U ++ [v]) :=
      fun σ τ he => hp σ τ (fun i hi => he i (List.mem_append_left _ hi))
    apply ih M (extend (.variable v) ρ) (U ++ [v]) f (v+1) P ha
      (bound_universal hρ) (covered_universal hc) hu' hp'
    intro σ h
    change body.evaluate M (fun i => (extend (.variable v) ρ i).evaluate M σ)
    rw [evaluate_extended_substitution]
    simpa only [Term.evaluate] using ht σ h (σ v)
  | existential body ih =>
    intro M ρ U f v P ha hρ hc hu hp ht
    let g := witnessFunction inhabited M body ρ U
    let N := replaceFunction M f g
    let term := Term.function f (U.map Term.variable)
    have old : AgreeBelow M N f := replaceFunction_agrees M f g
    have instances : ∀ σ, P σ → Translated N (extend term ρ) body σ := by
      intro σ h
      have witness := witnessFunction_spec inhabited M body ρ U hc σ (ht σ h)
      have witness' := (Nnf.evaluate_agree old body ha _).mp witness
      change body.evaluate N (fun i => (extend term ρ i).evaluate N σ)
      rw [evaluate_extended_substitution]
      have value : term.evaluate N σ = g (U.map σ) := by
        rw [evaluate_function_variables]
        simp [N, replaceFunction]
      rw [value]
      apply (body_congr N body _ _ _ ?_).mp witness'
      intro i hi
      exact Term.evaluate_agree old (ρ i) (hρ i hi) σ
    obtain ⟨Q, newer, result⟩ := ih N (extend term ρ) U (f+1) v P
      (Nat.le_succ_of_le ha) (bound_existential hρ) (covered_existential hc) hu hp instances
    exact ⟨Q, old.trans (newer.mono (Nat.le_succ f)), result⟩

end Principia.FirstOrder
