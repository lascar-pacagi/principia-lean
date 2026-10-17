import Principia.FirstOrder.SkolemLemmas
set_option warningAsError true

namespace Principia.FirstOrder

theorem Term.functionBound_substitute (t : Term) (ρ : Nat → Term) (f : Nat)
    (ht : t.functionBound ≤ f) (hρ : ∀ i ∈ t.support, (ρ i).functionBound ≤ f) :
    (t.substitute ρ).functionBound ≤ f := by
  cases t with
  | «variable» i => simpa [substitute] using hρ i (by simp [support])
  | function g args =>
    simp only [substitute, functionBound, List.map_map]
    simp only [functionBound] at ht
    apply fold_max_le (Nat.le_trans (fold_max_initial _ _) ht)
    intro n hn
    obtain ⟨a, ha, he⟩ := List.mem_map.mp hn
    subst n
    apply Term.functionBound_substitute a ρ f
    · exact Nat.le_trans (fold_max_member _ (List.mem_map.mpr ⟨a, ha, rfl⟩)) ht
    · intro i hi
      exact hρ i (by simpa only [support] using
        List.mem_flatten.mpr ⟨a.support, List.mem_map.mpr ⟨a, ha, rfl⟩, hi⟩)
termination_by sizeOf t
decreasing_by
  have hs := List.sizeOf_lt_of_mem ha
  simp_all only [Term.function.sizeOf_spec]
  omega

theorem Term.support_substitute (t : Term) (ρ : Nat → Term) (P : Nat → Prop)
    (hρ : ∀ i ∈ t.support, ∀ j ∈ (ρ i).support, P j) :
    ∀ j ∈ (t.substitute ρ).support, P j := by
  cases t with
  | «variable» i => simpa only [substitute] using hρ i (by simp [support])
  | function g args =>
    intro j hj
    simp only [substitute, support, List.map_map] at hj
    obtain ⟨xs, hxs, hj⟩ := List.mem_flatten.mp hj
    obtain ⟨a, ha, he⟩ := List.mem_map.mp hxs
    subst xs
    apply Term.support_substitute a ρ P _ j hj
    intro i hi k hk
    exact hρ i (by simpa only [support] using
      List.mem_flatten.mpr ⟨a.support, List.mem_map.mpr ⟨a, ha, rfl⟩, hi⟩) k hk
termination_by sizeOf t
decreasing_by
  have hs := List.sizeOf_lt_of_mem ha
  simp_all only [Term.function.sizeOf_spec]
  omega

theorem literal_bound_substitute (l : Literal) (ρ : Nat → Term) (f : Nat)
    (ht : literalFunctionBound l ≤ f)
    (hρ : ∀ i ∈ literalSupport l, (ρ i).functionBound ≤ f) :
    literalFunctionBound (l.substitute ρ) ≤ f := by
  apply fold_max_le (Nat.zero_le _)
  intro n hn
  obtain ⟨t, ht', he⟩ := List.mem_map.mp hn
  obtain ⟨a, ha, ha'⟩ := List.mem_map.mp ht'
  subst t
  subst n
  apply Term.functionBound_substitute a ρ f
  · exact Nat.le_trans (fold_max_member _ (List.mem_map.mpr ⟨a, ha, rfl⟩)) ht
  · exact fun i hi => hρ i (List.mem_flatten.mpr
      ⟨a.support, List.mem_map.mpr ⟨a, ha, rfl⟩, hi⟩)

theorem literal_support_substitute (l : Literal) (ρ : Nat → Term) (P : Nat → Prop)
    (hρ : ∀ i ∈ literalSupport l, ∀ j ∈ (ρ i).support, P j) :
    ∀ j ∈ literalSupport (l.substitute ρ), P j := by
  intro j hj
  obtain ⟨xs, hxs, hj⟩ := List.mem_flatten.mp hj
  obtain ⟨t, ht, he⟩ := List.mem_map.mp hxs
  obtain ⟨a, ha, ha'⟩ := List.mem_map.mp ht
  subst xs
  subst t
  apply Term.support_substitute a ρ P _ j hj
  exact fun i hi => hρ i (List.mem_flatten.mpr
    ⟨a.support, List.mem_map.mpr ⟨a, ha, rfl⟩, hi⟩)

theorem skolem_term_bound (f : Nat) (U : List Nat) :
    (Term.function f (U.map Term.variable)).functionBound ≤ f+1 := by
  simp only [Term.functionBound]
  apply fold_max_le (Nat.le_refl _)
  intro n hn
  obtain ⟨t, ht, he⟩ := List.mem_map.mp hn
  obtain ⟨i, hi, he'⟩ := List.mem_map.mp ht
  subst t
  subst n
  simp [Term.functionBound]

theorem skolem_term_support (f : Nat) (U : List Nat) :
    (Term.function f (U.map Term.variable)).support = U := by
  simp only [Term.support, List.map_map, Function.comp_def]
  induction U with
  | nil => rfl
  | cons a rest ih => simpa [Term.support] using congrArg (a :: ·) ih

/-- Every variable used by a translated free reference is one of the enclosing universals. -/
def Covered (a : Nnf) (ρ : Nat → Term) (U : List Nat) : Prop :=
  ∀ i ∈ a.support, ∀ j ∈ (ρ i).support, j ∈ U

def SubstitutionBound (a : Nnf) (ρ : Nat → Term) (f : Nat) : Prop :=
  ∀ i ∈ a.support, (ρ i).functionBound ≤ f

structure SkolemBounds (f v : Nat) (result : SkolemResult) : Prop where
  functions : f ≤ result.nextFunction
  variables : v ≤ result.nextVariable
  matrixFunctions : result.matrix.functionBound ≤ result.nextFunction
  matrixVariables : ∀ i ∈ result.matrix.support, i < result.nextVariable

theorem skolemize_bounds (a : Nnf) : ∀ (ρ : Nat → Term) (U : List Nat) (f v : Nat),
    a.functionBound ≤ f → SubstitutionBound a ρ f → Covered a ρ U →
    (∀ i ∈ U, i < v) → SkolemBounds f v (skolemize ρ U a f v) := by
  induction a with
  | literal l =>
    intro ρ U f v ha hρ hc hu
    exact ⟨Nat.le_refl _, Nat.le_refl _, literal_bound_substitute l ρ f ha hρ,
      literal_support_substitute l ρ (· < v) (fun i hi j hj => hu j (hc i hi j hj))⟩
  | verum => intro ρ U f v ha hρ hc hu; exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.zero_le _, by simp [skolemize, Matrix.support]⟩
  | falsum => intro ρ U f v ha hρ hc hu; exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.zero_le _, by simp [skolemize, Matrix.support]⟩
  | conjunction a b iha ihb =>
    intro ρ U f v ha hρ hc hu
    have left := iha ρ U f v (Nat.le_trans (Nat.le_max_left ..) ha)
      (fun i hi => hρ i (List.mem_append_left _ hi))
      (fun i hi => hc i (List.mem_append_left _ hi)) hu
    have right := ihb ρ U _ _ (Nat.le_trans (Nat.le_trans (Nat.le_max_right ..) ha) left.functions)
      (fun i hi => Nat.le_trans (hρ i (List.mem_append_right _ hi)) left.functions)
      (fun i hi => hc i (List.mem_append_right _ hi))
      (fun i hi => Nat.lt_of_lt_of_le (hu i hi) left.variables)
    exact ⟨Nat.le_trans left.functions right.functions, Nat.le_trans left.variables right.variables,
      Nat.max_le.mpr ⟨Nat.le_trans left.matrixFunctions right.functions, right.matrixFunctions⟩,
      fun i hi => (List.mem_append.mp hi).elim
        (fun hi => Nat.lt_of_lt_of_le (left.matrixVariables i hi) right.variables)
        (right.matrixVariables i)⟩
  | disjunction a b iha ihb =>
    intro ρ U f v ha hρ hc hu
    have left := iha ρ U f v (Nat.le_trans (Nat.le_max_left ..) ha)
      (fun i hi => hρ i (List.mem_append_left _ hi))
      (fun i hi => hc i (List.mem_append_left _ hi)) hu
    have right := ihb ρ U _ _ (Nat.le_trans (Nat.le_trans (Nat.le_max_right ..) ha) left.functions)
      (fun i hi => Nat.le_trans (hρ i (List.mem_append_right _ hi)) left.functions)
      (fun i hi => hc i (List.mem_append_right _ hi))
      (fun i hi => Nat.lt_of_lt_of_le (hu i hi) left.variables)
    exact ⟨Nat.le_trans left.functions right.functions, Nat.le_trans left.variables right.variables,
      Nat.max_le.mpr ⟨Nat.le_trans left.matrixFunctions right.functions, right.matrixFunctions⟩,
      fun i hi => (List.mem_append.mp hi).elim
        (fun hi => Nat.lt_of_lt_of_le (left.matrixVariables i hi) right.variables)
        (right.matrixVariables i)⟩
  | universal body ih =>
    intro ρ U f v ha hρ hc hu
    have bounds := ih (extend (.variable v) ρ) (U ++ [v]) f (v+1) ha
      (by
        intro i hi
        cases i with
        | zero => simp [extend, Term.functionBound]
        | succ i => exact hρ i (List.mem_filterMap.mpr ⟨i+1, hi, rfl⟩))
      (by
        intro i hi j hj
        cases i with
        | zero => exact List.mem_append_right _ (by simpa [extend, Term.support] using hj)
        | succ i => exact List.mem_append_left _ (hc i (List.mem_filterMap.mpr ⟨i+1, hi, rfl⟩) j hj))
      (by intro i hi; rcases List.mem_append.mp hi with hi | hi
          · exact Nat.lt_succ_of_lt (hu i hi)
          · simp only [List.mem_singleton] at hi; subst i; omega)
    exact ⟨bounds.functions, Nat.le_trans (by omega) bounds.variables,
      bounds.matrixFunctions, bounds.matrixVariables⟩
  | existential body ih =>
    intro ρ U f v ha hρ hc hu
    let term := Term.function f (U.map Term.variable)
    have bounds := ih (extend term ρ) U (f+1) v (Nat.le_succ_of_le ha)
      (by
        intro i hi
        cases i with
        | zero => exact skolem_term_bound f U
        | succ i => exact Nat.le_succ_of_le (hρ i (List.mem_filterMap.mpr ⟨i+1, hi, rfl⟩)))
      (by
        intro i hi j hj
        cases i with
        | zero => simpa only [extend, term, skolem_term_support] using hj
        | succ i => exact hc i (List.mem_filterMap.mpr ⟨i+1, hi, rfl⟩) j hj) hu
    exact ⟨Nat.le_trans (by omega) bounds.functions, bounds.variables,
      bounds.matrixFunctions, bounds.matrixVariables⟩
end Principia.FirstOrder
