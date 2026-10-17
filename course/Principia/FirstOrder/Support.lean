import Principia.FirstOrder.Semantics

namespace Principia.FirstOrder

def Term.support : Term → List Nat
  | .variable i => [i]
  | .function _ args => (args.map Term.support).flatten

def lowerSupport (xs : List Nat) : List Nat := xs.filterMap fun
  | 0 => none
  | i+1 => some i

def Formula.support : Formula → List Nat
  | .predicate _ args => (args.map Term.support).flatten
  | .falsum => []
  | .implies a b | .conjunction a b | .disjunction a b => a.support ++ b.support
  | .universal a | .existential a => lowerSupport a.support

def updateEnvironment {D : Type} (ρ : Nat → D) (n : Nat) (x : D) : Nat → D :=
  fun i => if i = n then x else ρ i

theorem Term.evaluate_congr {D : Type} (M : Model D) (t : Term) (ρ σ : Nat → D)
    (h : ∀ i ∈ t.support, ρ i = σ i) : t.evaluate M ρ = t.evaluate M σ := by
  cases t with
  | «variable» i => simpa only [evaluate] using h i (by simp [support])
  | function f args =>
    simp only [support] at h
    simp only [evaluate]
    congr 1
    apply List.map_congr_left
    intro a ha
    apply Term.evaluate_congr M a ρ σ
    intro i hi
    exact h i (List.mem_flatten.mpr ⟨a.support, List.mem_map.mpr ⟨a, ha, rfl⟩, hi⟩)
termination_by sizeOf t
decreasing_by
  have hs := List.sizeOf_lt_of_mem ha
  simp_all only [Term.function.sizeOf_spec]
  omega

theorem Formula.evaluate_congr {D : Type} (M : Model D) : ∀ (a : Formula) (ρ σ : Nat → D),
    (∀ i ∈ a.support, ρ i = σ i) → (a.evaluate M ρ ↔ a.evaluate M σ) := by
  intro a
  induction a with
  | predicate p args =>
    intro ρ σ h
    have he : args.map (Term.evaluate M ρ) = args.map (Term.evaluate M σ) := by
      apply List.map_congr_left
      intro t ht
      exact Term.evaluate_congr M t ρ σ (fun i hi =>
        h i (List.mem_flatten.mpr ⟨t.support, List.mem_map.mpr ⟨t, ht, rfl⟩, hi⟩))
    simp only [evaluate, he]
  | falsum => intro ρ σ h; rfl
  | implies a b iha ihb =>
    intro ρ σ h
    exact imp_congr (iha ρ σ (fun i hi => h i (List.mem_append_left _ hi)))
      (ihb ρ σ (fun i hi => h i (List.mem_append_right _ hi)))
  | conjunction a b iha ihb =>
    intro ρ σ h
    exact and_congr (iha ρ σ (fun i hi => h i (List.mem_append_left _ hi)))
      (ihb ρ σ (fun i hi => h i (List.mem_append_right _ hi)))
  | disjunction a b iha ihb =>
    intro ρ σ h
    exact or_congr (iha ρ σ (fun i hi => h i (List.mem_append_left _ hi)))
      (ihb ρ σ (fun i hi => h i (List.mem_append_right _ hi)))
  | universal body ih =>
    intro ρ σ h
    apply forall_congr'
    intro x
    apply ih
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact h i (List.mem_filterMap.mpr ⟨i+1, hi, rfl⟩)
  | existential body ih =>
    intro ρ σ h
    apply exists_congr
    intro x
    apply ih
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact h i (List.mem_filterMap.mpr ⟨i+1, hi, rfl⟩)

theorem evaluate_fresh {D : Type} (M : Model D) (ρ : Nat → D) (a : Formula)
    {n : Nat} (hn : n ∉ a.support) (x : D) :
    a.evaluate M (updateEnvironment ρ n x) ↔ a.evaluate M ρ := by
  apply Formula.evaluate_congr
  intro i hi
  have he : i ≠ n := fun he => hn (he ▸ hi)
  simp [updateEnvironment, he]

theorem evaluate_fresh_instance {D : Type} (M : Model D) (ρ : Nat → D) (body : Formula)
    {n : Nat} (hn : n ∉ lowerSupport body.support) (x : D) :
    (body.instantiate (.variable n)).evaluate M (updateEnvironment ρ n x) ↔
      body.evaluate M (extend x ρ) := by
  rw [Formula.evaluate_instantiate]
  have he : Term.evaluate M (updateEnvironment ρ n x) (.variable n) = x := by
    simp [Term.evaluate, updateEnvironment]
  rw [he]
  apply Formula.evaluate_congr
  intro i hi
  cases i with
  | zero => rfl
  | succ i =>
    have he : i ≠ n := by
      intro he
      subst i
      exact hn (List.mem_filterMap.mpr ⟨n+1, hi, rfl⟩)
    simp [extend, updateEnvironment, he]

def freshIndex (Γ : List Formula) : Nat :=
  ((Γ.map Formula.support).flatten.foldr max 0) + 1

theorem le_maximum {xs : List Nat} {i : Nat} (hi : i ∈ xs) : i ≤ xs.foldr max 0 := by
  induction xs with
  | nil => cases hi
  | cons a rest ih =>
    rcases List.mem_cons.mp hi with he | hr
    · subst i; exact Nat.le_max_left ..
    · exact Nat.le_trans (ih hr) (Nat.le_max_right ..)

theorem freshIndex_fresh (Γ : List Formula) (a : Formula) (ha : a ∈ Γ) :
    freshIndex Γ ∉ a.support := by
  intro hn
  have hb := le_maximum (List.mem_flatten.mpr
    ⟨a.support, List.mem_map.mpr ⟨a, ha, rfl⟩, hn⟩)
  unfold freshIndex at hb
  omega

end Principia.FirstOrder
