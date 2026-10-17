import Principia.FirstOrder.ClausificationCore

set_option warningAsError true

namespace Principia.FirstOrder

/-- Models agree on the old language; fresh function symbols may receive new meanings. -/
def AgreeBelow {D : Type} (M N : Model D) (f : Nat) : Prop :=
  M.predicate = N.predicate ∧ ∀ g, g < f → ∀ args, M.function g args = N.function g args

theorem AgreeBelow.refl {D : Type} (M : Model D) (f : Nat) : AgreeBelow M M f :=
  ⟨rfl, fun _ _ _ => rfl⟩
theorem AgreeBelow.mono {D : Type} {M N : Model D} {f g : Nat}
    (h : AgreeBelow M N g) (hfg : f ≤ g) : AgreeBelow M N f :=
  ⟨h.1, fun k hk args => h.2 k (by omega) args⟩
theorem AgreeBelow.trans {D : Type} {M N P : Model D} {f : Nat}
    (h : AgreeBelow M N f) (k : AgreeBelow N P f) : AgreeBelow M P f :=
  ⟨h.1.trans k.1, fun g hg args => (h.2 g hg args).trans (k.2 g hg args)⟩

theorem fold_max_initial (xs : List Nat) (initial : Nat) : initial ≤ xs.foldl max initial := by
  induction xs generalizing initial with
  | nil => exact Nat.le_refl _
  | cons a rest ih => exact Nat.le_trans (Nat.le_max_left ..) (ih _)

theorem fold_max_member {xs : List Nat} (initial : Nat) {n : Nat} (hn : n ∈ xs) :
    n ≤ xs.foldl max initial := by
  induction xs generalizing initial with
  | nil => cases hn
  | cons a rest ih =>
    rcases List.mem_cons.mp hn with he | hr
    · subst n; exact Nat.le_trans (Nat.le_max_right ..) (fold_max_initial rest _)
    · exact ih _ hr

theorem fold_max_le {xs : List Nat} {initial n : Nat}
    (hi : initial ≤ n) (h : ∀ k ∈ xs, k ≤ n) : xs.foldl max initial ≤ n := by
  induction xs generalizing initial with
  | nil => exact hi
  | cons a rest ih =>
    exact ih (Nat.max_le.mpr ⟨hi, h a (by simp)⟩) (fun k hk => h k (by simp [hk]))

def literalFunctionBound (l : Literal) : Nat :=
  (l.atom.arguments.map Term.functionBound).foldl max 0

def literalSupport (l : Literal) : List Nat := (l.atom.arguments.map Term.support).flatten

def Nnf.functionBound : Nnf → Nat
  | .literal l => literalFunctionBound l
  | .verum | .falsum => 0
  | .conjunction a b | .disjunction a b => max a.functionBound b.functionBound
  | .universal a | .existential a => a.functionBound

def Nnf.support : Nnf → List Nat
  | .literal l => literalSupport l
  | .verum | .falsum => []
  | .conjunction a b | .disjunction a b => a.support ++ b.support
  | .universal a | .existential a => lowerSupport a.support

def Matrix.functionBound : Matrix → Nat
  | .literal l => literalFunctionBound l
  | .verum | .falsum => 0
  | .conjunction a b | .disjunction a b => max a.functionBound b.functionBound

def Matrix.support : Matrix → List Nat
  | .literal l => literalSupport l
  | .verum | .falsum => []
  | .conjunction a b | .disjunction a b => a.support ++ b.support

theorem Term.evaluate_agree {D : Type} {M N : Model D} {f : Nat} (h : AgreeBelow M N f)
    (t : Term) (bound : t.functionBound ≤ f) (ρ : Nat → D) : t.evaluate M ρ = t.evaluate N ρ := by
  cases t with
  | «variable» i => simp [evaluate]
  | function g args =>
    simp only [functionBound] at bound
    have hg : g < f := by
      have hi := fold_max_initial (args.map Term.functionBound) (g+1)
      omega
    have ha : args.map (evaluate M ρ) = args.map (evaluate N ρ) := by
      apply List.map_congr_left
      intro a ha
      apply Term.evaluate_agree h a
      exact Nat.le_trans (fold_max_member _ (List.mem_map.mpr ⟨a, ha, rfl⟩)) bound
    simp only [evaluate, ha]
    exact h.2 g hg _
termination_by sizeOf t
decreasing_by
  have hs := List.sizeOf_lt_of_mem ha
  simp_all only [Term.function.sizeOf_spec]
  omega

theorem Literal.evaluate_agree {D : Type} {M N : Model D} {f : Nat} (h : AgreeBelow M N f)
    (l : Literal) (bound : literalFunctionBound l ≤ f) (ρ : Nat → D) :
    l.evaluate M ρ ↔ l.evaluate N ρ := by
  have ht : l.atom.arguments.map (Term.evaluate M ρ) = l.atom.arguments.map (Term.evaluate N ρ) := by
    apply List.map_congr_left
    intro t ht
    exact Term.evaluate_agree h t
      (Nat.le_trans (fold_max_member _ (List.mem_map.mpr ⟨t, ht, rfl⟩)) bound) ρ
  simp only [Literal.evaluate, Atom.evaluate, ht, h.1]

theorem Literal.evaluate_congr {D : Type} (M : Model D) (l : Literal) (ρ σ : Nat → D)
    (h : ∀ i ∈ literalSupport l, ρ i = σ i) : l.evaluate M ρ ↔ l.evaluate M σ := by
  have ht : l.atom.arguments.map (Term.evaluate M ρ) = l.atom.arguments.map (Term.evaluate M σ) := by
    apply List.map_congr_left
    intro t ht
    exact Term.evaluate_congr M t ρ σ (fun i hi =>
      h i (List.mem_flatten.mpr ⟨t.support, List.mem_map.mpr ⟨t, ht, rfl⟩, hi⟩))
  simp only [Literal.evaluate, Atom.evaluate, ht]

theorem Nnf.evaluate_congr {D : Type} (M : Model D) : ∀ (a : Nnf) (ρ σ : Nat → D),
    (∀ i ∈ a.support, ρ i = σ i) → (a.evaluate M ρ ↔ a.evaluate M σ) := by
  intro a
  induction a with
  | literal l => exact fun ρ σ h => Literal.evaluate_congr M l ρ σ h
  | verum => intro ρ σ h; rfl
  | falsum => intro ρ σ h; rfl
  | conjunction a b iha ihb =>
    intro ρ σ h
    exact and_congr (iha _ _ (fun i hi => h i (List.mem_append_left _ hi)))
      (ihb _ _ (fun i hi => h i (List.mem_append_right _ hi)))
  | disjunction a b iha ihb =>
    intro ρ σ h
    exact or_congr (iha _ _ (fun i hi => h i (List.mem_append_left _ hi)))
      (ihb _ _ (fun i hi => h i (List.mem_append_right _ hi)))
  | universal a ih =>
    intro ρ σ h
    apply forall_congr'
    intro x
    apply ih
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact h i (List.mem_filterMap.mpr ⟨i+1, hi, rfl⟩)
  | existential a ih =>
    intro ρ σ h
    apply exists_congr
    intro x
    apply ih
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact h i (List.mem_filterMap.mpr ⟨i+1, hi, rfl⟩)

theorem Nnf.evaluate_agree {D : Type} {M N : Model D} {f : Nat} (h : AgreeBelow M N f) :
    ∀ a : Nnf, a.functionBound ≤ f → ∀ ρ, a.evaluate M ρ ↔ a.evaluate N ρ := by
  intro a
  induction a with
  | literal l => exact fun hb ρ => Literal.evaluate_agree h l hb ρ
  | verum => intro hb ρ; rfl
  | falsum => intro hb ρ; rfl
  | conjunction a b iha ihb =>
    intro hb ρ
    exact and_congr (iha (Nat.le_trans (Nat.le_max_left ..) hb) ρ)
      (ihb (Nat.le_trans (Nat.le_max_right ..) hb) ρ)
  | disjunction a b iha ihb =>
    intro hb ρ
    exact or_congr (iha (Nat.le_trans (Nat.le_max_left ..) hb) ρ)
      (ihb (Nat.le_trans (Nat.le_max_right ..) hb) ρ)
  | universal a ih => intro hb ρ; exact forall_congr' (fun x => ih hb (extend x ρ))
  | existential a ih => intro hb ρ; exact exists_congr (fun x => ih hb (extend x ρ))

theorem Matrix.evaluate_agree {D : Type} {M N : Model D} {f : Nat} (h : AgreeBelow M N f) :
    ∀ a : Matrix, a.functionBound ≤ f → ∀ ρ, a.evaluate M ρ ↔ a.evaluate N ρ := by
  intro a
  induction a with
  | literal l => exact fun hb ρ => Literal.evaluate_agree h l hb ρ
  | verum => intro hb ρ; rfl
  | falsum => intro hb ρ; rfl
  | conjunction a b iha ihb =>
    intro hb ρ
    exact and_congr (iha (Nat.le_trans (Nat.le_max_left ..) hb) ρ)
      (ihb (Nat.le_trans (Nat.le_max_right ..) hb) ρ)
  | disjunction a b iha ihb =>
    intro hb ρ
    exact or_congr (iha (Nat.le_trans (Nat.le_max_left ..) hb) ρ)
      (ihb (Nat.le_trans (Nat.le_max_right ..) hb) ρ)

theorem Matrix.evaluate_congr {D : Type} (M : Model D) : ∀ (a : Matrix) (ρ σ : Nat → D),
    (∀ i ∈ a.support, ρ i = σ i) → (a.evaluate M ρ ↔ a.evaluate M σ) := by
  intro a
  induction a with
  | literal l => exact fun ρ σ h => Literal.evaluate_congr M l ρ σ h
  | verum => intro ρ σ h; rfl
  | falsum => intro ρ σ h; rfl
  | conjunction a b iha ihb =>
    intro ρ σ h
    exact and_congr (iha _ _ (fun i hi => h i (List.mem_append_left _ hi)))
      (ihb _ _ (fun i hi => h i (List.mem_append_right _ hi)))
  | disjunction a b iha ihb =>
    intro ρ σ h
    exact or_congr (iha _ _ (fun i hi => h i (List.mem_append_left _ hi)))
      (ihb _ _ (fun i hi => h i (List.mem_append_right _ hi)))

end Principia.FirstOrder
