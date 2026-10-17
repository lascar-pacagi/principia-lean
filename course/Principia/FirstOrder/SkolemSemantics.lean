import Principia.FirstOrder.SkolemBounds
set_option warningAsError true

namespace Principia.FirstOrder

abbrev Translated {D : Type} (M : Model D) (ρ : Nat → Term) (a : Nnf) (σ : Nat → D) :=
  a.evaluate M (fun i => (ρ i).evaluate M σ)

def DependsOn {D : Type} (P : (Nat → D) → Prop) (U : List Nat) : Prop :=
  ∀ ρ σ, (∀ i ∈ U, ρ i = σ i) → (P ρ ↔ P σ)

theorem depends_translated {D : Type} (M : Model D) (ρ : Nat → Term) (a : Nnf)
    {U : List Nat} (hc : Covered a ρ U) : DependsOn (Translated M ρ a) U := by
  intro σ τ h
  apply Nnf.evaluate_congr
  intro i hi
  exact Term.evaluate_congr M (ρ i) σ τ (fun j hj => h j (hc i hi j hj))

theorem translated_agree {D : Type} {M N : Model D} {f : Nat} (h : AgreeBelow M N f)
    (a : Nnf) (ρ : Nat → Term) (σ : Nat → D) (ha : a.functionBound ≤ f)
    (hρ : SubstitutionBound a ρ f) : Translated M ρ a σ ↔ Translated N ρ a σ := by
  apply (Nnf.evaluate_agree h a ha _).trans
  apply Nnf.evaluate_congr
  intro i hi
  exact Term.evaluate_agree h (ρ i) (hρ i hi) σ

theorem body_congr {D : Type} (M : Model D) (body : Nnf) (ρ σ : Nat → D) (x : D)
    (h : ∀ i ∈ lowerSupport body.support, ρ i = σ i) :
    body.evaluate M (extend x ρ) ↔ body.evaluate M (extend x σ) := by
  apply Nnf.evaluate_congr
  intro i hi
  cases i with
  | zero => rfl
  | succ i => exact h i (List.mem_filterMap.mpr ⟨i+1, hi, rfl⟩)

theorem evaluate_extended_substitution {D : Type} (M : Model D) (σ : Nat → D)
    (ρ : Nat → Term) (t : Term) :
    (fun i => (extend t ρ i).evaluate M σ) =
      extend (t.evaluate M σ) (fun i => (ρ i).evaluate M σ) := by
  funext i
  cases i <;> rfl

theorem evaluate_function_variables {D : Type} (M : Model D) (σ : Nat → D)
    (f : Nat) (U : List Nat) :
    (Term.function f (U.map Term.variable)).evaluate M σ = M.function f (U.map σ) := by
  simp [Term.evaluate, List.map_map, Function.comp_def]

noncomputable def reconstruct {D : Type} (inhabited : Nonempty D) :
    List Nat → List D → Nat → D
  | u :: us, x :: xs, i => if i = u then x else reconstruct inhabited us xs i
  | _, _, _ => Classical.choice inhabited

theorem reconstruct_agrees {D : Type} (inhabited : Nonempty D) (U : List Nat) (σ : Nat → D) :
    ∀ i ∈ U, reconstruct inhabited U (U.map σ) i = σ i := by
  induction U with
  | nil => simp
  | cons u rest ih =>
    intro i hi
    by_cases he : i = u
    · subst i; simp [reconstruct]
    · have hr := (List.mem_cons.mp hi).resolve_left he
      simpa [reconstruct, he] using ih i hr

noncomputable def witnessFunction {D : Type} (inhabited : Nonempty D) (M : Model D)
    (body : Nnf) (ρ : Nat → Term) (U : List Nat) (args : List D) : D := by
  classical
  let σ := reconstruct inhabited U args
  exact if h : ∃ x, body.evaluate M (extend x (fun i => (ρ i).evaluate M σ))
    then Classical.choose h else Classical.choice inhabited

theorem witnessFunction_spec {D : Type} (inhabited : Nonempty D) (M : Model D)
    (body : Nnf) (ρ : Nat → Term) (U : List Nat) (hc : Covered (.existential body) ρ U)
    (σ : Nat → D) (h : Translated M ρ (.existential body) σ) :
    body.evaluate M (extend (witnessFunction inhabited M body ρ U (U.map σ))
      (fun i => (ρ i).evaluate M σ)) := by
  classical
  let τ := reconstruct inhabited U (U.map σ)
  have he : ∀ i ∈ lowerSupport body.support, (ρ i).evaluate M τ = (ρ i).evaluate M σ := by
    intro i hi
    apply Term.evaluate_congr
    intro j hj
    exact reconstruct_agrees inhabited U σ j (hc i hi j hj)
  have hr : ∃ x, body.evaluate M (extend x (fun i => (ρ i).evaluate M τ)) := by
    obtain ⟨x, hx⟩ := h
    exact ⟨x, (body_congr M body _ _ x he).mpr hx⟩
  have chosen : body.evaluate M
      (extend (witnessFunction inhabited M body ρ U (U.map σ))
        (fun i => (ρ i).evaluate M τ)) := by
    dsimp only [witnessFunction]
    rw [dif_pos hr]
    exact Classical.choose_spec hr
  exact (body_congr M body _ _ _ he).mp chosen

def replaceFunction {D : Type} (M : Model D) (f : Nat) (g : List D → D) : Model D :=
  ⟨fun k args => if k = f then g args else M.function k args, M.predicate⟩

theorem replaceFunction_agrees {D : Type} (M : Model D) (f : Nat) (g : List D → D) :
    AgreeBelow M (replaceFunction M f g) f := by
  refine ⟨rfl, ?_⟩
  intro k hk args
  simp [replaceFunction, show k ≠ f by omega]

/-- Semantic invariant needed when a binder is removed by the compiler. -/
theorem covered_universal {body : Nnf} {ρ : Nat → Term} {U : List Nat} {v : Nat}
    (hc : Covered (.universal body) ρ U) :
    Covered body (extend (.variable v) ρ) (U ++ [v]) := by
  intro i hi j hj
  cases i with
  | zero => exact List.mem_append_right _ (by simpa [extend, Term.support] using hj)
  | succ i => exact List.mem_append_left _ (hc i (List.mem_filterMap.mpr ⟨i+1, hi, rfl⟩) j hj)

theorem bound_universal {body : Nnf} {ρ : Nat → Term} {f v : Nat}
    (hρ : SubstitutionBound (.universal body) ρ f) :
    SubstitutionBound body (extend (.variable v) ρ) f := by
  intro i hi
  cases i with
  | zero => simp [extend, Term.functionBound]
  | succ i => exact hρ i (List.mem_filterMap.mpr ⟨i+1, hi, rfl⟩)

theorem covered_existential {body : Nnf} {ρ : Nat → Term} {U : List Nat} {f : Nat}
    (hc : Covered (.existential body) ρ U) :
    Covered body (extend (.function f (U.map .variable)) ρ) U := by
  intro i hi j hj
  cases i with
  | zero => simpa only [extend, skolem_term_support] using hj
  | succ i => exact hc i (List.mem_filterMap.mpr ⟨i+1, hi, rfl⟩) j hj

theorem bound_existential {body : Nnf} {ρ : Nat → Term} {U : List Nat} {f : Nat}
    (hρ : SubstitutionBound (.existential body) ρ f) :
    SubstitutionBound body (extend (.function f (U.map .variable)) ρ) (f+1) := by
  intro i hi
  cases i with
  | zero => exact skolem_term_bound f U
  | succ i => exact Nat.le_succ_of_le (hρ i (List.mem_filterMap.mpr ⟨i+1, hi, rfl⟩))

end Principia.FirstOrder
