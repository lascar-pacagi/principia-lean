import Principia.FirstOrder.SkolemExpansion
import Principia.FirstOrder.SkolemRecovery

set_option warningAsError true

namespace Principia.FirstOrder

theorem nnf_functionBound (a : Formula) (p : Bool) :
    (a.toNnf p).functionBound = a.functionBound := by
  induction a generalizing p <;> cases p <;>
    simp_all [Formula.toNnf, Nnf.functionBound, Formula.functionBound, literalFunctionBound]

theorem nnf_support (a : Formula) (p : Bool) : (a.toNnf p).support = a.support := by
  induction a generalizing p <;> cases p <;>
    simp_all [Formula.toNnf, Nnf.support, Formula.support, literalSupport]

def freeVariableCount (a : Formula) : Nat := (a.support.map (· + 1)).foldl max 0

theorem freeVariableCount_covers (a : Formula) {i : Nat} (hi : i ∈ a.support) :
    i < freeVariableCount a := by
  have hb : i+1 ≤ freeVariableCount a :=
    fold_max_member 0 (List.mem_map.mpr ⟨i, hi, rfl⟩)
  omega

def initialTranslation (a : Formula) : Nat → Term :=
  fun i => .function (a.functionBound+i) []

theorem initial_bound (a : Formula) :
    SubstitutionBound (a.toNnf true) (initialTranslation a)
      (a.functionBound + freeVariableCount a) := by
  intro i hi
  have h := freeVariableCount_covers a (by simpa only [nnf_support] using hi)
  simp only [initialTranslation, Term.functionBound, List.map_nil, List.foldl_nil]
  omega

theorem initial_covered (a : Formula) : Covered (a.toNnf true) (initialTranslation a) [] := by
  intro i hi j hj
  simp [initialTranslation, Term.support] at hj

/-- Interpret the fresh constants as the original free-variable assignment. -/
def initializeModel {D : Type} (M : Model D) (a : Formula) (ρ : Nat → D) : Model D :=
  ⟨fun f args => if a.functionBound ≤ f ∧ f < a.functionBound + freeVariableCount a
    then ρ (f - a.functionBound) else M.function f args, M.predicate⟩

theorem initializeModel_agrees {D : Type} (M : Model D) (a : Formula) (ρ : Nat → D) :
    AgreeBelow M (initializeModel M a ρ) a.functionBound := by
  refine ⟨rfl, ?_⟩
  intro f hf args
  simp [initializeModel, show ¬a.functionBound ≤ f by omega]

theorem initializeModel_free_variable {D : Type} (M : Model D) (a : Formula)
    (ρ σ : Nat → D) {i : Nat} (hi : i ∈ a.support) :
    (initialTranslation a i).evaluate (initializeModel M a ρ) σ = ρ i := by
  have hb := freeVariableCount_covers a hi
  simp [initialTranslation, Term.evaluate, initializeModel,
    show a.functionBound + i < a.functionBound + freeVariableCount a by omega]

/-- Every model/environment of the input expands, on the SAME nonempty domain, to a model
of its generated clauses. All original function and predicate interpretations are preserved. -/
theorem clausify_model_expansion {D : Type} (inhabited : Nonempty D) (M : Model D)
    (ρ : Nat → D) (a : Formula) (ha : a.evaluate M ρ) :
    ∃ N : Model D, AgreeBelow M N a.functionBound ∧ SatisfiesClauses N (clausify a).clauses := by
  let M₀ := initializeModel M a ρ
  have old : AgreeBelow M M₀ a.functionBound := initializeModel_agrees M a ρ
  have normalized : (a.toNnf true).evaluate M ρ := (toNnf_correct M a true ρ).mpr ha
  have unchanged := (Nnf.evaluate_agree old (a.toNnf true) (by rw [nnf_functionBound]; exact Nat.le_refl _) ρ).mp normalized
  have source : ∀ σ : Nat → D, True → Translated M₀ (initialTranslation a) (a.toNnf true) σ := by
    intro σ _
    apply (Nnf.evaluate_congr M₀ (a.toNnf true) ρ _ ?_).mp unchanged
    intro i hi
    exact (initializeModel_free_variable M a ρ σ (by simpa only [nnf_support] using hi)).symm
  obtain ⟨N, extended, result⟩ := skolemize_expand inhabited (a.toNnf true) M₀
    (initialTranslation a) [] (a.functionBound + freeVariableCount a) 0 (fun _ => True)
    (by rw [nnf_functionBound]; omega) (initial_bound a) (initial_covered a)
    (by simp) (fun _ _ _ => Iff.rfl) source
  refine ⟨N, old.trans (extended.mono (by omega)), ?_⟩
  intro c hc σ
  exact (matrix_toClauses_correct N σ _).mpr (result σ True.intro) c hc

/-- A model of the generated clauses recovers a satisfying environment for the input.
The free constants provide that environment; they are not universally quantified variables. -/
theorem clausify_model_recovery {D : Type} (inhabited : Nonempty D) (M : Model D)
    (a : Formula) (h : SatisfiesClauses M (clausify a).clauses) :
    ∃ ρ : Nat → D, a.evaluate M ρ := by
  let σ₀ : Nat → D := fun _ => Classical.choice inhabited
  have matrix : ∀ σ : Nat → D,
      (skolemize (initialTranslation a) [] (a.toNnf true)
        (a.functionBound + freeVariableCount a) 0).matrix.evaluate M σ := by
    intro σ
    exact (matrix_toClauses_correct M σ _).mp (fun c hc => h c hc σ)
  have recovered := skolemize_recover (a.toNnf true) M (initialTranslation a) []
    (a.functionBound + freeVariableCount a) 0 σ₀
    (by rw [nnf_functionBound]; omega) (initial_bound a) (initial_covered a)
    (by simp) (fun σ _ => matrix σ)
  exact ⟨_, (toNnf_correct M a true _).mp recovered⟩

def Formula.Satisfiable (a : Formula) : Prop :=
  ∃ (D : Type) (_ : Nonempty D) (M : Model D) (ρ : Nat → D), a.evaluate M ρ

def ClausesSatisfiable (S : ClauseSet) : Prop :=
  ∃ (D : Type) (_ : Nonempty D) (M : Model D), SatisfiesClauses M S

/-- General equisatisfiability of the ACTUAL executable conversion, with arbitrary alternation
of quantifiers, nested function terms, open formulas, and nonempty domains. -/
theorem clausify_equisatisfiable (a : Formula) :
    a.Satisfiable ↔ ClausesSatisfiable (clausify a).clauses := by
  constructor
  · intro ⟨D, inhabited, M, ρ, h⟩
    obtain ⟨N, _, hn⟩ := clausify_model_expansion inhabited M ρ a h
    exact ⟨D, inhabited, N, hn⟩
  · intro ⟨D, inhabited, M, h⟩
    obtain ⟨ρ, hρ⟩ := clausify_model_recovery inhabited M a h
    exact ⟨D, inhabited, M, ρ, hρ⟩

theorem clausify_unsatisfiable (a : Formula) :
    Unsatisfiable (clausify a).clauses ↔ ¬a.Satisfiable := by
  constructor
  · intro h ⟨D, inhabited, M, ρ, ha⟩
    obtain ⟨N, _, hN⟩ := clausify_model_expansion inhabited M ρ a ha
    exact h D inhabited N hN
  · intro hn D inhabited M hM
    obtain ⟨ρ, hρ⟩ := clausify_model_recovery inhabited M a hM
    exact hn ⟨D, inhabited, M, ρ, hρ⟩

end Principia.FirstOrder
