import Principia.FirstOrder.Syntax

namespace Principia.FirstOrder

/-- An interpretation of function and predicate symbols over a nonempty domain. -/
structure Model (Domain : Type) where
  function : Nat → List Domain → Domain
  predicate : Nat → List Domain → Prop

namespace Term

def evaluate {D : Type} (M : Model D) (ρ : Nat → D) : Term → D
  | .variable i => ρ i
  | .function f args => M.function f (args.map (evaluate M ρ))

theorem evaluate_substitute {D : Type} (M : Model D) (ρ : Nat → D)
    (σ : Nat → Term) (t : Term) :
    evaluate M ρ (substitute σ t) =
      evaluate M (fun i => evaluate M ρ (σ i)) t := by
  cases t with
  | «variable» i => simp [substitute, evaluate]
  | function f args =>
    simp only [substitute, evaluate, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro a ha
    exact evaluate_substitute M ρ σ a
termination_by sizeOf t
decreasing_by
  have hs := List.sizeOf_lt_of_mem ha
  simp only [Term.function.sizeOf_spec]
  omega

theorem evaluate_rename {D : Type} (M : Model D) (ρ : Nat → D)
    (f : Nat → Nat) (t : Term) :
    evaluate M ρ (rename f t) = evaluate M (fun i => ρ (f i)) t :=
  by simpa [rename, evaluate] using
    (evaluate_substitute M ρ (fun i => .variable (f i)) t)

end Term

namespace Formula

def evaluate {D : Type} (M : Model D) (ρ : Nat → D) : Formula → Prop
  | .predicate p args => M.predicate p (args.map (Term.evaluate M ρ))
  | .falsum => False
  | .implies a b => evaluate M ρ a → evaluate M ρ b
  | .conjunction a b => evaluate M ρ a ∧ evaluate M ρ b
  | .disjunction a b => evaluate M ρ a ∨ evaluate M ρ b
  | .universal a => ∀ x, evaluate M (extend x ρ) a
  | .existential a => ∃ x, evaluate M (extend x ρ) a

theorem evaluate_substitute {D : Type} (M : Model D) :
    ∀ (a : Formula) (ρ : Nat → D) (σ : Nat → Term),
    evaluate M ρ (substitute σ a) ↔
      evaluate M (fun i => Term.evaluate M ρ (σ i)) a := by
  intro a
  induction a with
  | predicate p args =>
    intro ρ σ
    simp only [substitute, evaluate, List.map_map, Function.comp_def]
    have he : (fun t => Term.evaluate M ρ (Term.substitute σ t)) =
        (fun t => Term.evaluate M (fun i => Term.evaluate M ρ (σ i)) t) := by
      funext t
      exact Term.evaluate_substitute M ρ σ t
    rw [he]
  | falsum => intro ρ σ; rfl
  | implies a b iha ihb =>
    intro ρ σ
    exact imp_congr (iha ρ σ) (ihb ρ σ)
  | conjunction a b iha ihb =>
    intro ρ σ
    exact and_congr (iha ρ σ) (ihb ρ σ)
  | disjunction a b iha ihb =>
    intro ρ σ
    exact or_congr (iha ρ σ) (ihb ρ σ)
  | universal a ih =>
    intro ρ σ
    have henv : ∀ x, (fun i => Term.evaluate M (extend x ρ) (liftSubstitution σ i)) =
        extend x (fun i => Term.evaluate M ρ (σ i)) := by
      intro x
      funext i
      cases i with
      | zero => simp [liftSubstitution, Term.evaluate, extend]
      | succ i => exact Term.evaluate_rename M (extend x ρ) Nat.succ (σ i)
    simp only [substitute, evaluate]
    constructor
    · intro h x
      have hx := (ih (extend x ρ) (liftSubstitution σ)).mp (h x)
      rw [henv] at hx
      exact hx
    · intro h x
      apply (ih (extend x ρ) (liftSubstitution σ)).mpr
      rw [henv]
      exact h x
  | existential a ih =>
    intro ρ σ
    have henv : ∀ x, (fun i => Term.evaluate M (extend x ρ) (liftSubstitution σ i)) =
        extend x (fun i => Term.evaluate M ρ (σ i)) := by
      intro x
      funext i
      cases i with
      | zero => simp [liftSubstitution, Term.evaluate, extend]
      | succ i => exact Term.evaluate_rename M (extend x ρ) Nat.succ (σ i)
    simp only [substitute, evaluate]
    constructor
    · intro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      have h := (ih (extend x ρ) (liftSubstitution σ)).mp hx
      rw [henv] at h
      exact h
    · intro ⟨x, hx⟩
      refine ⟨x, (ih (extend x ρ) (liftSubstitution σ)).mpr ?_⟩
      rw [henv]
      exact hx

theorem evaluate_instantiate {D : Type} (M : Model D) (ρ : Nat → D)
    (a : Formula) (t : Term) :
    evaluate M ρ (a.instantiate t) ↔
      evaluate M (extend (Term.evaluate M ρ t) ρ) a := by
  have he : (fun i => Term.evaluate M ρ (extend t Term.variable i)) =
      extend (Term.evaluate M ρ t) ρ := by
    funext i
    cases i <;> simp [extend, Term.evaluate]
  unfold instantiate
  rw [evaluate_substitute, he]

theorem evaluate_shift {D : Type} (M : Model D) (ρ : Nat → D)
    (x : D) (a : Formula) : evaluate M (extend x ρ) a.shift ↔ evaluate M ρ a := by
  simpa [shift, rename, Term.evaluate, extend] using
    (evaluate_substitute M a (extend x ρ) (fun i => .variable (i + 1)))

def Entails (Γ : List Formula) (a : Formula) : Prop :=
  ∀ (D : Type) (_ : Nonempty D) (M : Model D) (ρ : Nat → D),
    (∀ b ∈ Γ, evaluate M ρ b) → evaluate M ρ a

def Valid (a : Formula) : Prop := Entails [] a

end Formula
end Principia.FirstOrder
