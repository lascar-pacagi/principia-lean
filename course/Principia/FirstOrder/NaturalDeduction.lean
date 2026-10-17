import Principia.FirstOrder.Support

/-! Classical first-order natural deduction. Freshness is enforced by shifting the entire context
under a new variable for universal introduction and existential elimination. -/
namespace Principia.FirstOrder

inductive Derivation : List Formula → Formula → Type where
  | assumption {Γ a} : a ∈ Γ → Derivation Γ a
  | implicationIntro {Γ a b} : Derivation (a :: Γ) b → Derivation Γ (.implies a b)
  | implicationElim {Γ a b} : Derivation Γ (.implies a b) → Derivation Γ a → Derivation Γ b
  | conjunctionIntro {Γ a b} : Derivation Γ a → Derivation Γ b → Derivation Γ (.conjunction a b)
  | conjunctionLeft {Γ a b} : Derivation Γ (.conjunction a b) → Derivation Γ a
  | conjunctionRight {Γ a b} : Derivation Γ (.conjunction a b) → Derivation Γ b
  | disjunctionLeft {Γ a b} : Derivation Γ a → Derivation Γ (.disjunction a b)
  | disjunctionRight {Γ a b} : Derivation Γ b → Derivation Γ (.disjunction a b)
  | disjunctionElim {Γ a b c} : Derivation Γ (.disjunction a b) →
      Derivation (a :: Γ) c → Derivation (b :: Γ) c → Derivation Γ c
  | falseElim {Γ a} : Derivation Γ .falsum → Derivation Γ a
  | contradiction {Γ a} : Derivation (a.negation :: Γ) .falsum → Derivation Γ a
  | universalIntro {Γ body} : Derivation (Γ.map Formula.shift) body →
      Derivation Γ (.universal body)
  | universalElim {Γ body} (t : Term) : Derivation Γ (.universal body) →
      Derivation Γ (body.instantiate t)
  | existentialIntro {Γ body} (t : Term) : Derivation Γ (body.instantiate t) →
      Derivation Γ (.existential body)
  | existentialElim {Γ body c} : Derivation Γ (.existential body) →
      Derivation (body :: Γ.map Formula.shift) c.shift → Derivation Γ c
  | weakening {Γ Δ a} : Derivation Γ a → (∀ b ∈ Γ, b ∈ Δ) → Derivation Δ a
  | universalIntroFresh {Γ body} (n : Nat)
      (freshContext : ∀ a ∈ Γ, n ∉ a.support)
      (freshBody : n ∉ lowerSupport body.support) :
      Derivation Γ (body.instantiate (.variable n)) → Derivation Γ (.universal body)
  | existentialElimFresh {Γ body c} (n : Nat)
      (freshContext : ∀ a ∈ Γ, n ∉ a.support)
      (freshBody : n ∉ lowerSupport body.support) (freshConclusion : n ∉ c.support) :
      Derivation Γ (.existential body) →
      Derivation (body.instantiate (.variable n) :: Γ) c → Derivation Γ c

namespace Derivation

def nodeCount : {Γ : List Formula} → {a : Formula} → Derivation Γ a → Nat
  | _, _, .assumption _ => 1
  | _, _, .implicationIntro d => 1 + d.nodeCount
  | _, _, .implicationElim d e => 1 + d.nodeCount + e.nodeCount
  | _, _, .conjunctionIntro d e => 1 + d.nodeCount + e.nodeCount
  | _, _, .conjunctionLeft d => 1 + d.nodeCount
  | _, _, .conjunctionRight d => 1 + d.nodeCount
  | _, _, .disjunctionLeft d => 1 + d.nodeCount
  | _, _, .disjunctionRight d => 1 + d.nodeCount
  | _, _, .disjunctionElim d e f => 1 + d.nodeCount + e.nodeCount + f.nodeCount
  | _, _, .falseElim d => 1 + d.nodeCount
  | _, _, .contradiction d => 1 + d.nodeCount
  | _, _, .universalIntro d => 1 + d.nodeCount
  | _, _, .universalElim _ d => 1 + d.nodeCount
  | _, _, .existentialIntro _ d => 1 + d.nodeCount
  | _, _, .existentialElim d e => 1 + d.nodeCount + e.nodeCount
  | _, _, .weakening d _ => 1 + d.nodeCount
  | _, _, .universalIntroFresh _ _ _ d => 1 + d.nodeCount
  | _, _, .existentialElimFresh _ _ _ _ d e => 1 + d.nodeCount + e.nodeCount

end Derivation

def Satisfies {D : Type} (M : Model D) (ρ : Nat → D) (Γ : List Formula) : Prop :=
  ∀ a ∈ Γ, a.evaluate M ρ

theorem satisfies_cons {D : Type} {M : Model D} {ρ : Nat → D} {Γ : List Formula} {a : Formula}
    (ha : a.evaluate M ρ) (hΓ : Satisfies M ρ Γ) : Satisfies M ρ (a :: Γ) := by
  intro b hb
  cases hb with
  | head => exact ha
  | tail _ h => exact hΓ b h

theorem satisfies_shift {D : Type} {M : Model D} {ρ : Nat → D} {Γ : List Formula}
    (hΓ : Satisfies M ρ Γ) (x : D) : Satisfies M (extend x ρ) (Γ.map Formula.shift) := by
  intro a ha
  obtain ⟨b, hb, he⟩ := List.mem_map.mp ha
  subst a
  exact (Formula.evaluate_shift M ρ x b).mpr (hΓ b hb)

/-- Every rule, including the eigenvariable rules, preserves truth in every interpretation. -/
theorem derivation_sound_in_model {D : Type} (M : Model D) {Γ : List Formula} {a : Formula}
    (d : Derivation Γ a) : ∀ ρ, Satisfies M ρ Γ → a.evaluate M ρ := by
  induction d with
  | assumption h => intro ρ hΓ; exact hΓ _ h
  | implicationIntro d ih =>
    intro ρ hΓ ha
    exact ih ρ (satisfies_cons ha hΓ)
  | implicationElim d e ihd ihe => intro ρ hΓ; exact ihd ρ hΓ (ihe ρ hΓ)
  | conjunctionIntro d e ihd ihe => intro ρ hΓ; exact ⟨ihd ρ hΓ, ihe ρ hΓ⟩
  | conjunctionLeft d ih => intro ρ hΓ; exact (ih ρ hΓ).1
  | conjunctionRight d ih => intro ρ hΓ; exact (ih ρ hΓ).2
  | disjunctionLeft d ih => intro ρ hΓ; exact Or.inl (ih ρ hΓ)
  | disjunctionRight d ih => intro ρ hΓ; exact Or.inr (ih ρ hΓ)
  | disjunctionElim d e f ihd ihe ihf =>
    intro ρ hΓ
    cases ihd ρ hΓ with
    | inl ha => exact ihe ρ (satisfies_cons ha hΓ)
    | inr hb => exact ihf ρ (satisfies_cons hb hΓ)
  | falseElim d ih => intro ρ hΓ; exact False.elim (ih ρ hΓ)
  | contradiction d ih =>
    intro ρ hΓ
    apply Classical.byContradiction
    intro hna
    exact ih ρ (satisfies_cons hna hΓ)
  | universalIntro d ih =>
    intro ρ hΓ x
    exact ih (extend x ρ) (satisfies_shift hΓ x)
  | universalElim t d ih =>
    intro ρ hΓ
    apply (Formula.evaluate_instantiate M ρ _ t).mpr
    exact ih ρ hΓ (Term.evaluate M ρ t)
  | existentialIntro t d ih =>
    intro ρ hΓ
    exact ⟨Term.evaluate M ρ t, (Formula.evaluate_instantiate M ρ _ t).mp (ih ρ hΓ)⟩
  | existentialElim d e ihd ihe =>
    intro ρ hΓ
    obtain ⟨x, hx⟩ := ihd ρ hΓ
    apply (Formula.evaluate_shift M ρ x _).mp
    exact ihe (extend x ρ) (satisfies_cons hx (satisfies_shift hΓ x))
  | weakening d included ih =>
    intro ρ hΔ
    exact ih ρ (fun b hb => hΔ b (included b hb))
  | universalIntroFresh n freshContext freshBody d ih =>
    intro ρ hΓ x
    apply (evaluate_fresh_instance M ρ _ freshBody x).mp
    exact ih (updateEnvironment ρ n x) (fun a ha =>
      (evaluate_fresh M ρ a (freshContext a ha) x).mpr (hΓ a ha))
  | existentialElimFresh n freshContext freshBody freshConclusion d e ihd ihe =>
    intro ρ hΓ
    obtain ⟨x, hx⟩ := ihd ρ hΓ
    apply (evaluate_fresh M ρ _ freshConclusion x).mp
    apply ihe (updateEnvironment ρ n x)
    apply satisfies_cons ((evaluate_fresh_instance M ρ _ freshBody x).mpr hx)
    exact fun a ha => (evaluate_fresh M ρ a (freshContext a ha) x).mpr (hΓ a ha)

theorem derivation_sound {Γ : List Formula} {a : Formula} (d : Derivation Γ a) :
    Formula.Entails Γ a := by
  intro D inhabited M ρ hΓ
  exact derivation_sound_in_model M d ρ hΓ

end Principia.FirstOrder
