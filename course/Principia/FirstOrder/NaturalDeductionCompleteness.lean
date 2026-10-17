import Principia.FirstOrder.Henkin

namespace Principia.FirstOrder

/-- The usual classical quantifier duality, with an explicitly fresh eigenvariable. -/
def exists_negation_of_not_universal (Γ : List Formula) (body : Formula) :
    Derivation Γ (.implies (Formula.universal body).negation (.existential body.negation)) := by
  apply Derivation.implicationIntro
  apply Derivation.contradiction
  let C := (Formula.existential body.negation).negation :: (Formula.universal body).negation :: Γ
  let n := freshIndex (.universal body :: C)
  apply Derivation.implicationElim (a := .universal body)
  · exact .assumption (by simp [Formula.negation])
  · apply Derivation.universalIntroFresh n
      (fun a ha => freshIndex_fresh _ a (List.mem_cons_of_mem _ ha))
      (freshIndex_fresh _ (.universal body) (by simp))
    apply Derivation.contradiction
    apply Derivation.implicationElim (a := .existential body.negation)
    · exact .assumption (by simp [C, Formula.negation])
    · apply Derivation.existentialIntro (.variable n)
      exact .assumption (by simp [Formula.instantiate, Formula.substitute, Formula.negation])

namespace Henkin

theorem theory_implication {Γ : List Formula} (hΓ : Consistent Γ) (a b : Formula) :
    Theory Γ (.implies a b) ↔ (Theory Γ a → Theory Γ b) := by
  constructor
  · exact theory_modus_ponens
  · intro h
    classical
    by_cases ha : Theory Γ a
    · obtain ⟨n, ⟨db⟩⟩ := h ha
      exact ⟨n, ⟨.implicationIntro (.weakening db (by simp_all))⟩⟩
    · obtain ⟨n, ⟨dna⟩⟩ := (theory_negation hΓ a).mpr ha
      exact ⟨n, ⟨.implicationIntro (.falseElim (.implicationElim
        (.weakening dna (by simp_all)) (.assumption (by simp))))⟩⟩

theorem theory_conjunction {Γ : List Formula} (a b : Formula) :
    Theory Γ (.conjunction a b) ↔ Theory Γ a ∧ Theory Γ b := by
  constructor
  · intro ⟨n, ⟨d⟩⟩
    exact ⟨⟨n, ⟨.conjunctionLeft d⟩⟩, ⟨n, ⟨.conjunctionRight d⟩⟩⟩
  · intro ⟨ha, hb⟩
    obtain ⟨n, ⟨da⟩, ⟨db⟩⟩ := common ha hb
    exact ⟨n, ⟨.conjunctionIntro da db⟩⟩

theorem theory_disjunction {Γ : List Formula} (hΓ : Consistent Γ) (a b : Formula) :
    Theory Γ (.disjunction a b) ↔ Theory Γ a ∨ Theory Γ b := by
  constructor
  · intro hor
    classical
    apply Classical.byContradiction
    intro hn
    have hna := (theory_negation hΓ a).mpr (fun ha => hn (Or.inl ha))
    have hnb := (theory_negation hΓ b).mpr (fun hb => hn (Or.inr hb))
    have both := (theory_conjunction a.negation b.negation).mpr ⟨hna, hnb⟩
    obtain ⟨n, ⟨dor⟩, ⟨dneg⟩⟩ := common hor both
    apply theory_consistent hΓ
    exact ⟨n, ⟨.disjunctionElim dor
      (.implicationElim (.weakening (.conjunctionLeft dneg) (by simp_all))
        (.assumption (by simp)))
      (.implicationElim (.weakening (.conjunctionRight dneg) (by simp_all))
        (.assumption (by simp)))⟩⟩
  · intro h
    rcases h with ⟨n, ⟨d⟩⟩ | ⟨n, ⟨d⟩⟩
    · exact ⟨n, ⟨.disjunctionLeft d⟩⟩
    · exact ⟨n, ⟨.disjunctionRight d⟩⟩

theorem theory_existential {Γ : List Formula} (hΓ : Consistent Γ) (body : Formula) :
    Theory Γ (.existential body) ↔ ∃ t, Theory Γ (body.instantiate t) := by
  constructor
  · exact theory_witness hΓ
  · intro ⟨t, n, ⟨d⟩⟩
    exact ⟨n, ⟨.existentialIntro t d⟩⟩

theorem theory_universal {Γ : List Formula} (hΓ : Consistent Γ) (body : Formula) :
    Theory Γ (.universal body) ↔ ∀ t, Theory Γ (body.instantiate t) := by
  constructor
  · intro ⟨n, ⟨d⟩⟩ t
    exact ⟨n, ⟨.universalElim t d⟩⟩
  · intro h
    classical
    apply Classical.byContradiction
    intro hn
    have hneg := (theory_negation hΓ (.universal body)).mpr hn
    have duality : Theory Γ (.implies (Formula.universal body).negation
        (.existential body.negation)) := ⟨0, ⟨exists_negation_of_not_universal Γ body⟩⟩
    obtain ⟨t, ht⟩ := theory_witness hΓ (theory_modus_ponens duality hneg)
    have hnot : Theory Γ (body.instantiate t).negation := by
      simpa [Formula.instantiate, Formula.substitute, Formula.negation] using ht
    exact (theory_negation hΓ _).mp hnot (h t)

noncomputable def model (Γ : List Formula) : Model Term :=
  ⟨Term.function, fun p args => Theory Γ (.predicate p args)⟩

theorem term_identity (Γ : List Formula) (t : Term) :
    t.evaluate (model Γ) Term.variable = t := by
  cases t with
  | «variable» i => simp [Term.evaluate]
  | function f args =>
    simp only [Term.evaluate, model]
    congr 1
    calc
      _ = args.map id := by
        apply List.map_congr_left
        intro a ha
        exact term_identity Γ a
      _ = args := List.map_id args

termination_by sizeOf t
decreasing_by
  have hs := List.sizeOf_lt_of_mem ha
  simp_all only [Term.function.sizeOf_spec]
  omega

def FormulaWeight : Formula → Nat
  | .predicate _ _ | .falsum => 1
  | .implies a b | .conjunction a b | .disjunction a b => 1 + FormulaWeight a + FormulaWeight b
  | .universal a | .existential a => 1 + FormulaWeight a

theorem weight_substitute (a : Formula) (σ : Nat → Term) :
    FormulaWeight (a.substitute σ) = FormulaWeight a := by
  induction a generalizing σ <;> simp_all [Formula.substitute, FormulaWeight]

theorem weight_instantiate (a : Formula) (t : Term) :
    FormulaWeight (a.instantiate t) = FormulaWeight a := weight_substitute a _

/-- The truth lemma includes quantifiers over the entire, generally infinite term domain. -/
theorem truth_lemma {Γ : List Formula} (hΓ : Consistent Γ) (a : Formula) :
    a.evaluate (model Γ) Term.variable ↔ Theory Γ a := by
  cases a with
  | predicate p args =>
    have ht : Term.evaluate (model Γ) Term.variable = id := by
      funext t; exact term_identity Γ t
    change (model Γ).predicate p (args.map (Term.evaluate (model Γ) Term.variable)) ↔ _
    rw [ht, List.map_id]
    rfl
  | falsum => exact ⟨False.elim, theory_consistent hΓ⟩
  | implies a b =>
    rw [Formula.evaluate, truth_lemma hΓ a, truth_lemma hΓ b]
    exact (theory_implication hΓ a b).symm
  | conjunction a b =>
    rw [Formula.evaluate, truth_lemma hΓ a, truth_lemma hΓ b]
    exact (theory_conjunction a b).symm
  | disjunction a b =>
    rw [Formula.evaluate, truth_lemma hΓ a, truth_lemma hΓ b]
    exact (theory_disjunction hΓ a b).symm
  | universal body =>
    rw [theory_universal hΓ]
    constructor
    · intro h t
      apply (truth_lemma hΓ (body.instantiate t)).mp
      apply (Formula.evaluate_instantiate (model Γ) Term.variable body t).mpr
      rw [term_identity]
      exact h t
    · intro h t
      have hi := (truth_lemma hΓ (body.instantiate t)).mpr (h t)
      have he := (Formula.evaluate_instantiate (model Γ) Term.variable body t).mp hi
      rw [term_identity] at he
      exact he
  | existential body =>
    rw [theory_existential hΓ]
    constructor
    · intro ⟨t, ht⟩
      refine ⟨t, (truth_lemma hΓ (body.instantiate t)).mp ?_⟩
      apply (Formula.evaluate_instantiate (model Γ) Term.variable body t).mpr
      rw [term_identity]
      exact ht
    · intro ⟨t, ht⟩
      have he := (Formula.evaluate_instantiate (model Γ) Term.variable body t).mp
        ((truth_lemma hΓ (body.instantiate t)).mpr ht)
      rw [term_identity] at he
      exact ⟨t, he⟩
termination_by FormulaWeight a
decreasing_by all_goals simp_all only [FormulaWeight, weight_instantiate] <;> omega

end Henkin

/-- General classical first-order completeness for the course's natural-deduction calculus. -/
theorem deduction_complete {Γ : List Formula} {a : Formula} (h : Formula.Entails Γ a) :
    Nonempty (Derivation Γ a) := by
  classical
  apply Classical.byContradiction
  intro hn
  have consistent : Henkin.Consistent (a.negation :: Γ) := by
    intro ⟨d⟩
    exact hn ⟨.contradiction d⟩
  have semantic : a.evaluate (Henkin.model (a.negation :: Γ)) Term.variable :=
    h Term ⟨.variable 0⟩ (Henkin.model (a.negation :: Γ)) Term.variable
      (fun b hb => (Henkin.truth_lemma consistent b).mpr
        (Henkin.theory_assumption (by simp [hb])))
  have positive := (Henkin.truth_lemma consistent a).mp semantic
  have negative : Henkin.Theory (a.negation :: Γ) a.negation :=
    Henkin.theory_assumption (by simp)
  exact (Henkin.theory_negation consistent a).mp negative positive

theorem deduction_iff_entails (Γ : List Formula) (a : Formula) :
    Nonempty (Derivation Γ a) ↔ Formula.Entails Γ a :=
  ⟨fun ⟨d⟩ => derivation_sound d, deduction_complete⟩

end Principia.FirstOrder
