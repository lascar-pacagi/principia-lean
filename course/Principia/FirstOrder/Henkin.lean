import Principia.FirstOrder.FormulaEnumeration

/-! A consistent finite context is extended to a complete witnessed theory. This is a
classical mathematical construction; deciding consistency is not an executable algorithm. -/
namespace Principia.FirstOrder.Henkin

abbrev Provable (Γ : List Formula) (a : Formula) := Nonempty (Derivation Γ a)
def Consistent (Γ : List Formula) := ¬Provable Γ .falsum

theorem weaken {Γ Δ : List Formula} {a : Formula} (h : ∀ b ∈ Γ, b ∈ Δ)
    (d : Provable Γ a) : Provable Δ a := by
  obtain ⟨d⟩ := d
  exact ⟨.weakening d h⟩

theorem consistent_choice {Γ : List Formula} (hΓ : Consistent Γ) (a : Formula) :
    Consistent (a :: Γ) ∨ Consistent (a.negation :: Γ) := by
  classical
  apply Classical.byContradiction
  intro h
  have hn : ¬Consistent (a::Γ) := fun hc => h (Or.inl hc)
  have hp : ¬Consistent (a.negation::Γ) := fun hc => h (Or.inr hc)
  obtain ⟨dn⟩ := Classical.not_not.mp hn
  obtain ⟨dp⟩ := Classical.not_not.mp hp
  exact hΓ ⟨.implicationElim (.implicationIntro dp) (.implicationIntro dn)⟩

def witnessIndex (Γ : List Formula) (body : Formula) := freshIndex (.existential body :: Γ)

theorem consistent_witness {Γ : List Formula} (hΓ : Consistent Γ) (body : Formula)
    (d : Provable Γ (.existential body)) :
    Consistent (body.instantiate (.variable (witnessIndex Γ body)) :: Γ) := by
  intro ⟨branch⟩
  obtain ⟨existential⟩ := d
  apply hΓ
  exact ⟨Derivation.existentialElimFresh (witnessIndex Γ body)
    (fun a ha => freshIndex_fresh _ a (by simp [ha]))
    (freshIndex_fresh _ (.existential body) (by simp)) (by simp [Formula.support])
    existential branch⟩

noncomputable def choose (Γ : List Formula) (a : Formula) : List Formula := by
  classical
  exact if Consistent (a :: Γ) then
    match a with
    | .existential body =>
      body.instantiate (.variable (witnessIndex (.existential body :: Γ) body)) ::
        .existential body :: Γ
    | _ => a :: Γ
  else a.negation :: Γ

theorem choose_extends (Γ : List Formula) (a : Formula) : ∀ b ∈ Γ, b ∈ choose Γ a := by
  classical
  intro b hb
  unfold choose
  split
  · cases a <;> simp [hb]
  · simp [hb]

theorem choose_consistent {Γ : List Formula} (hΓ : Consistent Γ) (a : Formula) :
    Consistent (choose Γ a) := by
  classical
  unfold choose
  split
  · rename_i h
    cases a with
    | existential body => exact consistent_witness h body ⟨.assumption (by simp)⟩
    | _ => exact h
  · rename_i h
    exact (consistent_choice hΓ a).resolve_left h

theorem choose_decides (Γ : List Formula) (a : Formula) :
    a ∈ choose Γ a ∨ a.negation ∈ choose Γ a := by
  classical
  unfold choose
  split
  · cases a <;> exact Or.inl (by simp)
  · exact Or.inr (by simp)

theorem choose_witness (Γ : List Formula) (body : Formula) :
    (Formula.existential body).negation ∈ choose Γ (.existential body) ∨
      ∃ t, body.instantiate t ∈ choose Γ (.existential body) := by
  classical
  unfold choose
  split
  · exact Or.inr ⟨.variable (witnessIndex (.existential body :: Γ) body), by simp⟩
  · exact Or.inl (by simp)

noncomputable def chooseAll (Γ : List Formula) : List Formula → List Formula
  | [] => Γ
  | a :: rest => chooseAll (choose Γ a) rest

theorem chooseAll_extends (Γ : List Formula) (pool : List Formula) :
    ∀ a ∈ Γ, a ∈ chooseAll Γ pool := by
  induction pool generalizing Γ with
  | nil => exact fun _ h => h
  | cons a rest ih => exact fun b hb => ih _ b (choose_extends Γ a b hb)

theorem chooseAll_consistent {Γ : List Formula} (hΓ : Consistent Γ) (pool : List Formula) :
    Consistent (chooseAll Γ pool) := by
  induction pool generalizing Γ with
  | nil => exact hΓ
  | cons a rest ih => exact ih (choose_consistent hΓ a)

theorem chooseAll_decides (Γ : List Formula) (pool : List Formula) {a : Formula}
    (ha : a ∈ pool) : a ∈ chooseAll Γ pool ∨ a.negation ∈ chooseAll Γ pool := by
  induction pool generalizing Γ with
  | nil => cases ha
  | cons b rest ih =>
    rcases List.mem_cons.mp ha with he | hr
    · subst b
      exact (choose_decides Γ a).imp (chooseAll_extends (choose Γ a) rest a) (chooseAll_extends (choose Γ a) rest _)
    · exact ih _ hr

theorem chooseAll_witness (Γ : List Formula) (pool : List Formula) {body : Formula}
    (ha : .existential body ∈ pool) :
    (Formula.existential body).negation ∈ chooseAll Γ pool ∨
      ∃ t, body.instantiate t ∈ chooseAll Γ pool := by
  induction pool generalizing Γ with
  | nil => cases ha
  | cons b rest ih =>
    rcases List.mem_cons.mp ha with he | hr
    · subst b
      rcases choose_witness Γ body with h | ⟨t, ht⟩
      · exact Or.inl (chooseAll_extends (choose Γ (.existential body)) rest _ h)
      · exact Or.inr ⟨t, chooseAll_extends (choose Γ (.existential body)) rest _ ht⟩
    · exact ih _ hr

noncomputable def stage (Γ : List Formula) : Nat → List Formula
  | 0 => Γ
  | n+1 => chooseAll (stage Γ n) (Enumeration.formulas n)

theorem stage_mono (Γ : List Formula) {m n : Nat} (h : m ≤ n) :
    ∀ a ∈ stage Γ m, a ∈ stage Γ n := by
  induction n with
  | zero =>
    have he : m = 0 := by omega
    subst m
    exact fun _ ha => ha
  | succ n ih =>
    by_cases he : m = n+1
    · subst m; exact fun _ ha => ha
    · exact fun a ha => chooseAll_extends _ _ a (ih (by omega) a ha)

theorem stage_consistent {Γ : List Formula} (hΓ : Consistent Γ) (n : Nat) :
    Consistent (stage Γ n) := by
  induction n with
  | zero => exact hΓ
  | succ n ih => exact chooseAll_consistent ih _

def Theory (Γ : List Formula) (a : Formula) : Prop := ∃ n, Provable (stage Γ n) a

theorem theory_assumption {Γ : List Formula} {a : Formula} (ha : a ∈ Γ) : Theory Γ a :=
  ⟨0, ⟨.assumption ha⟩⟩

theorem theory_consistent {Γ : List Formula} (hΓ : Consistent Γ) : ¬Theory Γ .falsum := by
  intro ⟨n, hn⟩
  exact stage_consistent hΓ n hn

theorem common {Γ : List Formula} {a b : Formula} (ha : Theory Γ a) (hb : Theory Γ b) :
    ∃ n, Provable (stage Γ n) a ∧ Provable (stage Γ n) b := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := hb
  exact ⟨max m n, weaken (stage_mono Γ (Nat.le_max_left ..)) hm,
    weaken (stage_mono Γ (Nat.le_max_right ..)) hn⟩

theorem theory_modus_ponens {Γ : List Formula} {a b : Formula}
    (hf : Theory Γ (.implies a b)) (ha : Theory Γ a) : Theory Γ b := by
  obtain ⟨n, ⟨df⟩, ⟨da⟩⟩ := common hf ha
  exact ⟨n, ⟨.implicationElim df da⟩⟩

theorem theory_decides (Γ : List Formula) (a : Formula) : Theory Γ a ∨ Theory Γ a.negation := by
  obtain ⟨n, hn⟩ := Enumeration.covers_formula a
  exact (chooseAll_decides (stage Γ n) _ hn).imp
    (fun ha => ⟨n+1, ⟨.assumption ha⟩⟩) (fun ha => ⟨n+1, ⟨.assumption ha⟩⟩)

theorem theory_negation {Γ : List Formula} (hΓ : Consistent Γ) (a : Formula) :
    Theory Γ a.negation ↔ ¬Theory Γ a := by
  constructor
  · intro hn ha
    exact theory_consistent hΓ (theory_modus_ponens hn ha)
  · intro hn
    exact (theory_decides Γ a).resolve_left hn

theorem theory_witness {Γ : List Formula} (hΓ : Consistent Γ) {body : Formula}
    (h : Theory Γ (.existential body)) : ∃ t, Theory Γ (body.instantiate t) := by
  obtain ⟨n, hn⟩ := Enumeration.covers_formula (.existential body)
  rcases chooseAll_witness (stage Γ n) _ hn with hneg | ⟨t, ht⟩
  · exact False.elim ((theory_negation hΓ _).mp ⟨n+1, ⟨.assumption hneg⟩⟩ h)
  · exact ⟨t, n+1, ⟨.assumption ht⟩⟩

end Principia.FirstOrder.Henkin
