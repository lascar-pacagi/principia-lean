import Principia.Goedel.Diagonal

/-!
# Principia.Goedel.Incompleteness — the abstract first incompleteness theorem (Course 5, slice 5.3)

Gödel's first incompleteness theorem, abstractly. A `Theory` has sentences, a (meta-level) provability
predicate `Prov`, a semantic truth `True_`, negation, and two honest assumptions: **soundness** (`Prov s →
True_ s` — it only proves truths) and a **Gödel sentence** `G` with `True_ G ↔ ¬ Prov G` (G says "I am
unprovable"). That sentence is exactly what the diagonal lemma yields for the provability predicate; we
take its *existence* as a field, because producing it concretely is the arithmetisation (Gödel numbering of
a real theory like Q/PA) — the genuinely long part, scoped here.

From just these, `G` is **true but unprovable**, and so is its negation unprovable: the theory is
**incomplete**. The proof is the diagonal argument once more, now with provability substituted in.
-/
namespace Principia

/-- An abstract theory: provability, truth, negation, soundness, and a Gödel sentence. -/
structure Theory where
  Sentence : Type
  Prov : Sentence → Prop
  True_ : Sentence → Prop
  neg : Sentence → Sentence
  neg_true : ∀ s, True_ (neg s) ↔ ¬ True_ s
  /-- **soundness**: anything provable is true. -/
  sound : ∀ s, Prov s → True_ s
  /-- the **Gödel sentence** (the diagonal lemma applied to the provability predicate). -/
  goedel_sentence : ∃ G, True_ G ↔ ¬ Prov G

/-- **Abstract first incompleteness.** There is a sentence `G` that is true, unprovable, and whose negation
    is also unprovable — so the theory neither proves `G` nor refutes it. -/
theorem incompleteness (T : Theory) :
    ∃ G, ¬ T.Prov G ∧ T.True_ G ∧ ¬ T.Prov (T.neg G) := by
  obtain ⟨G, hG⟩ := T.goedel_sentence
  have hnp : ¬ T.Prov G := fun hp => (hG.mp (T.sound G hp)) hp     -- provable ⇒ true ⇒ unprovable: absurd
  have htrue : T.True_ G := hG.mpr hnp                              -- so it's unprovable, hence true
  exact ⟨G, hnp, htrue, fun hpn => (T.neg_true G).mp (T.sound _ hpn) htrue⟩   -- ¬G provable ⇒ G false: absurd

/-- A degenerate model (nothing provable) — witnesses that the `Theory` axioms are consistent, so
    `incompleteness` is not vacuous. -/
def trivialTheory : Theory where
  Sentence := Bool
  Prov _ := False
  True_ b := b = true
  neg := not
  neg_true s := by cases s <;> simp
  sound _ h := h.elim
  goedel_sentence := ⟨true, by simp⟩

end Principia
