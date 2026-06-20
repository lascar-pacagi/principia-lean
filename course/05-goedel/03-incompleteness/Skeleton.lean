import Principia.Goedel.Diagonal

/-!
# 03-incompleteness — Skeleton  (THIS IS YOUR FILE)

The `Theory` framework is GIVEN. Prove `incompleteness`: a sound theory with a Gödel sentence has a
sentence that is true, unprovable, and whose negation is unprovable too.

Run:  make lab C=05-goedel/03-incompleteness
Stuck? See §5 "Prove it" and §6 "Hints for the skeleton" in `explainer.qmd`.
-/
set_option warningAsError true
namespace Principia

structure Theory where
  Sentence : Type
  Prov : Sentence → Prop
  True_ : Sentence → Prop
  neg : Sentence → Sentence
  neg_true : ∀ s, True_ (neg s) ↔ ¬ True_ s
  sound : ∀ s, Prov s → True_ s
  goedel_sentence : ∃ G, True_ G ↔ ¬ Prov G

-- Gödel I: there is a true, unprovable sentence whose negation is also unprovable (so the theory is incomplete).
theorem incompleteness (T : Theory) :
    ∃ G, ¬ T.Prov G ∧ T.True_ G ∧ ¬ T.Prov (T.neg G) := by
  sorry

end Principia
