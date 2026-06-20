import Principia.Goedel.Diagonal

/-!
# 02-tarski — Skeleton  (THIS IS YOUR FILE)

The `Lang` framework is GIVEN (and `no_self_neg` is imported from 5.1). Prove `tarski`: the truth
predicate of a language is not definable within it.

Run:  make lab C=05-goedel/02-tarski
Stuck? See §5 "Prove it" and §6 "Hints for the skeleton" in `explainer.qmd`.
-/
set_option warningAsError true
namespace Principia

structure Lang where
  Sentence : Type
  True_ : Sentence → Prop
  neg : Sentence → Sentence
  neg_true : ∀ s, True_ (neg s) ↔ ¬ True_ s
  Definable : (Sentence → Prop) → Prop
  neg_def : ∀ P, Definable P → Definable (fun s => ¬ P s)
  diagonal : ∀ P, Definable P → ∃ s, True_ s ↔ P s

-- Tarski: truth is not definable. (If it were, ¬truth would be too; the diagonal lemma then builds a Liar.)
theorem tarski (L : Lang) : ¬ L.Definable L.True_ := by
  sorry

end Principia
