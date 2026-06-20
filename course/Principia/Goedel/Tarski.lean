import Principia.Goedel.Diagonal

/-!
# Principia.Goedel.Tarski — undefinability of truth (Course 5, slice 5.2)

Tarski's theorem: **no language can define its own truth predicate.** We model a language abstractly as a
type of sentences with a semantic truth predicate `True_`, a negation, a notion of which predicates are
`Definable` (expressible inside the language), and — crucially — a **diagonal lemma** (every definable
predicate has a self-referential fixed-point sentence). Then `True_` itself is *not* definable: if it were,
so would be its negation, and the diagonal lemma would manufacture a Liar sentence `True_ s ↔ ¬ True_ s` —
impossible by `no_self_neg`. This is the diagonal argument (5.1) with a truth predicate substituted in.
-/
namespace Principia

/-- A language with a semantics: sentences, truth, negation, a class of definable predicates closed under
    negation, and the diagonal lemma for definable predicates. -/
structure Lang where
  Sentence : Type
  True_ : Sentence → Prop
  neg : Sentence → Sentence
  neg_true : ∀ s, True_ (neg s) ↔ ¬ True_ s
  Definable : (Sentence → Prop) → Prop
  neg_def : ∀ P, Definable P → Definable (fun s => ¬ P s)
  /-- **diagonal lemma**: every definable predicate `P` has a sentence asserting `P` of itself. -/
  diagonal : ∀ P, Definable P → ∃ s, True_ s ↔ P s

/-- **Tarski's undefinability of truth.** The truth predicate of a language is not definable within it. -/
theorem tarski (L : Lang) : ¬ L.Definable L.True_ := by
  intro hdef
  have hnd : L.Definable (fun s => ¬ L.True_ s) := L.neg_def _ hdef     -- ¬truth would be definable
  obtain ⟨s, hs⟩ := L.diagonal _ hnd                                     -- the Liar: True_ s ↔ ¬ True_ s
  exact no_self_neg ⟨_, hs⟩

end Principia
