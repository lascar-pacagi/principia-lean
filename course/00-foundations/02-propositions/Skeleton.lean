/-!
# 02-propositions — Skeleton  (THIS IS YOUR FILE)

One theorem per connective. Replace each `sorry`. All are constructive (no classical logic needed).

Run:  make lab C=00-foundations/02-propositions
Try each cold. Stuck? See §5 "Prove it" and §6 "Hints for the skeleton" in `explainer.qmd`.
-/
set_option warningAsError true

namespace Course02

-- → : chain two implications.
theorem imp_trans (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r := by
  sorry

-- ∧ : take a conjunction apart and rebuild it the other way.
theorem and_reassoc (p q r : Prop) (h : p ∧ (q ∧ r)) : (p ∧ q) ∧ r := by
  sorry

-- ∨ : a disjunction could have been built either way — handle both.
theorem or_comm' (p q : Prop) (h : p ∨ q) : q ∨ p := by
  sorry

-- ¬ : recall `¬p` is `p → False`. (Constructive direction of the contrapositive.)
theorem contrapositive (p q : Prop) (h : p → q) : ¬q → ¬p := by
  sorry

-- ↔ : an iff is a pair of implications.
theorem iff_symm (p q : Prop) (h : p ↔ q) : q ↔ p := by
  sorry

-- ∀ / ∃ : feed a universal fact through an existential witness.
theorem exists_imp (α : Type) (p q : α → Prop)
    (h : ∀ x, p x → q x) (hex : ∃ x, p x) : ∃ x, q x := by
  sorry

end Course02
