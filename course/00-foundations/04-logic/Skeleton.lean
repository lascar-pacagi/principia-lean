/-!
# 04-logic — Skeleton  (THIS IS YOUR FILE)

Four theorems that are true *classically* but NOT provable by the constructive rules of `02-propositions`
alone. You'll need Lean's classical tools — `Classical.em` and `Classical.byContradiction`.
(`by_contra` is a Mathlib tactic and is NOT available here; use `Classical.byContradiction`.)

Run:  make lab C=00-foundations/04-logic
Try each cold. Stuck? See §6 "Prove it" and §7 "Hints for the skeleton" in `explainer.qmd`.
-/
set_option warningAsError true

namespace Course04

-- double-negation elimination
theorem dne (p : Prop) : ¬¬p → p := by
  sorry

-- the law of excluded middle (try to DERIVE it, rather than just citing `Classical.em`)
theorem em (p : Prop) : p ∨ ¬p := by
  sorry

-- Peirce's law: classically true, but it mentions no ¬ at all — a famous "purely implicational" classic
theorem peirce (p q : Prop) : ((p → q) → p) → p := by
  sorry

-- the classical half of De Morgan (the converse is constructive — see the exercises)
theorem not_and (p q : Prop) : ¬(p ∧ q) → ¬p ∨ ¬q := by
  sorry

end Course04
