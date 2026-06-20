/-!
# 00-setup — Skeleton  (THIS IS YOUR FILE)

Replace each `sorry` with a real proof, then run:  make lab C=00-foundations/00-setup
The line below makes a leftover `sorry` a hard error — that's the RED you turn GREEN.

Try each goal cold first. Stuck? The lesson has §9 "Prove it" and §10 "Hints for the skeleton" —
read `explainer.qmd` (or its rendered `explainer.html` / `explainer.pdf`).
-/
set_option warningAsError true

namespace Setup

theorem and_swap (p q : Prop) (h : p ∧ q) : q ∧ p := by
  sorry

theorem two_plus_two : 2 + 2 = 4 := by
  sorry

theorem zero_add' (n : Nat) : 0 + n = n := by
  sorry

end Setup
