/-!
# 00-setup — Skeleton  (THIS IS YOUR FILE)

Replace each `sorry` with a real proof, then run:  make lab C=00-foundations/00-setup
The line below makes a leftover `sorry` a hard error — that's the RED you turn GREEN.

Try each goal cold first. Stuck? The lesson has §9 "Prove it" and §10 "Hints for the skeleton" —
read `explainer.qmd` (or its rendered `explainer.html` / `explainer.pdf`).
-/
set_option warningAsError true

namespace Setup

theorem and_reorder (p q r : Prop) (h : p ∧ (q ∧ r)) : q ∧ (p ∧ r) := by
  apply And.intro
  . exact h.2.1
  . apply And.intro
    . exact h.1
    . exact h.2.2


theorem sum_lt : 3 + 4 < 5 + 3 := by
  decide

theorem one_add' (n : Nat) : 1 + n = n + 1 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]

end Setup
