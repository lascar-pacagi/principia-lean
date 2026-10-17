/-!
# 04-logic — Optional practice

Run: make lab C=00-foundations/04-logic
See §9 for statements and hints, and §10 for worked corrections.
-/
set_option warningAsError true

namespace Course04.Optional

theorem not_and_converse (p q : Prop) : (¬p ∨ ¬q) → ¬(p ∧ q) := by
  intro hnpornq
  intro hpq
  cases hnpornq with
  | inl hnp =>
    exact hnp hpq.1
  | inr hnq =>
    exact hnq hpq.2

theorem not_imp (p q : Prop) : ¬(p → q) → p ∧ ¬q := by
  intro h1
  apply And.intro
  . apply Classical.byContradiction
    intro hnp
    have hnpoq : ¬p∨q := Or.inl hnp
    have hpiq : p→q := by
      intro hp
      contradiction
    exact h1 hpiq
  . intro hq
    have hpiq : p→q := by
      intro hp
      exact hq
    exact h1 hpiq

end Course04.Optional
