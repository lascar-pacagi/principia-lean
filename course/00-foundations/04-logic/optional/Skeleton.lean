/-!
# 04-logic — Optional practice

Run: make lab C=00-foundations/04-logic
See §9 for statements and hints, and §10 for worked corrections.
-/
set_option warningAsError true

namespace Course04.Optional

theorem not_and_converse (p q : Prop) : (¬p ∨ ¬q) → ¬(p ∧ q) := by
  sorry

theorem not_imp (p q : Prop) : ¬(p → q) → p ∧ ¬q := by
  sorry

end Course04.Optional
