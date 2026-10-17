/-!
# 04-logic — Optional solutions

See §10 for worked explanations.
`make test` checks these proofs; `make axioms` audits them.
-/
set_option warningAsError true

namespace Course04.Optional

theorem not_and_converse (p q : Prop) : (¬p ∨ ¬q) → ¬(p ∧ q) := by
  intro hnot
  intro hpq
  cases hnot with
  | inl hnp =>
    exact hnp hpq.1
  | inr hnq =>
    exact hnq hpq.2

theorem not_imp (p q : Prop) : ¬(p → q) → p ∧ ¬q := by
  intro hnotImp
  constructor
  · apply Classical.byContradiction
    intro hnp
    have hpq : p → q := by
      intro hp
      exact False.elim (hnp hp)
    exact hnotImp hpq
  · intro hq
    have hpq : p → q := by
      intro hp
      exact hq
    exact hnotImp hpq

/-! ## Checks — compare a constructive and a classical proof -/
#print axioms not_and_converse
#print axioms not_imp

end Course04.Optional
