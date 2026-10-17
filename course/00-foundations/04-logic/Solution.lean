/-!
# 04-logic — Verified solutions

The worked explanations are in §8 of the explainer.
`make test` checks these proofs; `make axioms` audits their dependencies.
-/
set_option warningAsError true

namespace Course04

theorem double_negation_elimination (p : Prop) : ¬¬p → p := by
  intro hnnp
  apply Classical.byContradiction
  intro hnp
  exact hnnp hnp

theorem excluded_middle (p : Prop) : p ∨ ¬p := by
  apply Classical.byContradiction
  intro hneither
  have hnp : ¬p := by
    intro hp
    have hor : p ∨ ¬p := Or.inl hp
    exact hneither hor
  have hor : p ∨ ¬p := Or.inr hnp
  exact hneither hor

theorem peirce (p q : Prop) : ((p → q) → p) → p := by
  intro h
  apply Classical.byContradiction
  intro hnp
  have hpq : p → q := by
    intro hp
    exact False.elim (hnp hp)
  have hp : p := h hpq
  exact hnp hp

theorem not_and (p q : Prop) : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro hnotBoth
  cases Classical.em p with
  | inl hp =>
    right
    intro hq
    exact hnotBoth ⟨hp, hq⟩
  | inr hnp =>
    left
    exact hnp

theorem truth_table_counterexample :
    ∃ a b : Bool, ((!(a || b)) || (a && b)) = false := by
  exact ⟨true, false, rfl⟩

theorem truth_table_not_valid :
    ¬(∀ a b : Bool, ((!(a || b)) || (a && b)) = true) := by
  intro hAll
  obtain ⟨a, b, hRow⟩ := truth_table_counterexample
  have hTrue : ((!(a || b)) || (a && b)) = true := hAll a b
  rw [hRow] at hTrue
  contradiction

/-! ## Checks — finite Boolean computation and proof dependencies -/

example : ∀ a b : Bool, (!(a && b)) = ((!a) || (!b)) := by
  decide
example : ∀ a : Bool, (a || !a) = true := by
  decide

#guard ((!true) || false) = false
#guard ((!false) || false) = true

#print axioms double_negation_elimination
#print axioms excluded_middle
#print axioms peirce
#print axioms not_and
#print axioms truth_table_counterexample
#print axioms truth_table_not_valid

end Course04
