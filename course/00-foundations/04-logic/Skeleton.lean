/-!
# 04-logic — Your exercises

Run: make lab C=00-foundations/04-logic
See §6 for statements, §7 for hints, and §8 for worked corrections.
Optional exercises are in optional/Skeleton.lean and are reported separately.
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
  intro neither
  have hnp : ¬p := by
    intro hp
    apply neither (Or.inl hp)
  apply neither (Or.inr hnp)


theorem peirce (p q : Prop) : ((p → q) → p) → p := by
  intro hpqp
  apply Classical.byContradiction
  intro hnp
  have hpq : p → q := by
    intro hp
    exfalso
    exact hnp hp
  have hp : p := hpqp hpq
  exact hnp hp


theorem not_and (p q : Prop) : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro hnpq
  cases Classical.em q with
  | inl hq =>
    cases Classical.em p with
    | inl hp =>
      exfalso
      exact hnpq ⟨ hp, hq ⟩
    | inr hnp => exact Or.inl hnp
  | inr hnq =>
    exact Or.inr hnq

theorem truth_table_counterexample :
    ∃ a b : Bool, ((!(a || b)) || (a && b)) = false := by
  refine ⟨true, ?_⟩
  refine ⟨false, ?_⟩
  rfl

theorem truth_table_not_valid :
    ¬(∀ a b : Bool, ((!(a || b)) || (a && b)) = true) := by
  intro h
  have hrow : false = true := h false true
  contradiction

end Course04
