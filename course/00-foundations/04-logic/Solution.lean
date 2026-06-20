/-!
# 04-logic — Solution  (verified answer key)

`make test` kernel-checks this; `make axioms` audits the keystones. These DO depend on `Classical.choice`
— that is the lesson, not a leak. Read to understand *why*, not to copy.
-/
namespace Course04

-- `Classical.byContradiction : ¬¬p → p` is the classical engine. Here it *is* the proof.
theorem dne (p : Prop) : ¬¬p → p := by
  intro h
  exact Classical.byContradiction h

-- Excluded middle, DERIVED from by-contradiction: assume `¬(p ∨ ¬p)`; then `p` would let us build the
-- left side, so `¬p`; but that builds the right side — contradiction.
theorem em (p : Prop) : p ∨ ¬p := by
  apply Classical.byContradiction
  intro h
  exact h (Or.inr (fun hp => h (Or.inl hp)))

-- Peirce: assume `¬p`; then `p → q` holds vacuously, so `h` hands us `p` — contradiction.
theorem peirce (p q : Prop) : ((p → q) → p) → p := by
  intro h
  apply Classical.byContradiction
  intro hnp
  exact hnp (h (fun hp => absurd hp hnp))

-- classical De Morgan: split on `p ∨ ¬p`.
theorem not_and (p q : Prop) : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h
  cases Classical.em p with
  | inl hp  => exact Or.inr (fun hq => h ⟨hp, hq⟩)
  | inr hnp => exact Or.inl hnp

/-! ## Checks (Tier-2 computational + honesty audit)

Propositional logic has *semantics*: a formula's truth is a function of its variables' truth values,
and a tautology is true under **every** valuation. Over `Bool` that's a finite check `decide` can run —
the truth-table decision procedure we'll formalize in Course 1. -/

example : ∀ a b : Bool, (!(a && b)) = ((!a) || (!b)) := by decide   -- De Morgan, by truth table
#guard decide (∀ p : Bool, p || !p)                                  -- excluded middle, by truth table

#print axioms dne       -- depends on Classical.choice (accepted) — never sorryAx
#print axioms em
#print axioms peirce
#print axioms not_and

end Course04
