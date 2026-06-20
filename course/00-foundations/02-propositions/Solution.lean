/-!
# 02-propositions — Solution  (verified answer key)

`make test` kernel-checks this; `make axioms` audits the keystones. Read to understand *why*, not to copy.
-/
namespace Course02

-- → : a proof of an implication is a function; `intro` assumes, application uses.
theorem imp_trans (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r := by
  intro hp
  exact hqr (hpq hp)

-- ∧ : `obtain ⟨…⟩` destructures; `⟨…⟩` builds.
theorem and_reassoc (p q r : Prop) (h : p ∧ (q ∧ r)) : (p ∧ q) ∧ r := by
  obtain ⟨hp, hq, hr⟩ := h
  exact ⟨⟨hp, hq⟩, hr⟩

-- ∨ : `cases` splits on which constructor was used; `Or.inl`/`Or.inr` build.
theorem or_comm' (p q : Prop) (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

-- ¬ : `¬q` is `q → False`; introduce both arrows, then derive `False`.
theorem contrapositive (p q : Prop) (h : p → q) : ¬q → ¬p := by
  intro hnq hp
  exact hnq (h hp)

-- ↔ : `constructor` asks for both directions; `.mp` / `.mpr` extract them.
theorem iff_symm (p q : Prop) (h : p ↔ q) : q ↔ p := by
  constructor
  · exact h.mpr
  · exact h.mp

-- ∀ / ∃ : `obtain ⟨x, hx⟩` opens the existential; `⟨x, …⟩` builds a new one.
theorem exists_imp (α : Type) (p q : α → Prop)
    (h : ∀ x, p x → q x) (hex : ∃ x, p x) : ∃ x, q x := by
  obtain ⟨x, hpx⟩ := hex
  exact ⟨x, h x hpx⟩

/-! ## Checks (Tier-2 computational + honesty audit)

For arbitrary `p q : Prop` we had to *prove* the theorems above. But statements over a *finite,
decidable* domain can instead be **checked by computation** — a first taste of the truth-table
semantics we'll build a prover around in Course 1. -/

example : ∀ a b : Bool, (a && b) = (b && a) := by decide   -- the machine checks the truth table
#guard (true && false) == false

#print axioms imp_trans
#print axioms or_comm'
#print axioms exists_imp

end Course02
