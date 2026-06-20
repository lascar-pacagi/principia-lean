/-!
# 01-diagonal — Skeleton  (THIS IS YOUR FILE)

Prove the three faces of the diagonal argument: `lawvere` (the engine), `cantor` (a corollary), and
`no_self_neg` (the propositional heart).

Run:  make lab C=05-goedel/01-diagonal
Stuck? See §5 "Prove it" and §6 "Hints for the skeleton" in `explainer.qmd`.
-/
set_option warningAsError true
namespace Principia

-- Lawvere: a point-surjective `e : A → (A → B)` forces every `g : B → B` to have a fixed point.
theorem lawvere {A B : Type} (e : A → A → B) (he : ∀ f : A → B, ∃ a, e a = f) (g : B → B) :
    ∃ b, g b = b := by
  sorry

-- Cantor: no `e : A → (A → Bool)` is point-surjective.
theorem cantor {A : Type} (e : A → A → Bool) : ¬ (∀ f : A → Bool, ∃ a, e a = f) := by
  sorry

-- the propositional heart: no proposition is equivalent to its own negation.
theorem no_self_neg : ¬ ∃ p : Prop, p ↔ ¬ p := by
  sorry

end Principia
