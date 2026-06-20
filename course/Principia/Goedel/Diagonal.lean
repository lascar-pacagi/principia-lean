/-!
# Principia.Goedel.Diagonal — the diagonal argument, once and for all (Course 5, slice 5.1)

Cantor, Russell, the Liar, Tarski, Gödel, and Turing are *the same argument*. Lawvere isolated it: a
**point-surjective** map `e : A → (A → B)` forces every `g : B → B` to have a **fixed point**. Read
contrapositively (pick a `g` with no fixed point), it says certain surjections cannot exist — which is
Cantor; specialised to provability it becomes Gödel (slice 5.3), and to truth, Tarski (slice 5.2).

Everything here is concrete and (almost) axiom-free — the diagonal is pure λ-calculus.
-/
namespace Principia

/-- **Lawvere's fixed-point theorem.** If every `f : A → B` arises as `e a` for some `a` (point
    surjectivity), then every `g : B → B` has a fixed point. The proof *is* the diagonal: feed
    `fun x => g (e x x)` through the surjection. -/
theorem lawvere {A B : Type} (e : A → A → B) (he : ∀ f : A → B, ∃ a, e a = f) (g : B → B) :
    ∃ b, g b = b := by
  obtain ⟨a, ha⟩ := he (fun x => g (e x x))     -- e a = (fun x => g (e x x))
  exact ⟨e a a, (congrFun ha a).symm⟩           -- e a a = g (e a a), so `e a a` is fixed by g

/-- **Cantor's theorem.** No map `A → (A → Bool)` is point-surjective: Boolean negation has no fixed
    point, so by Lawvere no such surjection can exist. (`A → Bool` is the "power set" of `A`.) -/
theorem cantor {A : Type} (e : A → A → Bool) : ¬ (∀ f : A → Bool, ∃ a, e a = f) := by
  intro he
  obtain ⟨b, hb⟩ := lawvere e he (fun x => !x)
  cases b <;> simp at hb

/-- The propositional heart shared by the Liar paradox, Russell's paradox, Tarski, and Gödel:
    **no proposition is equivalent to its own negation.** -/
theorem no_self_neg : ¬ ∃ p : Prop, p ↔ ¬ p := by
  rintro ⟨p, hp⟩
  have hnp : ¬ p := fun h => hp.mp h h
  exact hnp (hp.mpr hnp)

end Principia
