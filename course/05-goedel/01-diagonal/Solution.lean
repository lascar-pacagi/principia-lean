/-!
# 01-diagonal — Solution  (verified answer key)

`make test` kernel-checks this; `make axioms` audits it. Graduates into `Principia.Goedel.Diagonal`.
-/
namespace Principia

-- feed the "diagonal" function `fun x => g (e x x)` through the surjection, then evaluate at the witness.
theorem lawvere {A B : Type} (e : A → A → B) (he : ∀ f : A → B, ∃ a, e a = f) (g : B → B) :
    ∃ b, g b = b := by
  obtain ⟨a, ha⟩ := he (fun x => g (e x x))
  exact ⟨e a a, (congrFun ha a).symm⟩

-- Boolean negation has no fixed point, so by `lawvere` no point-surjection onto `A → Bool` exists.
theorem cantor {A : Type} (e : A → A → Bool) : ¬ (∀ f : A → Bool, ∃ a, e a = f) := by
  intro he
  obtain ⟨b, hb⟩ := lawvere e he (fun x => !x)
  cases b <;> simp at hb

theorem no_self_neg : ¬ ∃ p : Prop, p ↔ ¬ p := by
  rintro ⟨p, hp⟩
  have hnp : ¬ p := fun h => hp.mp h h
  exact hnp (hp.mpr hnp)

/-! ## Checks (honesty audit) -/

#print axioms lawvere       -- (none)
#print axioms cantor        -- propext
#print axioms no_self_neg   -- (none)

end Principia
