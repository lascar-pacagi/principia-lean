import Principia.Goedel.Diagonal

/-!
# 02-tarski — Solution  (verified answer key)

`make test` kernel-checks this; `make axioms` audits it. Graduates into `Principia.Goedel.Tarski`.
-/
namespace Principia

structure Lang where
  Sentence : Type
  True_ : Sentence → Prop
  neg : Sentence → Sentence
  neg_true : ∀ s, True_ (neg s) ↔ ¬ True_ s
  Definable : (Sentence → Prop) → Prop
  neg_def : ∀ P, Definable P → Definable (fun s => ¬ P s)
  diagonal : ∀ P, Definable P → ∃ s, True_ s ↔ P s

-- if `True_` were definable, so is `¬True_`; the diagonal lemma then yields `True_ s ↔ ¬ True_ s`.
theorem tarski (L : Lang) : ¬ L.Definable L.True_ := by
  intro hdef
  have hnd : L.Definable (fun s => ¬ L.True_ s) := L.neg_def _ hdef
  obtain ⟨s, hs⟩ := L.diagonal _ hnd
  exact no_self_neg ⟨_, hs⟩

/-! ## Checks (honesty audit) -/

#print axioms tarski   -- (none)

end Principia
