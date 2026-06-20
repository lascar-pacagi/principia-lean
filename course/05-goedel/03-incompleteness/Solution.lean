import Principia.Goedel.Diagonal

/-!
# 03-incompleteness — Solution  (verified answer key)

`make test` kernel-checks this; `make axioms` audits it. Graduates into `Principia.Goedel.Incompleteness`.
-/
namespace Principia

structure Theory where
  Sentence : Type
  Prov : Sentence → Prop
  True_ : Sentence → Prop
  neg : Sentence → Sentence
  neg_true : ∀ s, True_ (neg s) ↔ ¬ True_ s
  sound : ∀ s, Prov s → True_ s
  goedel_sentence : ∃ G, True_ G ↔ ¬ Prov G

-- if G were provable it'd be true (soundness) hence unprovable — absurd; so G is unprovable, hence true;
-- and if ¬G were provable, ¬G would be true, contradicting G's truth.
theorem incompleteness (T : Theory) :
    ∃ G, ¬ T.Prov G ∧ T.True_ G ∧ ¬ T.Prov (T.neg G) := by
  obtain ⟨G, hG⟩ := T.goedel_sentence
  have hnp : ¬ T.Prov G := fun hp => (hG.mp (T.sound G hp)) hp
  have htrue : T.True_ G := hG.mpr hnp
  exact ⟨G, hnp, htrue, fun hpn => (T.neg_true G).mp (T.sound _ hpn) htrue⟩

/-! ## Checks (consistency model + honesty audit)

A degenerate theory (nothing provable) is a model, so the `Theory` axioms are consistent and
`incompleteness` is not vacuous. -/

def trivialTheory : Theory where
  Sentence := Bool
  Prov _ := False
  True_ b := b = true
  neg := not
  neg_true s := by cases s <;> simp
  sound _ h := h.elim
  goedel_sentence := ⟨true, by simp⟩

#print axioms incompleteness   -- (none)

end Principia
