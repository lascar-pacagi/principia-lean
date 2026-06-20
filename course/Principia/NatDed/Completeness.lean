import Principia.NatDed.Kalmar
import Principia.NatDed.Soundness

/-!
# Principia.NatDed.Completeness — completeness (Course 1, slice 1.6)

`Γ ⊨ φ → Γ ⊢ φ` for the closed case, assembled from `Kalmar.kalmar` and `Kalmar.elim`. Together with
`Soundness.soundness` it closes the loop **`⊢ ⟺ ⊨`** (`provable_iff_tautology`).
-/
namespace Principia.Form

open scoped Principia.Form Principia

/-- **Completeness** (closed case): every tautology has a closed derivation.
    For each valuation, Kalmár's lemma gives a proof from that valuation's literals; `elim` collapses
    all of them to the empty context. -/
noncomputable def completeness {φ : Form} (h : Tautology φ) : [] ⊢ φ :=
  elim φ.maxVar φ (fun v => (kalmar v φ.maxVar φ (Nat.le_refl _)).1 (h v))

/-- **The loop closes**: provability and validity coincide. (`mp` is soundness, `mpr` completeness.) -/
theorem provable_iff_tautology {φ : Form} : Nonempty ([] ⊢ φ) ↔ Tautology φ :=
  ⟨fun ⟨d⟩ => tautology_of_proof d, fun h => ⟨completeness h⟩⟩

end Principia.Form
