import Principia.NatDed.Kalmar
import Principia.NatDed.Soundness

/-!
# 06-completeness — Your exercises

Run: make lab C=01-natural-deduction/06-completeness
See §6 for statements, §7 for hints, and §8 for worked corrections.
Optional exercises have their own skeleton and answer key under optional/.
-/
set_option warningAsError true
open scoped Principia.Form Principia

namespace Principia.Form

def completeness {φ : Form} (h : Tautology φ) : [] ⊢ φ := by
  sorry

theorem provable_iff_tautology {φ : Form} : Nonempty ([] ⊢ φ) ↔ Tautology φ := by
  sorry

end Principia.Form
