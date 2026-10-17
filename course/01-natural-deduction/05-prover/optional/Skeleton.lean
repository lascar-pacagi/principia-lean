import Principia.NatDed.Prover

/-! Optional exercises; see the lesson for hints and corrections. -/
set_option warningAsError true
open Principia Principia.Form
open scoped Principia.Form Principia
namespace Course1.Search

theorem certify_constant : Tautology (Form.var 0 ⇒ (Form.var 1 ⇒ Form.var 0)) := by
  sorry

theorem search_misses_projection :
    (prove ((Form.var 0 ⋏ Form.var 1) ⇒ Form.var 1)).isSome = false ∧
      Tautology ((Form.var 0 ⋏ Form.var 1) ⇒ Form.var 1) := by
  sorry


end Course1.Search
