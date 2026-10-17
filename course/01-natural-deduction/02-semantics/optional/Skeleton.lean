import Principia.Logic.Semantics

/-! Optional exercises; see the lesson for hints and corrections. -/
set_option warningAsError true
open Principia Principia.Form
open scoped Principia.Form Principia
namespace Course1.Semantics

theorem eval_top (v : Nat → Bool) : eval v Form.top = true := by
  simp [Form.top, Form.neg, eval]

theorem taut_and_elim_left (a b : Form) : Tautology ((a ⋏ b) ⇒ a) := by
  intro v
  simp only [eval]
  cases eval v a <;> cases eval v b <;> rfl


end Course1.Semantics
