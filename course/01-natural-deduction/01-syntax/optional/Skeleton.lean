import Principia.Logic.Syntax

/-! Optional exercises; see the lesson for hints and corrections. -/
set_option warningAsError true
open Principia Principia.Form
open scoped Principia.Form Principia
namespace Course1.Syntax

theorem three_le_size_imp (a b : Form) : 3 ≤ (a ⇒ b).size := by
  simp only [Form.size]
  have h1 : 1 ≤ a.size := by
    exact Form.size_pos a
  have h2 : 1 ≤ b.size := Form.size_pos b
  omega

theorem top_size : Form.top.size = 3 := by
  simp only [Form.top, Form.size_neg, Form.size]


end Course1.Syntax
