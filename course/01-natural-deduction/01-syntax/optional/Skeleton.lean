import Principia.Logic.Syntax

/-! Optional exercises; see the lesson for hints and corrections. -/
set_option warningAsError true
open Principia Principia.Form
open scoped Principia.Form Principia
namespace Course1.Syntax

theorem three_le_size_imp (a b : Form) : 3 ≤ (a ⇒ b).size := by
  sorry

theorem top_size : Form.top.size = 3 := by
  sorry


end Course1.Syntax
