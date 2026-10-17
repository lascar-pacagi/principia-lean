import Principia.Logic.Syntax

/-! Optional exercises; see the lesson for hints and corrections. -/
set_option warningAsError true
open Principia Principia.Form
open scoped Principia.Form Principia
namespace Course1.Syntax

theorem three_le_size_imp (a b : Form) : 3 ≤ (a ⇒ b).size := by
  have ha := Form.size_pos a
  have hb := Form.size_pos b
  simp only [Form.size]
  omega

theorem top_size : Form.top.size = 3 := by
  rfl

#print axioms three_le_size_imp
#print axioms top_size

end Course1.Syntax
