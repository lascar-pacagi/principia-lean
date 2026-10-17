import Principia.NatDed.Solver

/-! Optional exercises; see the lesson for hints and corrections. -/
set_option warningAsError true
open Principia Principia.Form
open scoped Principia.Form Principia
namespace Course1.Solver

theorem entails_from_solver (a b : Form)
    (h : (solve (a ⇒ b)).isValid = true) : Entails [a] b := by
  sorry

theorem solver_agrees_with_table (a : Form) : (solve a).isValid = taut? a := by
  sorry


end Course1.Solver
