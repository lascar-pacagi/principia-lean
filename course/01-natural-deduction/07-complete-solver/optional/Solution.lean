import Principia.NatDed.Solver

/-! Optional exercises; see the lesson for hints and corrections. -/
set_option warningAsError true
open Principia Principia.Form
open scoped Principia.Form Principia
namespace Course1.Solver

theorem entails_from_solver (a b : Form)
    (h : (solve (a ⇒ b)).isValid = true) : Entails [a] b := by
  intro v hΓ
  have hi := solve_sound h v
  rw [eval_imp] at hi
  exact hi (hΓ a (by simp))

theorem solver_agrees_with_table (a : Form) : (solve a).isValid = taut? a := by
  cases ht : taut? a with
  | true =>
    exact solve_complete ((taut?_eq_true_iff a).mp ht)
  | false =>
    cases hs : (solve a).isValid with
    | false => rfl
    | true =>
      have ht' := (taut?_eq_true_iff a).mpr (solve_sound hs)
      rw [ht] at ht'
      contradiction

#print axioms entails_from_solver
#print axioms solver_agrees_with_table

end Course1.Solver
