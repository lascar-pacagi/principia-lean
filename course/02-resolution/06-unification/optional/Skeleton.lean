import Principia.FirstOrder

/-! See the explainer for worked steps and exercise corrections. -/
set_option warningAsError true
open Principia.FirstOrder
namespace Course2.Unification

theorem occurs_in_own_application :
    (Term.function 1 [.function 2 [], .function 3 [.variable 0]]).occurs 0 = true := by
  sorry

theorem binding_updates_earlier_rhs :
    (Substitution.bind ⟨[(0, .function 3 [.variable 1])]⟩
      1 (.function 2 [])).apply (.variable 0) = .function 3 [.function 2 []] := by
  sorry

end Course2.Unification
