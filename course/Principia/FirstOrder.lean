import Principia.FirstOrder.Syntax
import Principia.FirstOrder.Semantics
import Principia.FirstOrder.NaturalDeduction
import Principia.FirstOrder.NaturalDeductionSearch
import Principia.FirstOrder.Resolution
import Principia.FirstOrder.Unification
import Principia.FirstOrder.ResolutionSearch
import Principia.FirstOrder.NaturalDeductionCompleteness
import Principia.FirstOrder.ResolutionCompleteness
import Principia.FirstOrder.Clausification

/-!
# First-order extension shared by natural deduction and resolution

Terms, capture-avoiding substitution, arbitrary-domain semantics, both proof systems and their
soundness theorems, checked unification, factoring and bounded proof-producing searches.
Each stage terminates; a failed stage is unknown. Both calculi have general first-order
completeness theorems. The executable Skolem pass preserves satisfiability via a general same-domain model-expansion
and recovery proof. The clausal frontend needs only the returned resolution refutation.
-/
