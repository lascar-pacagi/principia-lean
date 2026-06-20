import Principia.Resolution.Cnf
import Principia.Resolution.Rule
import Principia.Resolution.Prover
import Principia.Resolution.Soundness
import Principia.Resolution.Completeness

/-!
# Principia.Resolution — CNF + resolution system + prover (Course 2)

Prover #2: CNF conversion (`Resolution.Cnf`), the resolution rule and refutations (`Resolution.Rule`),
the saturation prover (`Resolution.Prover`), soundness (`Resolution.Soundness`), and the verified
decision direction + tie to Course 1 (`Resolution.Completeness`). Full refutation-completeness is the
flagged hard keystone (see `Resolution.Completeness`). Aggregates the `Resolution.*` submodules.
-/
