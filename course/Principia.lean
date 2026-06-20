import Principia.Logic
import Principia.NatDed
import Principia.Resolution
import Principia.Sat
import Principia.Euclid
import Principia.Goedel

/-!
# Principia — a verified logic toolkit, built one course at a time

The accumulating artifact of this course. Modules graduate in as each course completes:

* `Principia.Logic`      — syntax & semantics (propositional + FOL): the shared spine
* `Principia.NatDed`     — natural-deduction system + prover            (Course 1)
* `Principia.Resolution` — CNF + resolution system + prover             (Course 2)
* `Principia.Sat`        — DPLL/CDCL + verified LRAT checker            (Course 3)
* `Principia.Euclid`     — Euclidean propositions (LeanEuclid)          (Course 4)
* `Principia.Goedel`     — diagonal lemma + abstract incompleteness     (Course 5)
-/
