import Principia.Sat.Basic
import Principia.Sat.Dpll
import Principia.Sat.Cdcl
import Principia.Sat.Lrat

/-!
# Principia.Sat — DPLL/CDCL solvers + verified LRAT checker (Course 3)

Three pieces of a SAT toolkit, reusing `Resolution.Cnf`:
* `Sat.Dpll` — DPLL search, **model-sound** (a returned model satisfies the CNF);
* `Sat.Cdcl` — a CDCL solver (clause learning + backjumping), **unverified** (differential-tested);
* `Sat.Lrat` — a **verified** UNSAT-certificate checker (`check proof cnf → cnf.Unsat`).

The trustworthy-UNSAT pipeline: run a fast (untrusted) solver like `cdcl`, and trust its UNSAT verdict
only via a certificate validated by the verified `Sat.Lrat.check`.
-/
