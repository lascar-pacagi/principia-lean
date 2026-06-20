import Principia.Goedel.Diagonal
import Principia.Goedel.Tarski
import Principia.Goedel.Incompleteness

/-!
# Principia.Goedel — the abstract heart of incompleteness (Course 5)

The logical core of Gödel's theorems, built abstractly (no arithmetization): the **diagonal argument**
(`Goedel.Diagonal` — Lawvere/Cantor), Tarski's **undefinability of truth** (`Goedel.Tarski`), and the
abstract **first incompleteness theorem** (`Goedel.Incompleteness`). The one ingredient that genuinely
needs Gödel numbering — the *diagonal lemma* producing a self-referential sentence — is taken as an
explicit hypothesis, so the famous consequences are derived cleanly and honestly. Aggregates the
`Goedel.*` submodules.
-/
