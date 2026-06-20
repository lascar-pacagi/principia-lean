import Principia.NatDed.Basic
import Principia.NatDed.Soundness
import Principia.NatDed.Prover
import Principia.NatDed.Kalmar
import Principia.NatDed.Completeness

/-!
# Principia.NatDed — natural-deduction system + prover (Course 1)

Prover #1: the inductive derivation relation `Γ ⊢ φ`, proof search, and the soundness / completeness
metatheory — closing the loop `⊢ ⟺ ⊨`. Aggregates the `NatDed.*` submodules.
-/
