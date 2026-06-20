import Principia.Euclid.Basic
import Principia.Euclid.Betweenness

/-!
# Principia.Euclid — Euclidean geometry from axioms (Course 4)

Synthetic geometry done honestly: the postulates are a `class` (`EuclidPlane`, extended to `EuclidPlane2`
with betweenness + the five-segment/SAS axiom), so theorems are parametric over any model and the hidden
assumptions (circle–circle continuity for I.1; SAS for the congruence theorems) are explicit. Independent
of the logic/SAT development. Aggregates the `Euclid.*` submodules.
-/
