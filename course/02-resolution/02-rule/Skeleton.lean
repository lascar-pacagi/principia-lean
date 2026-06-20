import Principia.Resolution.Cnf

/-!
# 02-rule — Skeleton  (THIS IS YOUR FILE)

`Lit.neg`, `resolvent`, and the `Refut` derivation type are GIVEN. Build the two refutations (resolution
derivations of the empty clause `□ = []`) by replacing each `sorry`.

Tip: name each hypothesis clause — `Refut.hyp (c := <the clause>) (by decide)`. Resolving two
complementary unit clauses (`[l]` and `[∼l]`) yields `□`.

Run:  make lab C=02-resolution/02-rule
Stuck? See §5 "Prove it" and §6 "Hints for the skeleton" in `explainer.qmd`.
-/
set_option warningAsError true

namespace Principia

def Lit.neg (l : Lit) : Lit := { l with pol := !l.pol }
def resolvent (c d : Clause) (l : Lit) : Clause := c.erase l ++ d.erase l.neg

inductive Refut (S : Cnf) : Clause → Type
  | hyp {c} : c ∈ S → Refut S c
  | res {c d : Clause} (l : Lit) : Refut S c → Refut S d → Refut S (resolvent c d l)

/-! Build these two refutations. -/

-- {p, ¬p}: resolve the two unit clauses to get □.
def refut1 : Refut [[⟨0, true⟩], [⟨0, false⟩]] [] :=
  sorry

-- {p ∨ q, ¬p, ¬q}: resolve (p∨q) with ¬p to get q, then q with ¬q to get □.
def refut2 : Refut [[⟨0, true⟩, ⟨1, true⟩], [⟨0, false⟩], [⟨1, false⟩]] [] :=
  sorry

end Principia
