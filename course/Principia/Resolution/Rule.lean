import Principia.Resolution.Cnf

/-!
# Principia.Resolution.Rule — the resolution rule and refutations (Course 2, slice 2.2)

The resolution rule: from a clause containing literal `l` and another containing its complement `∼l`,
derive their **resolvent** (drop the two complementary literals, union the rest). A `Refut S c` is a
resolution derivation of clause `c` from the clause set `S`; a **refutation** of `S` is a derivation of
the empty clause `□ = []`, witnessing that `S` is unsatisfiable (slice 2.4).
-/
namespace Principia

/-- The complementary literal. -/
def Lit.neg (l : Lit) : Lit := { l with pol := !l.pol }

/-- Resolvent of `c` and `d` on `l`: drop `l` from `c`, drop `∼l` from `d`, concatenate the rest.
    (Resolving two complementary unit clauses gives `□`.) -/
def resolvent (c d : Clause) (l : Lit) : Clause := c.erase l ++ d.erase l.neg

/-- A resolution derivation of a clause from `S`: a hypothesis clause, or a resolvent of two derivations.
    `Refut S []` is a *refutation* of `S`. -/
inductive Refut (S : Cnf) : Clause → Type
  /-- use a clause already in `S` -/
  | hyp {c} : c ∈ S → Refut S c
  /-- resolve two derived clauses on a literal `l` -/
  | res {c d : Clause} (l : Lit) : Refut S c → Refut S d → Refut S (resolvent c d l)

/-- `S` is refutable when the empty clause is derivable from it. -/
def Cnf.Refutable (S : Cnf) : Prop := Nonempty (Refut S [])

end Principia
