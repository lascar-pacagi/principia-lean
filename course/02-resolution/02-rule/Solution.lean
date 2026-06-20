import Principia.Resolution.Cnf

/-!
# 02-rule — Solution  (verified answer key)

`make test` kernel-checks this (each refutation type-checks ⇒ it's a valid resolution proof of `□`).
Graduates into `Principia.Resolution.Rule`. Read to understand *why*, not to copy.
-/
namespace Principia

def Lit.neg (l : Lit) : Lit := { l with pol := !l.pol }
def resolvent (c d : Clause) (l : Lit) : Clause := c.erase l ++ d.erase l.neg

inductive Refut (S : Cnf) : Clause → Type
  | hyp {c} : c ∈ S → Refut S c
  | res {c d : Clause} (l : Lit) : Refut S c → Refut S d → Refut S (resolvent c d l)

-- resolve [+0] and [-0] on the literal +0: both erase to [], so the resolvent is □.
def refut1 : Refut [[⟨0, true⟩], [⟨0, false⟩]] [] :=
  .res ⟨0, true⟩ (.hyp (c := [⟨0, true⟩]) (by decide)) (.hyp (c := [⟨0, false⟩]) (by decide))

-- first resolve [+0,+1] with [-0] on +0  → [+1];  then resolve [+1] with [-1] on +1  → □.
def refut2 : Refut [[⟨0, true⟩, ⟨1, true⟩], [⟨0, false⟩], [⟨1, false⟩]] [] :=
  .res ⟨1, true⟩
    (.res ⟨0, true⟩ (.hyp (c := [⟨0, true⟩, ⟨1, true⟩]) (by decide)) (.hyp (c := [⟨0, false⟩]) (by decide)))
    (.hyp (c := [⟨1, false⟩]) (by decide))

/-! ## Checks (the kernel verifies each refutation just by type-checking it) -/

#check (refut1 : Refut [[⟨0, true⟩], [⟨0, false⟩]] [])
#eval resolvent [⟨0, true⟩, ⟨1, true⟩] [⟨0, false⟩] ⟨0, true⟩   -- ⇒ [+1]
#guard resolvent [⟨0, true⟩] [⟨0, false⟩] ⟨0, true⟩ == ([] : Clause)

end Principia
