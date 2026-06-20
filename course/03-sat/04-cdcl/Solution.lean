import Principia.Sat.Dpll

/-!
# 04-cdcl — Solution  (verified-to-build answer key)

`make test` builds this and runs the differential `#guard`s (the solver is unverified, so the `#guard`s
*are* the correctness check). Graduates into `Principia.Sat.Cdcl`.
-/
namespace Principia

structure TEntry where
  lit    : Lit
  level  : Nat
  reason : Option Clause
deriving Repr
abbrev Trail := List TEntry

def assignedTrue (t : Trail) (l : Lit) : Bool := t.any (fun e => decide (e.lit = l))
def isUnassigned (t : Trail) (l : Lit) : Bool := !assignedTrue t l && !assignedTrue t l.neg

inductive CStatus | sat | conflict | unit (l : Lit) | open_

-- satisfied if any literal is true; else look at the unassigned literals: none ⇒ conflict, one ⇒ unit,
-- otherwise still open.
def clauseStatus (t : Trail) (c : Clause) : CStatus :=
  if c.any (fun l => assignedTrue t l) then .sat
  else match c.filter (fun l => isUnassigned t l) with
    | []  => .conflict
    | [l] => .unit l
    | _   => .open_

def isConflict (t : Trail) (c : Clause) : Bool := match clauseStatus t c with | .conflict => true | _ => false
def unitOf (t : Trail) (c : Clause) : Option Lit := match clauseStatus t c with | .unit l => some l | _ => none
def bcp (clauses : List Clause) (level : Nat) : Nat → Trail → Trail × Option Clause
  | 0, t => (t, none)
  | fuel + 1, t =>
    match clauses.find? (fun c => isConflict t c) with
    | some c => (t, some c)
    | none => match clauses.findSome? (fun c => (unitOf t c).map (fun l => (l, c))) with
      | some (l, c) => bcp clauses level fuel ({lit := l, level := level, reason := some c} :: t)
      | none => (t, none)
def litLevel (t : Trail) (lit : Lit) : Nat := (t.find? (fun e => decide (e.lit = lit.neg))).elim 0 (·.level)
def analyze (t : Trail) (d : Nat) : Nat → Clause → Clause
  | 0, learned => learned
  | fuel + 1, learned =>
    if (learned.filter (fun lit => decide (litLevel t lit = d))).length ≤ 1 then learned
    else match t.find? (fun e => e.level = d && e.reason.isSome
                                 && learned.any (fun lit => decide (lit = e.lit.neg))) with
      | some e => match e.reason with
        | some r => analyze t d fuel (resolvent learned r e.lit.neg)
        | none => learned
      | none => learned
def backjumpLevel (t : Trail) (d : Nat) (learned : Clause) : Nat :=
  ((learned.filter (fun lit => decide (litLevel t lit ≠ d))).map (litLevel t)).foldl Nat.max 0
def pickDecision (t : Trail) (clauses : List Clause) : Option Lit :=
  ((clauses.flatMap id).map (·.var)).findSome?
    (fun n => if isUnassigned t ⟨n, true⟩ then some ⟨n, true⟩ else none)
def cdclLoop (orig : List Clause) : Nat → List Clause → Nat → Trail → Option (List Lit)
  | 0, _, _, _ => none
  | fuel + 1, learned, level, t =>
    let clauses := orig ++ learned
    match bcp clauses level (clauses.length + t.length + 1) t with
    | (t', some confl) =>
      if level = 0 then none
      else
        let lc := analyze t' level (t'.length + 1) confl
        let bj := backjumpLevel t' level lc
        let t'' := t'.filter (fun e => e.level ≤ bj)
        match lc.find? (fun lit => decide (litLevel t' lit = level)) with
        | some uip => cdclLoop orig fuel (lc :: learned) bj ({lit := uip, level := bj, reason := some lc} :: t'')
        | none => none
    | (t', none) =>
      match pickDecision t' clauses with
      | none => some (t'.map (·.lit))
      | some d => cdclLoop orig fuel learned (level + 1) ({lit := d, level := level + 1, reason := none} :: t')
def cdcl (cnf : Cnf) : Option (List Lit) := cdclLoop cnf 10000 [] 0 []

/-! ## Differential tests (Tier-3): CDCL must agree with the verified `dpll`, and its models must satisfy. -/
def battery : List Cnf :=
  [ [[⟨0,true⟩,⟨1,true⟩], [⟨0,false⟩], [⟨1,false⟩]],
    [[⟨0,true⟩,⟨1,true⟩], [⟨0,false⟩]],
    [[⟨0,true⟩], [⟨0,false⟩]],
    [],
    [[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩], [⟨0,false⟩], [⟨1,false⟩]],
    [[⟨0,true⟩,⟨1,true⟩], [⟨0,true⟩,⟨1,false⟩], [⟨0,false⟩,⟨1,true⟩], [⟨0,false⟩,⟨1,false⟩]],
    [[⟨0,true⟩], [⟨0,false⟩,⟨1,true⟩], [⟨1,false⟩,⟨2,true⟩], [⟨2,false⟩]] ]
#guard battery.all (fun cnf =>
  ((cdcl cnf).isSome == (dpll 50 cnf).isSome) &&
  (match cdcl cnf with | some ls => Cnf.satBy ls cnf | none => true))
#eval cdcl [[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩], [⟨0,false⟩], [⟨1,false⟩]]   -- a model

end Principia
