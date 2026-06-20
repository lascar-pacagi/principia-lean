import Principia.Sat.Dpll

/-!
# Principia.Sat.Cdcl — a CDCL solver: clause learning + backjumping (Course 3, slice 3.5)

The modern SAT algorithm — **Conflict-Driven Clause Learning** — on top of slice 3.2's DPLL. Where DPLL
backtracks *chronologically* (undo the last guess), CDCL, on hitting a conflict, **analyses** it to
*learn* a new clause (by resolving the conflict against the reasons that caused it, up to the *first
unique implication point*), then **backjumps** non-chronologically to the deepest level where that
learned clause becomes unit, and propagates. The learned clause prevents the solver from ever repeating
that conflict — the source of CDCL's exponential edge over DPLL.

**Status: UNVERIFIED.** Unlike `dpll` (model-sound, slice 3.2) and the LRAT checker (`check_unsat`,
slice 3.6), this solver has *no machine-checked soundness proof* — the 1-UIP analysis and backjumping are
intricate. We justify it instead by **differential testing** (its SAT/UNSAT verdicts agree with the
verified `dpll` on a battery of instances; see the concept's `#guard`s) and by the fact that in practice
its UNSAT answers would be *emitted as an LRAT certificate and checked* by the verified `Sat.Lrat.check`
— a fast untrusted solver guarded by a small verified checker, exactly the Course-3 thesis.
-/
namespace Principia

/-- A trail entry: an assigned literal, the decision level it was set at, and the *reason* clause that
    forced it (`none` for a decision). -/
structure TEntry where
  lit    : Lit
  level  : Nat
  reason : Option Clause
deriving Repr

/-- The assignment trail (head = most recently assigned). -/
abbrev Trail := List TEntry

def assignedTrue (t : Trail) (l : Lit) : Bool := t.any (fun e => decide (e.lit = l))
def isUnassigned (t : Trail) (l : Lit) : Bool := !assignedTrue t l && !assignedTrue t l.neg

/-- A clause's status under the current (partial) assignment. -/
inductive CStatus | sat | conflict | unit (l : Lit) | open_

/-- Classify a clause: satisfied (a literal is true), conflicting (all false), unit (one unassigned,
    rest false), or open (≥ 2 unassigned). -/
def clauseStatus (t : Trail) (c : Clause) : CStatus :=
  if c.any (fun l => assignedTrue t l) then .sat
  else match c.filter (fun l => isUnassigned t l) with
    | []  => .conflict
    | [l] => .unit l
    | _   => .open_

def isConflict (t : Trail) (c : Clause) : Bool := match clauseStatus t c with | .conflict => true | _ => false
def unitOf (t : Trail) (c : Clause) : Option Lit := match clauseStatus t c with | .unit l => some l | _ => none

/-- Boolean constraint propagation: assign forced units until fixpoint or conflict. -/
def bcp (clauses : List Clause) (level : Nat) : Nat → Trail → Trail × Option Clause
  | 0, t => (t, none)
  | fuel + 1, t =>
    match clauses.find? (fun c => isConflict t c) with
    | some c => (t, some c)
    | none => match clauses.findSome? (fun c => (unitOf t c).map (fun l => (l, c))) with
      | some (l, c) => bcp clauses level fuel ({lit := l, level := level, reason := some c} :: t)
      | none => (t, none)

/-- The decision level at which clause-literal `lit` was falsified (i.e. `lit.neg` was assigned). -/
def litLevel (t : Trail) (lit : Lit) : Nat := (t.find? (fun e => decide (e.lit = lit.neg))).elim 0 (·.level)

/-- **1-UIP conflict analysis.** Resolve the conflict clause with the reasons of its current-level
    literals (most recent first) until just one literal remains at the current level — the learned clause. -/
def analyze (t : Trail) (d : Nat) : Nat → Clause → Clause
  | 0, learned => learned
  | fuel + 1, learned =>
    if (learned.filter (fun lit => decide (litLevel t lit = d))).length ≤ 1 then learned
    else match t.find? (fun e => e.level = d && e.reason.isSome
                                 && learned.any (fun lit => decide (lit = e.lit.neg))) with
      | some e => match e.reason with
        | some r => analyze t d fuel (resolvent learned r e.lit.neg)   -- one resolution step
        | none => learned
      | none => learned

/-- Backjump to the second-highest decision level in the learned clause (0 if it has only the UIP). -/
def backjumpLevel (t : Trail) (d : Nat) (learned : Clause) : Nat :=
  ((learned.filter (fun lit => decide (litLevel t lit ≠ d))).map (litLevel t)).foldl Nat.max 0

/-- Pick an unassigned variable to branch on (positive polarity). -/
def pickDecision (t : Trail) (clauses : List Clause) : Option Lit :=
  ((clauses.flatMap id).map (·.var)).findSome?
    (fun n => if isUnassigned t ⟨n, true⟩ then some ⟨n, true⟩ else none)

/-- The CDCL main loop: propagate; on conflict, learn + backjump (or report UNSAT at level 0); otherwise
    decide, or report the model when everything is assigned. -/
def cdclLoop (orig : List Clause) : Nat → List Clause → Nat → Trail → Option (List Lit)
  | 0, _, _, _ => none
  | fuel + 1, learned, level, t =>
    let clauses := orig ++ learned
    match bcp clauses level (clauses.length + t.length + 1) t with
    | (t', some confl) =>
      if level = 0 then none                                            -- conflict with no decisions ⇒ UNSAT
      else
        let lc := analyze t' level (t'.length + 1) confl                -- learn
        let bj := backjumpLevel t' level lc                             -- where to jump back to
        let t'' := t'.filter (fun e => e.level ≤ bj)                    -- backjump (pop the trail)
        match lc.find? (fun lit => decide (litLevel t' lit = level)) with
        | some uip => cdclLoop orig fuel (lc :: learned) bj
                        ({lit := uip, level := bj, reason := some lc} :: t'')   -- assert the UIP
        | none => none
    | (t', none) =>
      match pickDecision t' clauses with
      | none => some (t'.map (·.lit))                                   -- all assigned, no conflict ⇒ SAT
      | some d => cdclLoop orig fuel learned (level + 1)
                    ({lit := d, level := level + 1, reason := none} :: t')      -- decide

/-- Solve `cnf` by CDCL: a satisfying assignment, or `none` if unsatisfiable (within the fuel). -/
def cdcl (cnf : Cnf) : Option (List Lit) := cdclLoop cnf 10000 [] 0 []

end Principia
