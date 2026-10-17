import Principia.NatDed.Solver
import Principia.NatDed.Prover

/-! Regression checks for the complete solver, including actual generated certificates. -/
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

open Principia Principia.Form
open scoped Principia.Form Principia

namespace CompleteSolverChecks

/-- An independent spelling of the truth conditions, especially implication. -/
def referenceEval (v : Nat → Bool) : Form → Bool
  | .var i => v i
  | .fls => false
  | .imp a b => if referenceEval v a then referenceEval v b else true
  | .and a b => if referenceEval v a then referenceEval v b else false
  | .or a b => if referenceEval v a then true else referenceEval v b

/-- All formulas up to a given depth, using two atoms and falsehood. -/
def formulas : Nat → List Form
  | 0 => [.var 0, .var 1, .fls]
  | n + 1 =>
    let children := formulas n
    [.var 0, .var 1, .fls] ++ children.flatMap (fun a =>
      children.flatMap (fun b => [.imp a b, .and a b, .or a b]))

def referenceValid (a : Form) : Bool :=
  [false, true].all (fun p => [false, true].all (fun q =>
    referenceEval (fun i => if i == 0 then p else q) a))

/-- Check tags against the independent table and traverse each positive proof tree. -/
def validate (a : Form) : Bool :=
  match solve a with
  | .valid d => referenceValid a && (d.nodeCount > 0)
  | .invalid _ => !referenceValid a

#guard (formulas 2).length = 2703
#guard (formulas 2).all validate

#guard (prove ((Form.var 0 ⋏ Form.var 1) ⇒ Form.var 0)).isSome = false
#guard (proveComplete ((Form.var 0 ⋏ Form.var 1) ⇒ Form.var 0)).isSome = true
#guard (solve (((Form.var 0 ⇒ Form.var 1) ⇒ Form.var 0) ⇒ Form.var 0)).isValid = true
#guard (solve (Form.var 0 ⋎ ∼Form.var 0)).isValid = true
#guard (solve (∼(Form.var 0 ⋏ Form.var 1) ⇒ (∼Form.var 0 ⋎ ∼Form.var 1))).isValid = true
#guard (solve Form.fls).isValid = false
#guard (solve Form.top).isValid = true
#guard (solve (Form.var 0 ⇒ Form.var 1)).isValid = false
#guard (solve (Form.var 4 ⇒ Form.var 4)).isValid = true
#guard (solve (Form.var 4 ⇒ Form.var 0)).isValid = false

#print axioms taut?_eq_true_iff
#print axioms completeness
#print axioms solve_iff
#print axioms solve_invalid_iff
#print axioms proveComplete_iff

end CompleteSolverChecks
