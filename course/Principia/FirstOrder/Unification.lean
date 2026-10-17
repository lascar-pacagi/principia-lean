import Principia.FirstOrder.Resolution

namespace Principia.FirstOrder

/-- A finite simultaneous substitution, stored as variable/term bindings. -/
structure Substitution where
  bindings : List (Nat × Term)
deriving Repr

namespace Substitution

def lookup (σ : Substitution) (i : Nat) : Term :=
  match σ.bindings.find? (fun binding => binding.1 == i) with
  | some binding => binding.2
  | none => .variable i

def apply (σ : Substitution) (t : Term) : Term := t.substitute σ.lookup

/-- Compose a new binding after the already accumulated substitution. -/
def bind (σ : Substitution) (i : Nat) (t : Term) : Substitution :=
  let single := fun j => if j = i then t else Term.variable j
  ⟨σ.bindings.map (fun (j, s) => (j, s.substitute single)) ++ [(i, t)]⟩

end Substitution

/-- Robinson-style equation processing. The explicit budget bounds this attempt; the public
wrapper checks the proposed result against the original equations before accepting it. -/
def unifyWork : Nat → List (Term × Term) → Substitution → Option Substitution
  | _, [], σ => some σ
  | 0, _ :: _, _ => none
  | fuel + 1, (a, b) :: rest, σ =>
    if a = b then unifyWork fuel rest σ else
    match a, b with
    | .variable i, t =>
      if t.occurs i then none else
      let single := fun j => if j = i then t else Term.variable j
      unifyWork fuel (rest.map (fun (s, u) => (s.substitute single, u.substitute single)))
        (σ.bind i t)
    | t, .variable i =>
      if t.occurs i then none else
      let single := fun j => if j = i then t else Term.variable j
      unifyWork fuel (rest.map (fun (s, u) => (s.substitute single, u.substitute single)))
        (σ.bind i t)
    | .function f xs, .function g ys =>
      if f = g ∧ xs.length = ys.length then unifyWork fuel (xs.zip ys ++ rest) σ
      else none

/-- A proposed substitution together with a kernel-checked proof that it solves every equation. -/
structure CheckedUnifier (equations : List (Term × Term)) where
  substitution : Substitution
  solves : ∀ pair ∈ equations,
    substitution.apply pair.1 = substitution.apply pair.2

def unify? (fuel : Nat) (equations : List (Term × Term)) : Option (CheckedUnifier equations) := do
  let σ ← unifyWork fuel equations ⟨[]⟩
  if h : equations.all (fun pair => decide (σ.apply pair.1 = σ.apply pair.2)) = true then
    pure ⟨σ, fun pair hp => of_decide_eq_true (List.all_eq_true.mp h pair hp)⟩
  else none

/-- Atom unification checks symbols, arities, and the final substituted atoms. -/
def unifyAtoms? (fuel : Nat) (a b : Atom) :
    Option {σ : Substitution // a.substitute σ.lookup = b.substitute σ.lookup} := do
  if a.symbol != b.symbol || a.arguments.length != b.arguments.length then none else do
  let result ← unify? fuel (a.arguments.zip b.arguments)
  let σ := result.substitution
  if h : a.substitute σ.lookup = b.substitute σ.lookup then pure ⟨σ, h⟩ else none

end Principia.FirstOrder
