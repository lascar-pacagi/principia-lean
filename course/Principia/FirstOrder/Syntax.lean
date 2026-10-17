/-!
# First-order terms and formulas

Bound variables use de Bruijn indices: 0 is the nearest binder; entering a binder shifts
free variables. Substitution lifts below binders to avoid capturing those free variables.
Function and predicate symbols are natural-number names, with their arity supplied by the
argument list. This core is first-order logic without built-in equality.
-/
namespace Principia.FirstOrder

inductive Term where
  | variable : Nat → Term
  | function : Nat → List Term → Term
deriving Repr

namespace Term

mutual
  def decideTermEquality : (a b : Term) → Decidable (a = b)
    | .variable i, .variable j =>
      if h : i = j then isTrue (by cases h; rfl)
      else isFalse (fun he => h (Term.variable.inj he))
    | .variable _, .function _ _ => isFalse (by intro h; cases h)
    | .function _ _, .variable _ => isFalse (by intro h; cases h)
    | .function f xs, .function g ys =>
      if h : f = g then
        match decideArgumentEquality xs ys with
        | .isTrue ha => isTrue (by cases h; cases ha; rfl)
        | .isFalse ha => isFalse (fun he => ha (Term.function.inj he).2)
      else isFalse (fun he => h (Term.function.inj he).1)
  termination_by a _ => sizeOf a
  decreasing_by all_goals simp_wf <;> omega

  def decideArgumentEquality : (xs ys : List Term) → Decidable (xs = ys)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
    | a :: xs, b :: ys =>
      match decideTermEquality a b with
      | .isFalse h => isFalse (fun he => h (List.cons.inj he).1)
      | .isTrue h =>
        match decideArgumentEquality xs ys with
        | .isFalse ht => isFalse (fun he => ht (List.cons.inj he).2)
        | .isTrue ht => isTrue (by cases h; cases ht; rfl)
  termination_by xs _ => sizeOf xs
  decreasing_by all_goals simp_wf <;> omega
end

instance : DecidableEq Term := decideTermEquality

def substitute (σ : Nat → Term) : Term → Term
  | .variable i => σ i
  | .function f args => .function f (args.map (substitute σ))

def rename (ρ : Nat → Nat) (t : Term) : Term :=
  substitute (fun i => .variable (ρ i)) t

def variableBound : Term → Nat
  | .variable i => i + 1
  | .function _ args => (args.map variableBound).foldl max 0

/-- Does variable i occur in this term? Used by the unifier's occurs check. -/
def occurs (i : Nat) : Term → Bool
  | .variable j => i == j
  | .function _ args => (args.map (occurs i)).any id

end Term

inductive Formula where
  | predicate : Nat → List Term → Formula
  | falsum : Formula
  | implies : Formula → Formula → Formula
  | conjunction : Formula → Formula → Formula
  | disjunction : Formula → Formula → Formula
  | universal : Formula → Formula
  | existential : Formula → Formula
deriving DecidableEq, Repr

/-- Extend an environment, assigning the new bound variable index zero. -/
def extend {α : Type} (x : α) (ρ : Nat → α) : Nat → α
  | 0 => x
  | i + 1 => ρ i

/-- Enter a binder: preserve its variable zero, shift substituted free variables. -/
def liftSubstitution (σ : Nat → Term) : Nat → Term
  | 0 => .variable 0
  | i + 1 => (σ i).rename Nat.succ

namespace Formula

def negation (a : Formula) : Formula := .implies a .falsum

def substitute (σ : Nat → Term) : Formula → Formula
  | .predicate p args => .predicate p (args.map (Term.substitute σ))
  | .falsum => .falsum
  | .implies a b => .implies (substitute σ a) (substitute σ b)
  | .conjunction a b => .conjunction (substitute σ a) (substitute σ b)
  | .disjunction a b => .disjunction (substitute σ a) (substitute σ b)
  | .universal a => .universal (substitute (liftSubstitution σ) a)
  | .existential a => .existential (substitute (liftSubstitution σ) a)

def rename (ρ : Nat → Nat) (a : Formula) : Formula :=
  substitute (fun i => .variable (ρ i)) a

/-- Replace the outermost bound variable with t, lowering the remaining indices. -/
def instantiate (body : Formula) (t : Term) : Formula :=
  body.substitute (extend t Term.variable)

/-- Move a formula into a context containing one new, fresh variable. -/
def shift (a : Formula) : Formula := a.rename Nat.succ

end Formula
end Principia.FirstOrder
