import Principia.FirstOrder.Semantics

namespace Principia.FirstOrder

structure Atom where
  symbol : Nat
  arguments : List Term
deriving DecidableEq, Repr

structure Literal where
  positive : Bool
  atom : Atom
deriving DecidableEq, Repr

abbrev Clause := List Literal
abbrev ClauseSet := List Clause

namespace Atom

def substitute (σ : Nat → Term) (a : Atom) : Atom :=
  ⟨a.symbol, a.arguments.map (Term.substitute σ)⟩

def evaluate {D : Type} (M : Model D) (ρ : Nat → D) (a : Atom) : Prop :=
  M.predicate a.symbol (a.arguments.map (Term.evaluate M ρ))

theorem evaluate_substitute {D : Type} (M : Model D) (ρ : Nat → D)
    (σ : Nat → Term) (a : Atom) :
    (a.substitute σ).evaluate M ρ ↔ a.evaluate M (fun i => Term.evaluate M ρ (σ i)) := by
  unfold substitute evaluate
  simp only [List.map_map, Function.comp_def]
  have he : (fun t => Term.evaluate M ρ (Term.substitute σ t)) =
      (fun t => Term.evaluate M (fun i => Term.evaluate M ρ (σ i)) t) := by
    funext t
    exact Term.evaluate_substitute M ρ σ t
  rw [he]

end Atom

namespace Literal

def complement (l : Literal) : Literal := ⟨!l.positive, l.atom⟩
def substitute (σ : Nat → Term) (l : Literal) : Literal := ⟨l.positive, l.atom.substitute σ⟩
def evaluate {D : Type} (M : Model D) (ρ : Nat → D) (l : Literal) : Prop :=
  if l.positive then l.atom.evaluate M ρ else ¬l.atom.evaluate M ρ

theorem complement_evaluate {D : Type} (M : Model D) (ρ : Nat → D) (l : Literal) :
    l.complement.evaluate M ρ ↔ ¬l.evaluate M ρ := by
  classical
  cases l with
  | mk positive atom => cases positive <;> simp [complement, evaluate]

theorem evaluate_substitute {D : Type} (M : Model D) (ρ : Nat → D)
    (σ : Nat → Term) (l : Literal) :
    (l.substitute σ).evaluate M ρ ↔ l.evaluate M (fun i => Term.evaluate M ρ (σ i)) := by
  cases l with
  | mk positive atom =>
    cases positive <;> simp only [substitute, evaluate, Bool.false_eq_true, if_false, if_true]
    · exact not_congr (Atom.evaluate_substitute M ρ σ atom)
    · exact Atom.evaluate_substitute M ρ σ atom

end Literal

namespace Clause

def substitute (σ : Nat → Term) (c : Clause) : Clause := c.map (Literal.substitute σ)
def evaluate {D : Type} (M : Model D) (ρ : Nat → D) (c : Clause) : Prop :=
  ∃ l ∈ c, l.evaluate M ρ

theorem evaluate_substitute {D : Type} (M : Model D) (ρ : Nat → D)
    (σ : Nat → Term) (c : Clause) :
    evaluate M ρ (substitute σ c) ↔ evaluate M (fun i => Term.evaluate M ρ (σ i)) c := by
  constructor
  · intro ⟨l, hl, ht⟩
    obtain ⟨k, hk, he⟩ := List.mem_map.mp hl
    subst l
    exact ⟨k, hk, (Literal.evaluate_substitute M ρ σ k).mp ht⟩
  · intro ⟨l, hl, ht⟩
    exact ⟨l.substitute σ, List.mem_map.mpr ⟨l, hl, rfl⟩,
      (Literal.evaluate_substitute M ρ σ l).mpr ht⟩

end Clause

/-- Clauses are implicitly universally quantified over all their variables. -/
def SatisfiesClauses {D : Type} (M : Model D) (S : ClauseSet) : Prop :=
  ∀ c ∈ S, ∀ ρ, Clause.evaluate M ρ c

def resolvent (c d : Clause) (l : Literal) : Clause := c.erase l ++ d.erase l.complement

inductive ResolutionDerivation (S : ClauseSet) : Clause → Type where
  | input {c} : c ∈ S → ResolutionDerivation S c
  | substitution {c} (σ : Nat → Term) : ResolutionDerivation S c →
      ResolutionDerivation S (Clause.substitute σ c)
  | resolution {c d} (l : Literal) : ResolutionDerivation S c → ResolutionDerivation S d →
      ResolutionDerivation S (resolvent c d l)
  | contraction {c} : ResolutionDerivation S c → ResolutionDerivation S c.eraseDups
  | weakening {c d} : ResolutionDerivation S c → (∀ l ∈ c, l ∈ d) →
      ResolutionDerivation S d
  | tautology (l : Literal) : ResolutionDerivation S [l, l.complement]

/-- Traverse the returned certificate, including substitution and contraction nodes. -/
def ResolutionDerivation.nodeCount {S : ClauseSet} {c : Clause} :
    ResolutionDerivation S c → Nat
  | .input _ => 1
  | .substitution _ d => 1 + d.nodeCount
  | .resolution _ left right => 1 + left.nodeCount + right.nodeCount
  | .contraction d => 1 + d.nodeCount
  | .weakening d _ => 1 + d.nodeCount
  | .tautology _ => 1

/-- Removing a false literal preserves the true witness in a satisfied clause. -/
theorem erase_preserves_truth {D : Type} (M : Model D) (ρ : Nat → D)
    (c : Clause) (l : Literal) (hc : Clause.evaluate M ρ c) (hl : ¬l.evaluate M ρ) :
    Clause.evaluate M ρ (c.erase l) := by
  obtain ⟨k, hk, ht⟩ := hc
  have hne : k ≠ l := by intro he; subst k; exact hl ht
  exact ⟨k, (List.mem_erase_of_ne hne).mpr hk, ht⟩

theorem resolvent_preserves_truth {D : Type} (M : Model D) (ρ : Nat → D)
    (c d : Clause) (l : Literal) (hc : Clause.evaluate M ρ c) (hd : Clause.evaluate M ρ d) :
    Clause.evaluate M ρ (resolvent c d l) := by
  classical
  by_cases hl : l.evaluate M ρ
  · have hn : ¬l.complement.evaluate M ρ := by
      intro he
      exact (Literal.complement_evaluate M ρ l).mp he hl
    obtain ⟨k, hk, ht⟩ := erase_preserves_truth M ρ d l.complement hd hn
    exact ⟨k, List.mem_append_right _ hk, ht⟩
  · obtain ⟨k, hk, ht⟩ := erase_preserves_truth M ρ c l hc hl
    exact ⟨k, List.mem_append_left _ hk, ht⟩

/-- First-order resolution, instantiation and factoring preserve every model. -/
theorem resolution_sound {D : Type} (M : Model D) {S : ClauseSet} {c : Clause}
    (d : ResolutionDerivation S c) (hS : SatisfiesClauses M S) :
    ∀ ρ, Clause.evaluate M ρ c := by
  induction d with
  | input h => intro ρ; exact hS _ h ρ
  | substitution σ d ih =>
    intro ρ
    exact (Clause.evaluate_substitute M ρ σ _).mpr (ih (fun i => Term.evaluate M ρ (σ i)))
  | resolution l d e ihd ihe =>
    intro ρ
    exact resolvent_preserves_truth M ρ _ _ l (ihd ρ) (ihe ρ)
  | contraction d ih =>
    intro ρ
    obtain ⟨l, hl, ht⟩ := ih ρ
    exact ⟨l, (List.mem_eraseDups).mpr hl, ht⟩
  | weakening d included ih =>
    intro ρ
    obtain ⟨l, hl, ht⟩ := ih ρ
    exact ⟨l, included l hl, ht⟩
  | tautology l =>
    intro ρ
    classical
    by_cases h : l.evaluate M ρ
    · exact ⟨l, by simp, h⟩
    · exact ⟨l.complement, by simp, (Literal.complement_evaluate M ρ l).mpr h⟩

def Unsatisfiable (S : ClauseSet) : Prop :=
  ∀ (D : Type) (_ : Nonempty D) (M : Model D), ¬SatisfiesClauses M S

theorem refutation_unsatisfiable {S : ClauseSet} (d : ResolutionDerivation S []) :
    Unsatisfiable S := by
  intro D inhabited M hS
  obtain ⟨l, hl, ht⟩ := resolution_sound M d hS (fun _ => Classical.choice inhabited)
  cases hl

end Principia.FirstOrder
