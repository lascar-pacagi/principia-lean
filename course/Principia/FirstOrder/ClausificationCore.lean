import Principia.FirstOrder.Support
import Principia.FirstOrder.ResolutionSearch

/-! Executable NNF, Skolemization, and CNF conversion. The model-expansion proofs
are in SkolemCorrectness; the certified prover interface is in Clausification. -/
namespace Principia.FirstOrder

inductive Nnf where
  | literal : Literal → Nnf
  | verum : Nnf
  | falsum : Nnf
  | conjunction : Nnf → Nnf → Nnf
  | disjunction : Nnf → Nnf → Nnf
  | universal : Nnf → Nnf
  | existential : Nnf → Nnf
deriving Repr

def Formula.toNnf : Bool → Formula → Nnf
  | p, .predicate symbol args => .literal ⟨p, ⟨symbol, args⟩⟩
  | true, .falsum => .falsum
  | false, .falsum => .verum
  | true, .implies a b => .disjunction (a.toNnf false) (b.toNnf true)
  | false, .implies a b => .conjunction (a.toNnf true) (b.toNnf false)
  | true, .conjunction a b => .conjunction (a.toNnf true) (b.toNnf true)
  | false, .conjunction a b => .disjunction (a.toNnf false) (b.toNnf false)
  | true, .disjunction a b => .disjunction (a.toNnf true) (b.toNnf true)
  | false, .disjunction a b => .conjunction (a.toNnf false) (b.toNnf false)
  | true, .universal a => .universal (a.toNnf true)
  | false, .universal a => .existential (a.toNnf false)
  | true, .existential a => .existential (a.toNnf true)
  | false, .existential a => .universal (a.toNnf false)

def Nnf.evaluate {D : Type} (M : Model D) (ρ : Nat → D) : Nnf → Prop
  | .literal l => l.evaluate M ρ
  | .verum => True
  | .falsum => False
  | .conjunction a b => a.evaluate M ρ ∧ b.evaluate M ρ
  | .disjunction a b => a.evaluate M ρ ∨ b.evaluate M ρ
  | .universal a => ∀ x, a.evaluate M (extend x ρ)
  | .existential a => ∃ x, a.evaluate M (extend x ρ)

theorem toNnf_correct {D : Type} (M : Model D) (a : Formula) :
    ∀ (p : Bool) (ρ : Nat → D),
    (a.toNnf p).evaluate M ρ ↔ if p then a.evaluate M ρ else ¬a.evaluate M ρ := by
  classical
  induction a with
  | predicate s args => intro p ρ; cases p <;> rfl
  | falsum => intro p ρ; cases p <;> simp [Formula.toNnf, Nnf.evaluate, Formula.evaluate]
  | implies a b iha ihb =>
    intro p ρ
    cases p <;> simp [Formula.toNnf, Nnf.evaluate, Formula.evaluate, iha, ihb, Classical.not_imp, Classical.or_iff_not_imp_left]
  | conjunction a b iha ihb =>
    intro p ρ
    cases p <;> simp [Formula.toNnf, Nnf.evaluate, Formula.evaluate, iha, ihb, Classical.or_iff_not_imp_left]
  | disjunction a b iha ihb =>
    intro p ρ
    cases p <;> simp [Formula.toNnf, Nnf.evaluate, Formula.evaluate, iha, ihb]
  | universal a ih =>
    intro p ρ
    cases p <;> simp [Formula.toNnf, Nnf.evaluate, Formula.evaluate, ih, Classical.not_forall]
  | existential a ih =>
    intro p ρ
    cases p <;> simp [Formula.toNnf, Nnf.evaluate, Formula.evaluate, ih]

inductive Matrix where
  | literal : Literal → Matrix
  | verum : Matrix
  | falsum : Matrix
  | conjunction : Matrix → Matrix → Matrix
  | disjunction : Matrix → Matrix → Matrix
deriving Repr

def Matrix.evaluate {D : Type} (M : Model D) (ρ : Nat → D) : Matrix → Prop
  | .literal l => l.evaluate M ρ
  | .verum => True
  | .falsum => False
  | .conjunction a b => a.evaluate M ρ ∧ b.evaluate M ρ
  | .disjunction a b => a.evaluate M ρ ∨ b.evaluate M ρ

def clauseProduct (s t : ClauseSet) : ClauseSet := s.flatMap fun c => t.map (c ++ ·)

def Matrix.toClauses : Matrix → ClauseSet
  | .literal l => [[l]]
  | .verum => []
  | .falsum => [[]]
  | .conjunction a b => a.toClauses ++ b.toClauses
  | .disjunction a b => clauseProduct a.toClauses b.toClauses

def ClausesAt {D : Type} (M : Model D) (ρ : Nat → D) (s : ClauseSet) : Prop :=
  ∀ c ∈ s, Clause.evaluate M ρ c

theorem clause_append {D : Type} (M : Model D) (ρ : Nat → D) (c d : Clause) :
    Clause.evaluate M ρ (c ++ d) ↔ Clause.evaluate M ρ c ∨ Clause.evaluate M ρ d := by
  simp only [Clause.evaluate, List.mem_append]
  constructor
  · intro ⟨l, hl, ht⟩
    exact hl.elim (fun h => Or.inl ⟨l, h, ht⟩) (fun h => Or.inr ⟨l, h, ht⟩)
  · intro h
    rcases h with ⟨l, hl, ht⟩ | ⟨l, hl, ht⟩
    · exact ⟨l, Or.inl hl, ht⟩
    · exact ⟨l, Or.inr hl, ht⟩

theorem clauseProduct_correct {D : Type} (M : Model D) (ρ : Nat → D) (s t : ClauseSet) :
    ClausesAt M ρ (clauseProduct s t) ↔ ClausesAt M ρ s ∨ ClausesAt M ρ t := by
  classical
  constructor
  · intro h
    by_cases hs : ClausesAt M ρ s
    · exact Or.inl hs
    · apply Or.inr
      have bad : ∃ c ∈ s, ¬Clause.evaluate M ρ c := by
        apply Classical.byContradiction
        intro hn
        exact hs (fun c hc => Classical.byContradiction (fun hn' => hn ⟨c, hc, hn'⟩))
      obtain ⟨c, hc, hn⟩ := bad
      intro d hd
      have hh := h (c ++ d) (List.mem_flatMap.mpr ⟨c, hc, List.mem_map.mpr ⟨d, hd, rfl⟩⟩)
      exact ((clause_append M ρ c d).mp hh).resolve_left hn
  · intro h c hc
    obtain ⟨a, ha, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨b, hb, he⟩ := List.mem_map.mp hc
    subst c
    apply (clause_append M ρ a b).mpr
    exact h.elim (fun hs => Or.inl (hs a ha)) (fun ht => Or.inr (ht b hb))

theorem matrix_toClauses_correct {D : Type} (M : Model D) (ρ : Nat → D) (a : Matrix) :
    ClausesAt M ρ a.toClauses ↔ a.evaluate M ρ := by
  induction a with
  | literal l => simp [Matrix.toClauses, ClausesAt, Clause.evaluate, Matrix.evaluate]
  | verum => simp [Matrix.toClauses, ClausesAt, Matrix.evaluate]
  | falsum => simp [Matrix.toClauses, ClausesAt, Clause.evaluate, Matrix.evaluate]
  | conjunction a b iha ihb =>
    constructor
    · intro h
      exact ⟨iha.mp (fun c hc => h c (List.mem_append_left _ hc)),
        ihb.mp (fun c hc => h c (List.mem_append_right _ hc))⟩
    · intro ⟨ha, hb⟩ c hc
      exact (List.mem_append.mp hc).elim (iha.mpr ha c) (ihb.mpr hb c)
  | disjunction a b iha ihb =>
    exact (clauseProduct_correct M ρ _ _).trans (or_congr iha ihb)

structure SkolemSymbol where
  symbol : Nat
  dependencies : List Nat
deriving Repr, DecidableEq

structure Clausification where
  clauses : ClauseSet
  skolemSymbols : List SkolemSymbol
  nextFunction : Nat
  nextVariable : Nat
deriving Repr

structure SkolemResult where
  matrix : Matrix
  symbols : List SkolemSymbol
  nextFunction : Nat
  nextVariable : Nat

/-- Bindings are already translated terms, so entering a removed binder extends the map directly.
Universals get globally fresh variable names; existentials depend on all enclosing universals. -/
def skolemize (ρ : Nat → Term) (universals : List Nat) :
    Nnf → (nextFunction nextVariable : Nat) → SkolemResult
  | .literal l, f, v => ⟨.literal (l.substitute ρ), [], f, v⟩
  | .verum, f, v => ⟨.verum, [], f, v⟩
  | .falsum, f, v => ⟨.falsum, [], f, v⟩
  | .conjunction a b, f, v =>
    let left := skolemize ρ universals a f v
    let right := skolemize ρ universals b left.nextFunction left.nextVariable
    ⟨.conjunction left.matrix right.matrix, left.symbols ++ right.symbols,
      right.nextFunction, right.nextVariable⟩
  | .disjunction a b, f, v =>
    let left := skolemize ρ universals a f v
    let right := skolemize ρ universals b left.nextFunction left.nextVariable
    ⟨.disjunction left.matrix right.matrix, left.symbols ++ right.symbols,
      right.nextFunction, right.nextVariable⟩
  | .universal body, f, v =>
    skolemize (extend (.variable v) ρ) (universals ++ [v]) body f (v+1)
  | .existential body, f, v =>
    let term := Term.function f (universals.map Term.variable)
    let result := skolemize (extend term ρ) universals body (f+1) v
    ⟨result.matrix, ⟨f, universals⟩ :: result.symbols,
      result.nextFunction, result.nextVariable⟩

def Term.functionBound : Term → Nat
  | .variable _ => 0
  | .function f args => (args.map Term.functionBound).foldl max (f+1)

def Formula.functionBound : Formula → Nat
  | .predicate _ args => (args.map Term.functionBound).foldl max 0
  | .falsum => 0
  | .implies a b | .conjunction a b | .disjunction a b => max a.functionBound b.functionBound
  | .universal a | .existential a => a.functionBound

/-- Satisfiability convention: free variables are existentially closed. They are assigned fresh
Skolem constants before the quantifier walk. Thus refuting the negation tests validity at ALL environments. -/
def clausify (a : Formula) : Clausification :=
  let base := a.functionBound
  let freeCount := (a.support.map (· + 1)).foldl max 0
  let freeConstants := (List.range freeCount).map (fun i => SkolemSymbol.mk (base+i) [])
  let initial := fun i => Term.function (base+i) []
  let result := skolemize initial [] (a.toNnf true) (base+freeCount) 0
  ⟨result.matrix.toClauses, freeConstants ++ result.symbols,
    result.nextFunction, result.nextVariable⟩

def contextFormula : List Formula → Formula
  | [] => Formula.falsum.negation
  | a :: rest => .conjunction a (contextFormula rest)

def counterexampleFormula (Γ : List Formula) (goal : Formula) : Formula :=
  .conjunction (contextFormula Γ) goal.negation


end Principia.FirstOrder
