import Principia.Logic.Syntax

/-!
# Principia.Logic.Semantics — truth-value semantics (Course 1, slice 1.2)

A valuation is a function `Nat → Bool` on the atoms. `eval` is the truth table as code; `Tautology` and
`Entails` (`⊨`) are validity and semantic entailment; `taut?` is a runnable decision procedure.
-/
namespace Principia.Form

open scoped Principia.Form

/-- Truth value of a formula under a valuation `v` of the atoms. -/
def eval (v : Nat → Bool) : Form → Bool
  | .var n   => v n
  | .falsum     => false
  | .imp a b => (!eval v a) || eval v b
  | .and a b => eval v a && eval v b
  | .or a b  => eval v a || eval v b

/-- `φ` is a tautology: true under *every* valuation. (Semantic `⊨ φ`.) -/
def Tautology (φ : Form) : Prop := ∀ v, eval v φ = true

/-- `Γ ⊨ φ`: every valuation satisfying all of `Γ` also satisfies `φ`. -/
def Entails (Γ : List Form) (φ : Form) : Prop :=
  ∀ v, (∀ ψ ∈ Γ, eval v ψ = true) → eval v φ = true

@[inherit_doc] scoped notation:40 Γ " ⊨ " φ => Entails Γ φ

/-! ### A runnable tautology checker

`eval` only depends on atoms below `maxVar φ`, so checking all `2^(maxVar φ)` valuations decides
tautology-hood. The equivalence `taut?_eq_true_iff` below certifies that this finite check covers
all valuations, including those represented as arbitrary functions `Nat → Bool`. -/
def maxVar : Form → Nat
  | .var n   => n + 1
  | .falsum     => 0
  | .imp a b => max (maxVar a) (maxVar b)
  | .and a b => max (maxVar a) (maxVar b)
  | .or a b  => max (maxVar a) (maxVar b)

/-- All valuations that differ only on atoms `< n` (others default to `false`). -/
def allEnvs : Nat → List (Nat → Bool)
  | 0     => [fun _ => false]
  | n + 1 => (allEnvs n).flatMap (fun v => [v, fun k => if k == n then true else v k])

/-- Decide tautology-hood by exhausting the (finite) relevant valuations. -/
def taut? (φ : Form) : Bool := (allEnvs (maxVar φ)).all (fun v => eval v φ)

/-! ### Why the finite table covers every valuation -/

/-- Enumerated valuations assign false to every index outside the table bound. -/
theorem allEnvs_default (n : Nat) (w : Nat → Bool) (hw : w ∈ allEnvs n) :
    ∀ i, n ≤ i → w i = false := by
  induction n generalizing w with
  | zero =>
    simp only [allEnvs, List.mem_cons, List.not_mem_nil, or_false] at hw
    subst w
    intro i hi
    rfl
  | succ n ih =>
    simp only [allEnvs, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hw
    obtain ⟨u, hu, hcases⟩ := hw
    cases hcases with
    | inl he =>
      subst w
      intro i hi
      exact ih u hu i (by omega)
    | inr he =>
      subst w
      intro i hi
      have hne : i ≠ n := by omega
      simp only [beq_iff_eq, if_neg hne]
      exact ih u hu i (by omega)

/-- Every valuation has a representative in the table, agreeing below its bound. -/
theorem allEnvs_cover (v : Nat → Bool) (n : Nat) :
    ∃ w ∈ allEnvs n, ∀ i, i < n → v i = w i := by
  induction n with
  | zero => exact ⟨fun _ => false, by simp [allEnvs], by intro i hi; omega⟩
  | succ n ih =>
    obtain ⟨w, hw, hagree⟩ := ih
    cases hv : v n with
    | false =>
      refine ⟨w, List.mem_flatMap.mpr ⟨w, hw, by simp⟩, ?_⟩
      intro i hi
      by_cases hlt : i < n
      · exact hagree i hlt
      · have he : i = n := by omega
        subst i
        rw [hv, allEnvs_default n w hw n (Nat.le_refl n)]
    | true =>
      refine ⟨fun k => if k == n then true else w k,
        List.mem_flatMap.mpr ⟨w, hw, by simp⟩, ?_⟩
      intro i hi
      by_cases hlt : i < n
      · have hne : i ≠ n := by omega
        simp only [beq_iff_eq, if_neg hne]
        exact hagree i hlt
      · have he : i = n := by omega
        subst i
        simp [hv]

/-- Evaluation observes only the atom indices covered by the formula bound. -/
theorem eval_eq_of_agree (v w : Nat → Bool) : ∀ (φ : Form) (n : Nat),
    φ.maxVar ≤ n → (∀ i, i < n → v i = w i) → eval v φ = eval w φ := by
  intro φ
  induction φ with
  | var i =>
    intro n hb h
    exact h i (by simp only [maxVar] at hb; omega)
  | falsum => intro n hb h; rfl
  | and a b iha ihb =>
    intro n hb h
    simp only [maxVar] at hb
    simp only [eval, iha n (by omega) h, ihb n (by omega) h]
  | or a b iha ihb =>
    intro n hb h
    simp only [maxVar] at hb
    simp only [eval, iha n (by omega) h, ihb n (by omega) h]
  | imp a b iha ihb =>
    intro n hb h
    simp only [maxVar] at hb
    simp only [eval, iha n (by omega) h, ihb n (by omega) h]

/-- The executable finite truth table is equivalent to universal semantic validity. -/
theorem taut?_eq_true_iff (φ : Form) : taut? φ = true ↔ Tautology φ := by
  constructor
  · intro h v
    obtain ⟨w, hw, hagree⟩ := allEnvs_cover v φ.maxVar
    have he : eval w φ = true := List.all_eq_true.mp h w hw
    rw [eval_eq_of_agree v w φ φ.maxVar (Nat.le_refl _) hagree]
    exact he
  · intro h
    exact List.all_eq_true.mpr (fun v hv => h v)


/-! ### Basic semantic facts -/

theorem eval_neg (v : Nat → Bool) (φ : Form) : eval v (∼φ) = !eval v φ := by
  simp [Form.neg, eval]

theorem eval_top (v : Nat → Bool) : eval v Form.top = true := by
  simp [Form.top, Form.neg, eval]

/-- `φ ⇒ φ` is valid. -/
theorem taut_imp_self (φ : Form) : Tautology (φ ⇒ φ) := by
  intro v; simp only [eval]; cases eval v φ <;> rfl

/-- Excluded middle is *semantically* valid (contrast `04-logic`, where `p ∨ ¬p` needed a classical
    axiom to *prove* — here it's just a truth table). -/
theorem taut_excluded_middle (φ : Form) : Tautology (φ ⋎ ∼φ) := by
  intro v; simp only [eval, Form.neg]; cases eval v φ <;> rfl

/-- Compatibility name for the semantic excluded-middle theorem. -/
theorem taut_em (φ : Form) : Tautology (φ ⋎ ∼φ) :=
  taut_excluded_middle φ

end Principia.Form
