import Principia.NatDed.Basic
import Principia.Logic.Semantics

/-!
# Principia.NatDed.Kalmar — the machinery of completeness (Course 1, slice 1.6)

The heavy lifting behind completeness, via **Kalmár's method** (elementary — no maximal consistent sets,
no choice beyond Lean's). In order:

* **derived inference rules** — weakening, and, for each connective, how to derive it or its negation;
* **`dEM`/`byCasesD`** — excluded middle in any context, and proof-by-cases;
* **literal contexts** `litCtx v n` — the assumptions `{±atomᵢ}` matching a valuation `v`;
* **`kalmar`** — for any `φ`, from `litCtx v n` derive `φ` if `v ⊨ φ`, else `∼φ` (induction on `φ`);
* **`elim`** — collapse all `2ⁿ` literal contexts to `[]` by eliminating each variable with `byCasesD`.

`Completeness.lean` assembles these into `Γ ⊨ φ → Γ ⊢ φ`.
-/
namespace Principia.Form

open scoped Principia.Form Principia

/-! ### Weakening -/

theorem cons_sub {Γ Δ : List Form} (a : Form) (h : Γ ⊆ Δ) : (a :: Γ) ⊆ (a :: Δ) := by
  intro x hx; cases hx with | head => exact .head _ | tail _ h' => exact .tail _ (h h')

/-- A derivation survives enlarging its context. -/
def weaken : {Γ Δ : List Form} → {φ : Form} → Γ ⊆ Δ → (Γ ⊢ φ) → (Δ ⊢ φ)
  | _, _, _, h, .ax m       => .ax (h m)
  | _, _, _, h, .impI d     => .impI (weaken (cons_sub _ h) d)
  | _, _, _, h, .impE d1 d2 => .impE (weaken h d1) (weaken h d2)
  | _, _, _, h, .andI d1 d2 => .andI (weaken h d1) (weaken h d2)
  | _, _, _, h, .andE₁ d    => .andE₁ (weaken h d)
  | _, _, _, h, .andE₂ d    => .andE₂ (weaken h d)
  | _, _, _, h, .orI₁ d     => .orI₁ (weaken h d)
  | _, _, _, h, .orI₂ d     => .orI₂ (weaken h d)
  | _, _, _, h, .orE d a b  => .orE (weaken h d) (weaken (cons_sub _ h) a) (weaken (cons_sub _ h) b)
  | _, _, _, h, .flsE d     => .flsE (weaken h d)
  | _, _, _, h, .raa d      => .raa (weaken (cons_sub _ h) d)

theorem sub_cons (c : Form) (Γ : List Form) : Γ ⊆ (c :: Γ) := by intro x h; exact .tail c h
theorem sub_cons2 (c d : Form) (Γ : List Form) : Γ ⊆ (c :: d :: Γ) := by
  intro x h; exact .tail c (.tail d h)

/-! ### Derived rules: build each connective, or its negation -/

def notAnd_left {Γ a b} (h : Γ ⊢ ∼a) : Γ ⊢ ∼(a ⋏ b) :=
  .impI (.impE (a := a) (weaken (sub_cons _ _) h) (.andE₁ (.ax (a := a ⋏ b) (by simp))))
def notAnd_right {Γ a b} (h : Γ ⊢ ∼b) : Γ ⊢ ∼(a ⋏ b) :=
  .impI (.impE (a := b) (weaken (sub_cons _ _) h) (.andE₂ (.ax (a := a ⋏ b) (by simp))))
def notOr {Γ a b} (ha : Γ ⊢ ∼a) (hb : Γ ⊢ ∼b) : Γ ⊢ ∼(a ⋎ b) :=
  .impI (.orE (.ax (a := a ⋎ b) (by simp))
    (.impE (a := a) (weaken (sub_cons2 _ _ _) ha) (.ax (a := a) (by simp)))
    (.impE (a := b) (weaken (sub_cons2 _ _ _) hb) (.ax (a := b) (by simp))))
def imp_of_notLeft {Γ a b} (h : Γ ⊢ ∼a) : Γ ⊢ (a ⇒ b) :=
  .impI (.flsE (.impE (a := a) (weaken (sub_cons _ _) h) (.ax (a := a) (by simp))))
def imp_of_right {Γ a b} (h : Γ ⊢ b) : Γ ⊢ (a ⇒ b) := .impI (weaken (sub_cons _ _) h)
def notImp {Γ a b} (ha : Γ ⊢ a) (hb : Γ ⊢ ∼b) : Γ ⊢ ∼(a ⇒ b) :=
  .impI (.impE (a := b) (weaken (sub_cons _ _) hb)
    (.impE (a := a) (.ax (a := a ⇒ b) (by simp)) (weaken (sub_cons _ _) ha)))
def notFls {Γ : List Form} : Γ ⊢ ∼Form.fls := .impI (.ax (a := Form.fls) (by simp))

/-- Excluded middle, in any context. -/
def dEM (Γ : List Form) (a : Form) : Γ ⊢ (a ⋎ ∼a) :=
  .raa <| .impE (a := a ⋎ ∼a) (.ax (a := ∼(a ⋎ ∼a)) (by simp))
    (.orI₂ (.impI (.impE (a := a ⋎ ∼a) (.ax (a := ∼(a ⋎ ∼a)) (by simp))
      (.orI₁ (.ax (a := a) (by simp))))))

/-- Proof by cases on `p ∨ ∼p`. -/
def byCasesD {Γ : List Form} {p φ : Form} (d1 : (p :: Γ) ⊢ φ) (d2 : (∼p :: Γ) ⊢ φ) : Γ ⊢ φ :=
  .orE (dEM Γ p) d1 d2

/-! ### Literal contexts -/

/-- The literal for atom `i` under `v`: `var i` if true, `∼var i` if false. -/
def lit (v : Nat → Bool) (i : Nat) : Form := if v i then Form.var i else ∼(Form.var i)

/-- The assumptions describing `v` on atoms `0 .. n-1`. -/
def litCtx (v : Nat → Bool) : Nat → List Form
  | 0     => []
  | n + 1 => lit v n :: litCtx v n

theorem lit_mem (v : Nat → Bool) (i n : Nat) (h : i < n) : lit v i ∈ litCtx v n := by
  induction n with
  | zero => omega
  | succ k ih =>
      cases Nat.lt_or_ge i k with
      | inl h' => exact List.Mem.tail _ (ih h')
      | inr h' => have he : i = k := by omega
                  subst he; exact List.Mem.head _

theorem lit_mem_pos (v) (i n) (hv : v i = true) (h : i < n) : Form.var i ∈ litCtx v n := by
  have m := lit_mem v i n h; simp [lit, hv] at m; exact m
theorem lit_mem_neg (v) (i n) (hv : v i = false) (h : i < n) : ∼(Form.var i) ∈ litCtx v n := by
  have m := lit_mem v i n h; simp [lit, hv] at m; exact m

/-! ### Kalmár's lemma

For every `φ` (with all atoms `< n`), the literal context `litCtx v n` proves `φ` when `v` makes it
true, and `∼φ` when `v` makes it false. By induction on `φ`, using the derived rules above. -/
noncomputable def kalmar (v : Nat → Bool) (n : Nat) : ∀ (φ : Form), φ.maxVar ≤ n →
    (eval v φ = true → litCtx v n ⊢ φ) × (eval v φ = false → litCtx v n ⊢ ∼φ) := by
  intro φ
  induction φ with
  | var i =>
      intro hb; simp only [Form.maxVar] at hb; have hi : i < n := by omega
      exact ⟨fun he => by simp only [eval] at he; exact .ax (lit_mem_pos v i n he hi),
             fun he => by simp only [eval] at he; exact .ax (lit_mem_neg v i n he hi)⟩
  | fls => intro _; exact ⟨fun he => by simp [eval] at he, fun _ => notFls⟩
  | and a b iha ihb =>
      intro hb; simp only [Form.maxVar] at hb
      have ca := iha (by omega); have cb := ihb (by omega)
      refine ⟨fun he => ?_, fun he => ?_⟩
      · simp only [eval] at he
        cases hva : eval v a with
        | false => rw [hva] at he; simp at he
        | true => cases hvb : eval v b with
          | false => rw [hva, hvb] at he; simp at he
          | true => exact .andI (ca.1 hva) (cb.1 hvb)
      · simp only [eval] at he
        cases hva : eval v a with
        | false => exact notAnd_left (ca.2 hva)
        | true => rw [hva] at he; simp at he; exact notAnd_right (cb.2 he)
  | or a b iha ihb =>
      intro hb; simp only [Form.maxVar] at hb
      have ca := iha (by omega); have cb := ihb (by omega)
      refine ⟨fun he => ?_, fun he => ?_⟩
      · simp only [eval] at he
        cases hva : eval v a with
        | true => exact .orI₁ (ca.1 hva)
        | false => rw [hva] at he; simp at he; exact .orI₂ (cb.1 he)
      · simp only [eval] at he
        cases hva : eval v a with
        | true => rw [hva] at he; simp at he
        | false => rw [hva] at he; simp at he; exact notOr (ca.2 hva) (cb.2 he)
  | imp a b iha ihb =>
      intro hb; simp only [Form.maxVar] at hb
      have ca := iha (by omega); have cb := ihb (by omega)
      refine ⟨fun he => ?_, fun he => ?_⟩
      · simp only [eval] at he
        cases hva : eval v a with
        | false => exact imp_of_notLeft (ca.2 hva)
        | true => rw [hva] at he; simp at he; exact imp_of_right (cb.1 he)
      · simp only [eval] at he
        cases hva : eval v a with
        | false => rw [hva] at he; simp at he
        | true => rw [hva] at he; simp at he; exact notImp (ca.1 hva) (cb.2 he)

/-! ### Variable elimination -/

/-- Update a valuation at one atom. -/
def upd (v : Nat → Bool) (n : Nat) (b : Bool) : Nat → Bool := fun k => if k = n then b else v k

theorem litCtx_congr {v w : Nat → Bool} :
    ∀ n, (∀ i, i < n → v i = w i) → litCtx v n = litCtx w n := by
  intro n; induction n with
  | zero => intro _; rfl
  | succ k ih =>
      intro h
      have hk : v k = w k := h k (by omega)
      have hrec : litCtx v k = litCtx w k := ih (fun i hi => h i (by omega))
      simp only [litCtx, hrec]; congr 1; simp only [lit, hk]

theorem litCtx_upd (v : Nat → Bool) (n : Nat) (b : Bool) : litCtx (upd v n b) n = litCtx v n :=
  litCtx_congr n (fun i hi => by simp only [upd, if_neg (Nat.ne_of_lt hi)])
theorem lit_upd_true (v : Nat → Bool) (n : Nat) : lit (upd v n true) n = Form.var n := by simp [lit, upd]
theorem lit_upd_false (v : Nat → Bool) (n : Nat) : lit (upd v n false) n = ∼(Form.var n) := by simp [lit, upd]

/-- If a goal is provable under *every* `n`-atom literal context, it's provable from `[]`:
    eliminate atom `n` with `byCasesD`, recurse. -/
noncomputable def elim : ∀ (n : Nat) (φ : Form), (∀ v, litCtx v n ⊢ φ) → ([] ⊢ φ)
  | 0,     _, h => h (fun _ => false)
  | n + 1, φ, h =>
    elim n φ (fun v => by
      have d1 : (Form.var n :: litCtx v n) ⊢ φ := by
        have hh := h (upd v n true);  simp only [litCtx, lit_upd_true, litCtx_upd] at hh; exact hh
      have d2 : (∼(Form.var n) :: litCtx v n) ⊢ φ := by
        have hh := h (upd v n false); simp only [litCtx, lit_upd_false, litCtx_upd] at hh; exact hh
      exact byCasesD d1 d2)

end Principia.Form
