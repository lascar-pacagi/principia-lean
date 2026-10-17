import Principia.FirstOrder.Resolution

namespace Principia.FirstOrder.Propositional

inductive Proof (T : Clause → Prop) : Clause → Type where
  | input {c} : T c → Proof T c
  | tautology (l : Literal) : Proof T [l, l.complement]
  | weakening {c d} : Proof T c → (∀ l ∈ c, l ∈ d) → Proof T d
  | resolve {c d} (l : Literal) : Proof T c → Proof T d → Proof T (resolvent c d l)

def Consistent (T : Clause → Prop) := ¬Nonempty (Proof T [])
def add (T : Clause → Prop) (l : Literal) := fun c => T c ∨ c = [l]
def positive (a : Atom) : Literal := ⟨true, a⟩

theorem complement_complement (l : Literal) : l.complement.complement = l := by
  cases l with | mk b a => cases b <;> rfl

def Proof.mapSource {T U : Clause → Prop} (h : ∀ c, T c → U c) :
    {c : Clause} → Proof T c → Proof U c
  | _, .input ht => .input (h _ ht)
  | _, .tautology l => .tautology l
  | _, .weakening d hd => .weakening (d.mapSource h) hd
  | _, .resolve l d e => .resolve l (d.mapSource h) (e.mapSource h)

theorem erase_append_subset (c : Clause) (l k : Literal) :
    ∀ x ∈ (c ++ [k]).erase l, x ∈ c.erase l ++ [k] := by
  by_cases h : l ∈ c
  · rw [List.erase_append_left _ h]; exact fun _ hx => hx
  · rw [List.erase_append_right _ h, List.erase_of_not_mem h]
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ (List.mem_of_mem_erase hx)

noncomputable def Proof.deduction {T : Clause → Prop} {l : Literal} :
    {c : Clause} → Proof (add T l) c → Proof T (c ++ [l.complement])
  | c, .input h => by
    classical
    exact if ht : T c then .weakening (.input ht) (fun _ hm => List.mem_append_left _ hm)
    else (show c = [l] from h.resolve_left ht) ▸ (Proof.tautology l)
  | _, .tautology k => .weakening (.tautology k) (fun _ h => List.mem_append_left _ h)
  | _, .weakening d hd => .weakening d.deduction (by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ (hd x hx)
      · exact List.mem_append_right _ hx)
  | _, @Proof.resolve _ c d k left right =>
    .weakening (.resolve k left.deduction right.deduction) (by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp (erase_append_subset c k l.complement x hx) with h | h
        · exact List.mem_append_left _ (List.mem_append_left _ h)
        · exact List.mem_append_right _ h
      · rcases List.mem_append.mp (erase_append_subset d k.complement l.complement x hx) with h | h
        · exact List.mem_append_left _ (List.mem_append_right _ h)
        · exact List.mem_append_right _ h)

theorem consistent_choice {T : Clause → Prop} (hT : Consistent T) (l : Literal) :
    Consistent (add T l) ∨ Consistent (add T l.complement) := by
  classical
  apply Classical.byContradiction
  intro h
  have hl : ¬Consistent (add T l) := fun hc => h (Or.inl hc)
  have hr : ¬Consistent (add T l.complement) := fun hc => h (Or.inr hc)
  obtain ⟨dl⟩ := Classical.not_not.mp hl
  obtain ⟨dr⟩ := Classical.not_not.mp hr
  have left : Proof T [l.complement] := dl.deduction
  have right : Proof T [l] := by simpa [complement_complement] using dr.deduction
  exact hT ⟨by simpa [resolvent] using Proof.resolve l right left⟩

noncomputable def choose (T : Clause → Prop) (a : Atom) : Clause → Prop := by
  classical
  exact if Consistent (add T (positive a)) then add T (positive a)
  else add T (positive a).complement

theorem choose_extends (T : Clause → Prop) (a : Atom) : ∀ c, T c → choose T a c := by
  classical
  intro c hc
  unfold choose
  split <;> exact Or.inl hc

theorem choose_consistent {T : Clause → Prop} (hT : Consistent T) (a : Atom) :
    Consistent (choose T a) := by
  classical
  unfold choose
  split
  · assumption
  · rename_i h; exact (consistent_choice hT (positive a)).resolve_left h

theorem choose_decides (T : Clause → Prop) (a : Atom) :
    choose T a [positive a] ∨ choose T a [(positive a).complement] := by
  classical
  unfold choose
  split
  · exact Or.inl (Or.inr rfl)
  · exact Or.inr (Or.inr rfl)

noncomputable def chooseAll (T : Clause → Prop) : List Atom → Clause → Prop
  | [] => T
  | a :: rest => chooseAll (choose T a) rest

theorem chooseAll_extends (T : Clause → Prop) (atoms : List Atom) :
    ∀ c, T c → chooseAll T atoms c := by
  induction atoms generalizing T with
  | nil => exact fun _ h => h
  | cons a rest ih => exact fun c h => ih _ c (choose_extends T a c h)

theorem chooseAll_consistent {T : Clause → Prop} (hT : Consistent T) (atoms : List Atom) :
    Consistent (chooseAll T atoms) := by
  induction atoms generalizing T with
  | nil => exact hT
  | cons a rest ih => exact ih (choose_consistent hT a)

theorem chooseAll_decides (T : Clause → Prop) (atoms : List Atom) {a : Atom}
    (ha : a ∈ atoms) :
    chooseAll T atoms [positive a] ∨ chooseAll T atoms [(positive a).complement] := by
  induction atoms generalizing T with
  | nil => cases ha
  | cons b rest ih =>
    rcases List.mem_cons.mp ha with he | hr
    · subst b
      exact (choose_decides T a).imp
        (chooseAll_extends (choose T a) rest _)
        (chooseAll_extends (choose T a) rest _)
    · exact ih _ hr

noncomputable def stage (pool : Nat → List Atom) (T : Clause → Prop) : Nat → Clause → Prop
  | 0 => T
  | n + 1 => chooseAll (stage pool T n) (pool n)

theorem stage_step (pool : Nat → List Atom) (T : Clause → Prop) (n : Nat) :
    ∀ c, stage pool T n c → stage pool T (n+1) c := chooseAll_extends _ _

theorem stage_mono (pool : Nat → List Atom) (T : Clause → Prop) {m n : Nat} (h : m ≤ n) :
    ∀ c, stage pool T m c → stage pool T n c := by
  induction n with
  | zero =>
    have he : m = 0 := by omega
    subst m
    exact fun _ hc => hc
  | succ n ih =>
    by_cases he : m = n+1
    · subst m; exact fun _ hc => hc
    · exact fun c hc => stage_step pool T n c (ih (by omega) c hc)

theorem stage_consistent {T : Clause → Prop} (hT : Consistent T)
    (pool : Nat → List Atom) (n : Nat) : Consistent (stage pool T n) := by
  induction n with
  | zero => exact hT
  | succ n ih => exact chooseAll_consistent ih _

noncomputable def valuation (pool : Nat → List Atom) (T : Clause → Prop) (a : Atom) : Prop :=
  ∃ n, stage pool T n [positive a]
def Holds (v : Atom → Prop) (l : Literal) : Prop := if l.positive then v l.atom else ¬v l.atom

theorem false_eventually (pool : Nat → List Atom) (covers : ∀ a, ∃ n, a ∈ pool n)
    (T : Clause → Prop) (l : Literal) (h : ¬Holds (valuation pool T) l) :
    ∃ n, stage pool T n [l.complement] := by
  classical
  cases l with
  | mk b a =>
    cases b with
    | false =>
      have hv : valuation pool T a := Classical.not_not.mp h
      simpa only [valuation, Literal.complement, positive, Bool.not_false] using hv
    | true =>
      obtain ⟨n, hn⟩ := covers a
      have decided := chooseAll_decides (stage pool T n) (pool n) hn
      rcases decided with hp | hn
      · exact False.elim (h ⟨n+1, hp⟩)
      · exact ⟨n+1, hn⟩

theorem common_stage (pool : Nat → List Atom) (T : Clause → Prop) (c : Clause)
    (h : ∀ l ∈ c, ∃ n, stage pool T n [l.complement]) :
    ∃ n, ∀ l ∈ c, stage pool T n [l.complement] := by
  induction c with
  | nil => exact ⟨0, by simp⟩
  | cons l rest ih =>
    obtain ⟨n, hn⟩ := h l (by simp)
    obtain ⟨m, hm⟩ := ih (fun k hk => h k (by simp [hk]))
    exact ⟨max n m, by
      intro k hk
      rcases List.mem_cons.mp hk with he | hr
      · subst k; exact stage_mono pool T (Nat.le_max_left ..) _ hn
      · exact stage_mono pool T (Nat.le_max_right ..) _ (hm k hr)⟩

noncomputable def Proof.refuteFalsified {T : Clause → Prop} {c : Clause} (d : Proof T c)
    (opposite : ∀ l ∈ c, T [l.complement]) : Proof T [] := by
  induction c with
  | nil => exact d
  | cons l rest ih =>
    have next : Proof T rest := by
      simpa [resolvent] using Proof.resolve l d (.input (opposite l (by simp)))
    exact ih next (fun k hk => opposite k (by simp [hk]))

theorem model_of_consistent {T : Clause → Prop} (hT : Consistent T)
    (pool : Nat → List Atom) (covers : ∀ a, ∃ n, a ∈ pool n) :
    ∀ c, T c → ∃ l ∈ c, Holds (valuation pool T) l := by
  classical
  intro c hc
  apply Classical.byContradiction
  intro h
  have each : ∀ l ∈ c, ∃ n, stage pool T n [l.complement] := by
    intro l hl
    exact false_eventually pool covers T l (fun ht => h ⟨l, hl, ht⟩)
  obtain ⟨n, hn⟩ := common_stage pool T c each
  exact stage_consistent hT pool n
    ⟨Proof.refuteFalsified (.input (stage_mono pool T (Nat.zero_le n) c hc)) hn⟩

end Principia.FirstOrder.Propositional
