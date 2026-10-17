import Principia.FirstOrder.Resolution
import Principia.FirstOrder.NaturalDeductionSearch

namespace Principia.FirstOrder

namespace Enumeration

def terms : Nat → List Term
  | 0 => []
  | n+1 => terms n ++ (List.range (n+1)).map Term.variable ++
      (List.range (n+1)).flatMap (fun f =>
        (argumentLists (terms n) (n+1)).map (Term.function f))

theorem step (n : Nat) : ∀ t ∈ terms n, t ∈ terms (n+1) := by
  intro t ht
  exact List.mem_append_left _ (List.mem_append_left _ ht)

theorem mono {m n : Nat} (h : m ≤ n) : ∀ t ∈ terms m, t ∈ terms n := by
  induction n with
  | zero => have he : m = 0 := by omega
            subst m
            exact fun _ ht => ht
  | succ n ih =>
    by_cases he : m = n+1
    · subst m; exact fun _ ht => ht
    · exact fun t ht => step n t (ih (by omega) t ht)

theorem arguments_mem {alphabet : List Term} {args : List Term} {n : Nat}
    (hl : args.length ≤ n) (ha : ∀ t ∈ args, t ∈ alphabet) :
    args ∈ argumentLists alphabet n := by
  induction n generalizing args with
  | zero => have he : args = [] := List.eq_nil_of_length_eq_zero (by omega)
            subst args
            simp [argumentLists]
  | succ n ih =>
    cases args with
    | nil => simp [argumentLists]
    | cons a rest =>
      apply List.mem_cons_of_mem
      exact List.mem_flatMap.mpr ⟨a, ha a (by simp),
        List.mem_map.mpr ⟨rest, ih (by simpa using hl) (fun t ht => ha t (by simp [ht])), rfl⟩⟩

theorem common (args : List Term) (h : ∀ t ∈ args, ∃ n, t ∈ terms n) :
    ∃ n, ∀ t ∈ args, t ∈ terms n := by
  induction args with
  | nil => exact ⟨0, by simp⟩
  | cons a rest ih =>
    obtain ⟨n, hn⟩ := h a (by simp)
    obtain ⟨m, hm⟩ := ih (fun t ht => h t (by simp [ht]))
    exact ⟨max n m, by
      intro t ht
      rcases List.mem_cons.mp ht with he | hr
      · subst t; exact mono (Nat.le_max_left ..) _ hn
      · exact mono (Nat.le_max_right ..) _ (hm t hr)⟩

theorem covers_term (t : Term) : ∃ n, t ∈ terms n := by
  cases t with
  | «variable» i =>
    exact ⟨i+1, List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩))⟩
  | function f args =>
    have each : ∀ a ∈ args, ∃ n, a ∈ terms n := by
      intro a ha
      exact covers_term a
    obtain ⟨n, hn⟩ := common args each
    let k := max n (max f args.length)
    have hargs : args ∈ argumentLists (terms k) (k+1) :=
      arguments_mem (by dsimp [k]; omega) (fun a ha => mono (Nat.le_max_left ..) a (hn a ha))
    exact ⟨k+1, List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨f, List.mem_range.mpr (by dsimp [k]; omega), List.mem_map.mpr ⟨args, hargs, rfl⟩⟩)⟩
termination_by sizeOf t
decreasing_by
  have hs := List.sizeOf_lt_of_mem ha
  simp only [Term.function.sizeOf_spec]
  omega

def atoms (n : Nat) : List Atom :=
  (List.range (n+1)).flatMap (fun p =>
    (argumentLists (terms n) n).map (fun args => ⟨p, args⟩))

theorem covers_atom (a : Atom) : ∃ n, a ∈ atoms n := by
  obtain ⟨n, hn⟩ := common a.arguments (fun t _ => covers_term t)
  let k := max n (max a.symbol a.arguments.length)
  exact ⟨k, List.mem_flatMap.mpr ⟨a.symbol,
    List.mem_range.mpr (by dsimp [k]; omega), List.mem_map.mpr ⟨a.arguments,
      arguments_mem (by dsimp [k]; omega)
        (fun t ht => mono (Nat.le_max_left ..) t (hn t ht)), by cases a; rfl⟩⟩⟩

end Enumeration

end Principia.FirstOrder
