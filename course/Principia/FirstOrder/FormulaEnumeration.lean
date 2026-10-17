import Principia.FirstOrder.Enumeration

namespace Principia.FirstOrder

def Formula.code : Formula → Term
  | .predicate p args => .function 0 [.function p args]
  | .falsum => .function 1 []
  | .implies a b => .function 2 [a.code, b.code]
  | .conjunction a b => .function 3 [a.code, b.code]
  | .disjunction a b => .function 4 [a.code, b.code]
  | .universal a => .function 5 [a.code]
  | .existential a => .function 6 [a.code]

def Formula.decode : Term → Option Formula
  | .function 0 [.function p args] => some (.predicate p args)
  | .function 1 [] => some .falsum
  | .function 2 [a, b] => do return .implies (← decode a) (← decode b)
  | .function 3 [a, b] => do return .conjunction (← decode a) (← decode b)
  | .function 4 [a, b] => do return .disjunction (← decode a) (← decode b)
  | .function 5 [a] => do return .universal (← decode a)
  | .function 6 [a] => do return .existential (← decode a)
  | _ => none
termination_by t => sizeOf t

theorem Formula.decode_code (a : Formula) : Formula.decode a.code = some a := by
  induction a <;> simp_all [code, decode]

def Enumeration.formulas (n : Nat) : List Formula := (Enumeration.terms n).filterMap Formula.decode

theorem Enumeration.covers_formula (a : Formula) : ∃ n, a ∈ Enumeration.formulas n := by
  obtain ⟨n, hn⟩ := Enumeration.covers_term a.code
  exact ⟨n, List.mem_filterMap.mpr ⟨a.code, hn, a.decode_code⟩⟩

end Principia.FirstOrder
