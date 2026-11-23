import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_911 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, ∃ o : Fin 3 → Fin 3 → ℕ,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    (∀ i j : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not →
      (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) ∧
    C.size ≤ 18 ∧
    (C.size = 18 → ∃ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
    ∀ x : Fin 9 → Bool, ∀ a b : Fin 3,
      ((C.wires (List.ofFn x)).getD (o a b) false = true ↔
        ∃ c : Fin 3, ∃ k : Fin 9, (k : ℕ) = 3 * (c : ℕ) + ((a * c + b : Fin 3) : ℕ) ∧ x k = true) := by
  sorry
