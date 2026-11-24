import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1798 : ∀ (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C → ∀ (j a b : ℕ), C.gates[j]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ → a < P + L + j → b < P + L + j → ∀ w : Fin L, PEqualNP.LowMerge.IsLow P L inc C (P + L + j) w → PEqualNP.LowMerge.IsLow P L inc C a w ∨ PEqualNP.LowMerge.IsLow P L inc C b w := by
  sorry
