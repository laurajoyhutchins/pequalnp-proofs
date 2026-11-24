import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2080 : ¬ (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x2 ∈ x1.gates, x2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x2.op = PEqualNP.CircuitLowerBounds.GateOp.or) → Monotone fun (x3 : Fin (26 : ℕ) → Bool) => x1.eval (List.ofFn x3)) := by
  sorry
