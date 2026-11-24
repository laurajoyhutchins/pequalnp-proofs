import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2621 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → ∀ (x3 : ℕ) (x4 : List Bool), ∃ (x5 : ℕ → Bool), (∀ x6 < (26 : ℕ), x5 x6 = Decidable.decide (x6 = x3)) ∧ ∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ), x1.gates[x6]? = Option.some x7 → x7.inputs = [x8, x9] → (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((26 : ℕ) + x6) = (x4.getD x8 Bool.false && x5 x9 || x5 x8 && x4.getD x9 Bool.false)) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((26 : ℕ) + x6) = (x5 x8 || x5 x9)) := by
  sorry
