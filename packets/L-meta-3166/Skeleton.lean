import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3166 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x2 = (0 : ℕ) ∨ x2 = (2 : ℕ) → PEqualNP.MetaComplexity.FanInTwo x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (10 : ℕ) x1 → x1.output ≠ (9 : ℕ) → List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide ((9 : ℕ) ∈ x8.inputs)) x1.gates = [x3] → x3.op = PEqualNP.CircuitLowerBounds.GateOp.or → x3.inputs = [(9 : ℕ), x2] ∨ x3.inputs = [x2, (9 : ℕ)] → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x11 ∧ x11.size + (1 : ℕ) = x1.size ∧ ∀ (x12 : Fin (9 : ℕ) → Bool), x11.eval (List.ofFn x12) = x1.eval (List.ofFn x12 ++ [x12 (0 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ))]) := by
  sorry
