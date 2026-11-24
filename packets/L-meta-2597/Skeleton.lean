import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2597 : ¬ (∀ (x1 : ℕ) (x2 : Fin x1) (x3 : Bool → Bool) (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.output ≠ x1 → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x7 ∧ x7.size ≤ x4.size ∧ ∀ (x8 : Fin x1 → Bool), x7.eval (List.ofFn x8 ++ [!x8 x2]) = x4.eval (List.ofFn x8 ++ [x3 (x8 x2)])) := by
  sorry
