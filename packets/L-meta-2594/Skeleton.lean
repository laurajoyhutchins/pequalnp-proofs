import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2594 : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size = x3.size ∧ ∀ (x6 : Fin x1 → Bool) (x7 : Bool), x5.eval (List.ofFn x6 ++ [x7]) = x3.eval (List.ofFn (x6 ∘ x2) ++ [x7]) := by
  sorry
