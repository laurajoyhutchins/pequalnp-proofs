import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3630 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card ≤ (2 : ℕ) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ (x5.size ≤ x1.size + if x2.card ≤ (1 : ℕ) ∨ x2 = {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} then (1 : ℕ) else (2 : ℕ)) ∧ ∀ (x6 : Fin (9 : ℕ) → Bool), x5.eval (List.ofFn x6 ++ [Bool.false]) = x1.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x7 ∈ x2, x6 x7 = Bool.true)]) := by
  sorry
