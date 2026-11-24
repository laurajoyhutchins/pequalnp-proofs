import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3511 : ∀ (x1 : Fin (9 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 →     (∀ x4 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x6 : Fin (9 : ℕ) → Bool := fun (x6 : Fin (9 : ℕ)) => x4.testBit ↑x6;         x2.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) || x6 x1]) = Decidable.decide (x4 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →       (14 : ℕ) ≤ x2.size := by
  sorry
