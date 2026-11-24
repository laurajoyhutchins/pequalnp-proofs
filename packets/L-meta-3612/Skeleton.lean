import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3612 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; ∀ (x3 : Fin (9 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 ≠ (0 : Fin (9 : ℕ)) → x3 ≠ (6 : Fin (9 : ℕ)) → PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (13 : ℕ) → ∃ (x9 : Fin (9 : ℕ) → Bool), x4.eval ((x2 x9).set ↑x3 !x9 x3) ≠ x1 x9 := by
  sorry
