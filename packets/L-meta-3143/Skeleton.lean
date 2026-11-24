import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3143 : ∀ (x1 : Fin (8 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x4 : Fin (8 : ℕ) → Bool), x2.eval (List.ofFn x4 ++ [!x4 x1, Bool.true, Bool.false]) = (fun (x5 : Fin (8 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (37 : ℕ), (46 : ℕ), (57 : ℕ), (74 : ℕ)].any fun (x6 : ℕ) => x5 (Fin.ofNat (8 : ℕ) (x6 / (10 : ℕ))) && x5 (Fin.ofNat (8 : ℕ) (x6 % (10 : ℕ)))) x4) → (13 : ℕ) ≤ x2.size := by
  sorry
