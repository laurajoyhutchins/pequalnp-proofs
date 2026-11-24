import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3268 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size = (8 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) → ∀ (x6 : Finset ℕ), x6.card ≤ (6 : ℕ) → ∃ (x8 : Fin (9 : ℕ) → Bool) (x9 : Fin (9 : ℕ) → Bool), (∀ x10 ∈ x6, (x2.wires (List.ofFn x8)).getD x10 Bool.false = (x2.wires (List.ofFn x9)).getD x10 Bool.false) ∧ x1 x8 ≠ x1 x9 := by
  sorry
