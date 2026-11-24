import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3690 : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : Fin x1), (x5, x3 x5) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x7 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x1), (x8, x9) ∈ x2 ∧ x7 (Fin.castAdd x1 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) → (2 : ℕ) * x1 ≤ x4.size + (1 : ℕ) := by
  sorry
