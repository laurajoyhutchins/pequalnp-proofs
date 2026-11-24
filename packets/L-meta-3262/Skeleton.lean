import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3262 : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x2 ∧ (x5, x8) ∈ x2 ∧ (x6, x7) ∈ x2 ∧ (x6, x8) ∈ x2)) → (∀ (x6 : Fin x1), (x6, x3 x6) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x8 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x1), (x9, x10) ∈ x2 ∧ x8 (Fin.castAdd x1 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → x2.card + x1 ≤ x4.size + (1 : ℕ) := by
  sorry
