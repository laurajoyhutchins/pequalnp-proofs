import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3362 : ∀ (x1 x2 x3 : ℕ) (x4 : Fin x1 → Fin x1 → Prop) [x5 : DecidableRel x4], (∀ (x6 : Fin x1), Fintype.card { x7 : Fin x1 // x4 x7 x6 } = x2) → (∀ (x7 x8 : Fin x1), x7 ≠ x8 → ∃! x10 : Fin x1, x4 x7 x10 ∧ x4 x8 x10) → ∀ (x8 x9 : Fin x3 → Finset (Fin x1)), (∀ (x10 : Fin x3), ∀ x11 ∈ x8 x10, ∀ x13 ∈ x9 x10, x4 x11 x13) → (∀ (x11 x12 : Fin x1), x4 x11 x12 → ∃ (x14 : Fin x3), x11 ∈ x8 x14 ∧ x12 ∈ x9 x14) → x1 * x2 ≤ ∑ x12 : Fin x3, ((x8 x12).card + (x9 x12).card) := by
  sorry
