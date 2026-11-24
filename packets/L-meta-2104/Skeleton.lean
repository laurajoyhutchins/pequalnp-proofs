import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2104 : ¬ (∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (x4 x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x4 → PEqualNP.MetaComplexity.Monotone2 x5 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x2 x5 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size ≤ x4.size + x5.size + (1 : ℕ) ∧ ∀ (x11 : Fin x2 → Bool), PEqualNP.MetaComplexity.circuitFun x2 x10 x11 = ((PEqualNP.MetaComplexity.circuitFun x1 x4 fun (x12 : Fin x1) => x11 (x3 x12)) || PEqualNP.MetaComplexity.circuitFun x2 x5 x11)) := by
  sorry
