import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1877 : ¬ (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 : Fin x1) (x5 : x2.Walk x4 x4), x5.IsCycle → (5 : ℕ) ≤ x5.length) → x2.edgeFinset.Nonempty → ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x6 → PEqualNP.TopForm.TopForm x2 x6 → PEqualNP.TopForm.junk x2 x6 = ∅ → PEqualNP.TopForm.Ustar x2 x6 = ∅) := by
  sorry
