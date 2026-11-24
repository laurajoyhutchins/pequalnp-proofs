import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2075 : ¬ (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x4 → x2.support.ncard ≤ x4.size + (1 : ℕ)) := by
  sorry
