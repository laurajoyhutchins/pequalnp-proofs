import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1883 : ¬ (∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∃ x12 ∈ PEqualNP.TopForm.junk x3 x7, PEqualNP.EdgeOwnership.InCone x2 x7 x11 x12) → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ))) := by
  sorry
