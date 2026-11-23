import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L112
import PEqualNP.MetaComplexity.L153

theorem PEqualNP.Outside.L_meta_765 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) s ↔ 5 ≤ s := by
  sorry
