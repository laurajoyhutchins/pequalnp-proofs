import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1005 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 3 && x 5)) 9 := by
  sorry
