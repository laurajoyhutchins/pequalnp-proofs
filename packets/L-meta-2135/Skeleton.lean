import Mathlib
import PEqualNP.Defs
import PEqualNP.Library.LRAT.Checker
import PEqualNP.Library.LRAT.Link

theorem PEqualNP.Outside.L_meta_2135 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack 5 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun z : Fin 5 → Bool => (z 0 && z 2) || (z 0 && z 3) || (z 0 && z 4) || (z 1 && z 2) || (z 1 && z 3) || (z 1 && z 4)) x) → 4 ≤ C.size := by
  sorry
