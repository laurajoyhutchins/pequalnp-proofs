import Mathlib
import PEqualNP.Defs
import PEqualNP.Library.LRAT.Checker
import PEqualNP.Library.LRAT.Link

theorem PEqualNP.Outside.L_meta_2121 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack 4 C → (∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun z : Fin 4 → Bool => (z 0 && z 2) || (z 0 && z 3) || (z 1 && z 2) || (z 1 && z 3)) x) → 3 ≤ C.size := by
  sorry
