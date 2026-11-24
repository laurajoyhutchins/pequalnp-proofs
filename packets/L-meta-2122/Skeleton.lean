import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2122 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 4 C ∧ C.size ≤ 2 ∧ ∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun z : Fin 4 → Bool => (z 0 && z 2) || (z 0 && z 3) || (z 1 && z 2) || (z 1 && z 3)) x := by
  sorry
