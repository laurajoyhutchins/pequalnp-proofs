import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_141 : ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size ≤ 25 ∧ PEqualNP.MetaComplexity.circuitFun 17 D = (fun x : Fin 17 → Bool => decide (∃ i j : Fin 17, ((i.val + 1 = j.val ∧ i.val ≠ 8) ∨ (i.val = 0 ∧ (j.val = 8 ∨ j.val = 9 ∨ j.val = 16))) ∧ x i = true ∧ x j = true)) := by
  sorry
