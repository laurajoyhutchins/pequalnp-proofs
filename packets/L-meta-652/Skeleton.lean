import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_652 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 15 ∧ ∃ o0 o1 o2 : ℕ, ∀ x : Fin 6 → Bool, (C.wires (List.ofFn x)).getD o0 false = ((x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) ∧ (C.wires (List.ofFn x)).getD o1 false = ((x 0 && x 4) || (x 1 && x 5) || (x 2 && x 3)) ∧ (C.wires (List.ofFn x)).getD o2 false = ((x 0 && x 5) || (x 1 && x 3) || (x 2 && x 4))) ∧ ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∃ o0 o1 o2 : ℕ, ∀ x : Fin 6 → Bool, (C.wires (List.ofFn x)).getD o0 false = ((x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) ∧ (C.wires (List.ofFn x)).getD o1 false = ((x 0 && x 4) || (x 1 && x 5) || (x 2 && x 3)) ∧ (C.wires (List.ofFn x)).getD o2 false = ((x 0 && x 5) || (x 1 && x 3) || (x 2 && x 4))) := by
  sorry
