import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_gct_228 : ∃ L : Submodule (ZMod 5) (Fin 3 × Fin 3 → ZMod 5), Module.finrank (ZMod 5) L = 4 ∧ ∀ t ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 3) => (1 : ZMod 5) + t (i, j)) = 6 := by
  sorry
