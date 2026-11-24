import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_gct_231 : ∃ L : Submodule ℂ (Fin 4 × Fin 4 → ℂ), Module.finrank ℂ L = 3 ∧ (∀ t ∈ L, ∀ i j : Fin 4, t (i, j) = t (j, i)) ∧ ∀ t ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + t (i, j)) = 24 := by
  sorry
