import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_gct_210 : ∀ L : Submodule ℂ (Fin 5 × Fin 5 → ℂ), (∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) → Module.finrank ℂ L ≤ 8 := by
  sorry
