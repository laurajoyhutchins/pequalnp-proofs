import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_gct_086 : ∃ C : ℕ, ∀ (n : ℕ) (L : Submodule ℂ (Fin n × Fin n → ℂ)), (∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) = (Nat.factorial n : ℂ)) → Module.finrank ℂ L ≤ C * n := by
  sorry
