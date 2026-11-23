import Mathlib

theorem PEqualNP.Research.DiagnosticSmoke : ∀ (x y : ℂ), (x + y) * (x - y) = x^2 - y^2 := by
  intro x y
  ring
