import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3434 : ∀ (x1 : ℕ → ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : List Bool), x3.length = x4.length → (∀ (x6 : ℕ), x3.length ≤ x6 → x1 x6 = x6) → (∀ x7 < x3.length, x1 x7 < x3.length ∨ x3.length + x2.size ≤ x1 x7) → (∀ (x8 : ℕ), x4.getD (x1 x8) Bool.false = x3.getD x8 Bool.false) → { gates := List.map (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => { op := x9.op, inputs := List.map x1 x9.inputs : PEqualNP.CircuitLowerBounds.Gate }) x2.gates, output := x1 x2.output : PEqualNP.CircuitLowerBounds.Circuit }.eval x4 = x2.eval x3 := by
  sorry
