import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_913 : ∃ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 13 → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates.length ≤ 38 ∧ (∀ (w : Fin 13) (x : Fin 13 → Bool), 9 ≤ (Finset.univ.filter (fun i : Fin 13 => x i = true)).card → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)), x v = true)) := by
  sorry
