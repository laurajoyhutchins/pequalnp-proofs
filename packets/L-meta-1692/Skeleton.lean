import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1692 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < 26 + (i : ℕ)) → (∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u1 : Fin 13 => decide (u1 = p)) ++ List.ofFn (fun v1 : Fin 13 => decide (v1 = l))) = true) → (∀ Q : Finset (Fin 13), Q.card = 4 → (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ Q)) ++ List.ofFn (fun v2 : Fin 13 => decide (∀ r ∈ Q, r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13))))) = false) → 64 ≤ gates.length := by
  sorry
