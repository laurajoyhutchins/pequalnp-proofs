import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1412 : ¬ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → C.size = 8 → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = true ↔ ∃ i : Fin 6, x i = true ∧ x (i + 1) = true) → ∃ (p : Fin 6) (b : Bool) (S : Finset (Fin 8)), (if b = true then 4 else 3) ≤ S.card ∧ ∀ j ∈ S, (∀ y z : Fin 6 → Bool, y p = b → z p = b → (C.wires (List.ofFn y)).getD (6 + ((j : Fin 8) : ℕ)) false = (C.wires (List.ofFn z)).getD (6 + ((j : Fin 8) : ℕ)) false) ∨ ∃ w < 6 + ((j : Fin 8) : ℕ), ∀ u : Fin 6 → Bool, u p = b → (C.wires (List.ofFn u)).getD (6 + ((j : Fin 8) : ℕ)) false = (C.wires (List.ofFn u)).getD w false) := by
  sorry
