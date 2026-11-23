import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1413 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → C.size = 10 → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = true ↔ ∃ i : Fin 7, x i = true ∧ x (i + 1) = true) → ∃ (p : Fin 7) (b : Bool) (S : Finset (Fin 10)), (if b = true then 4 else 3) ≤ S.card ∧ ∀ j ∈ S, (∀ y z : Fin 7 → Bool, y p = b → z p = b → (C.wires (List.ofFn y)).getD (7 + ((j : Fin 10) : ℕ)) false = (C.wires (List.ofFn z)).getD (7 + ((j : Fin 10) : ℕ)) false) ∨ ∃ w < 7 + ((j : Fin 10) : ℕ), ∀ u : Fin 7 → Bool, u p = b → (C.wires (List.ofFn u)).getD (7 + ((j : Fin 10) : ℕ)) false = (C.wires (List.ofFn u)).getD w false := by
  sorry
