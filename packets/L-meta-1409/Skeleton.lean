import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1409 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → C.size = 7 → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = true ↔ ∃ i : Fin 5, x i = true ∧ x (i + 1) = true) → ∃ (p : Fin 5) (b : Bool) (S : Finset (Fin 7)), (if b = true then 4 else 3) ≤ S.card ∧ ∀ j ∈ S, (∀ y z : Fin 5 → Bool, y p = b → z p = b → (C.wires (List.ofFn y)).getD (5 + ((j : Fin 7) : ℕ)) false = (C.wires (List.ofFn z)).getD (5 + ((j : Fin 7) : ℕ)) false) ∨ ∃ w < 5 + ((j : Fin 7) : ℕ), ∀ u : Fin 5 → Bool, u p = b → (C.wires (List.ofFn u)).getD (5 + ((j : Fin 7) : ℕ)) false = (C.wires (List.ofFn u)).getD w false := by
  sorry
