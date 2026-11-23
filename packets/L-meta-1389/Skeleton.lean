import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_529
import PEqualNP.Outside.L_meta_1046
import PEqualNP.Outside.L_meta_1330
import PEqualNP.Outside.L_meta_1332
import PEqualNP.Outside.L_meta_1333
import PEqualNP.Outside.L_meta_1346
import PEqualNP.Outside.L_meta_1347
import PEqualNP.Outside.L_meta_1350
import PEqualNP.Outside.L_meta_1351
import PEqualNP.Outside.L_meta_1354
import PEqualNP.MetaComplexity.L1352
import PEqualNP.MetaComplexity.L1372

theorem PEqualNP.Outside.L_meta_1389 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 7 → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin 1, ι j = i) → (∀ (o : Fin 7) (x : Fin 7 → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ (![{0, 1, 3}, {1, 2, 4}, {2, 3, 5}, {3, 4, 6}, {0, 4, 5}, {1, 5, 6}, {0, 2, 6}] : Fin 7 → Finset (Fin 7)) o, x v = true)) → 14 ≤ gates.length := by
  sorry
