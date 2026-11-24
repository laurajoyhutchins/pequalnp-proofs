import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3212 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ x3 ∈ x1.gates, x3.op = PEqualNP.CircuitLowerBounds.GateOp.not → x3.inputs.length ≤ (1 : ℕ)) → (List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x5 : ℕ) => x4.inputs.contains x5) x1.gates).length = (2 : ℕ) → (∀ (x5 : Fin (8 : ℕ) → Bool), x1.eval (Bool.false :: List.ofFn x5 ++ [Bool.true]) = [(1 : ℕ), (10 : ℕ), (19 : ℕ), (5 : ℕ), (14 : ℕ), (23 : ℕ), (38 : ℕ), (47 : ℕ), (60 : ℕ)].any fun (x6 : ℕ) => x5 (Fin.ofNat (8 : ℕ) (x6 / (8 : ℕ))) && x5 (Fin.ofNat (8 : ℕ) (x6 % (8 : ℕ)))) → (14 : ℕ) ≤ x1.size := by
  sorry
