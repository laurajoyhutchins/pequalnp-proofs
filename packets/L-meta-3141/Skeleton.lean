import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3141 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → Option.map PEqualNP.CircuitLowerBounds.Gate.op x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.not → x1.size ≤ (15 : ℕ) → x1.eval [Bool.true, Bool.false, Bool.false, Bool.false, Bool.true, Bool.false, Bool.false, Bool.false, Bool.false] ≠ x1.eval [Bool.true, Bool.false, Bool.false, Bool.false, Bool.false, Bool.false, Bool.false, Bool.false, Bool.false] → ∃ (x7 : Fin (8 : ℕ)) (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size ≤ (12 : ℕ) ∧ ∀ (x9 : Fin (8 : ℕ) → Bool), x8.eval (List.ofFn x9 ++ [!x9 x7, Bool.true, Bool.false]) = x1.eval (List.ofFn (Fin.insertNth (4 : Fin (9 : ℕ)) Bool.false x9)) := by
  sorry
