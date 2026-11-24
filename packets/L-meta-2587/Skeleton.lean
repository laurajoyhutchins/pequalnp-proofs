import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2587 : ¬ (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < x1.gates.length →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and →           x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).inputs →             have x9 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.CircuitMoves.eraseGate (26 : ℕ) x1 x2 x3;             PEqualNP.MetaComplexity.Monotone2 x9 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x9 ∧ x9.size < x1.size ∧ ∀ (x10 : List Bool), x10.length = (26 : ℕ) → (x1.eval x10 = Bool.true → x9.eval x10 = Bool.true) ∧ ((x1.wires x10).getD ((26 : ℕ) + x2) Bool.false = (x1.wires x10).getD x3 Bool.false → x9.eval x10 = x1.eval x10)) := by
  sorry
