import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2668 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → ∀ x7 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x7 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧ PEqualNP.MetaComplexity.circuitFun x1 (PEqualNP.CircuitMoves.eraseGate x1 x4 x7 (x1 + x4.gates.length)) (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.false := by
  sorry
