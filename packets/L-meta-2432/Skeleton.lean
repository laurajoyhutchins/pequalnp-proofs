import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2432 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 : Fin x1) (x5 : x2.Walk x4 x4), x5.IsCycle → (5 : ℕ) ≤ x5.length) → ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x7 : Fin x1), PEqualNP.MetaComplexity.circuitFun x1 x5 (PEqualNP.EdgeOwnership.pairInput x7 x7) = Bool.false) → (∀ (x8 : ℕ), ¬((PEqualNP.MetaComplexity.NestedCover.gateAt x5 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x9 : Fin x1) (x10 : Fin x1), ¬x2.Adj x9 x10 ∧ PEqualNP.EdgeOwnership.gateVal x1 x5 x8 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true)) → {x9 ∈ x2.edgeFinset | (PEqualNP.MetaComplexity.circuitFun x1 x5 fun (x10 : Fin x1) => Decidable.decide (x10 ∈ x9)) = Bool.true}.card ≤ x5.size := by
  sorry
