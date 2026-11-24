import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2108 : ¬ (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 x5 x6 x7 : Fin x1), x4 ≠ x5 → x4 ≠ x6 → x4 ≠ x7 → x5 ≠ x6 → x5 ≠ x7 → x6 ≠ x7 → x2.Adj x4 x5 → x2.Adj x5 x6 → x2.Adj x6 x7 → ¬x2.Adj x7 x4) → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x6 : Fin x1 → Bool), x3.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8 ∧ x6 x7 = Bool.true ∧ x6 x8 = Bool.true) → ∃ (x7 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x7 ∧ x7.card ≤ {x8 : Fin x3.gates.length | (x3.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard) := by
  sorry
