import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2775 : ∃ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (T L : Finset ℕ) (i₁ i₂ a b c : ℕ),
  PEqualNP.TopForm.IsAO2 n C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ PEqualNP.MetaComplexity.NestedCover.IsOrTree n C T L C.output ∧
  n + i₁ ∈ L ∧ n + i₂ ∈ L ∧ i₁ ≠ i₂ ∧
  (PEqualNP.MetaComplexity.NestedCover.gateAt C i₁).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C i₁).inputs = [a, b] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C i₁).inputs = [b, a]) ∧
  (PEqualNP.MetaComplexity.NestedCover.gateAt C i₂).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C i₂).inputs = [a, c] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C i₂).inputs = [c, a]) ∧
  (∀ k < C.gates.length, k ∉ T → n + i₁ ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs ∧ n + i₂ ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs ∧
    ∀ j ∈ T, n + j ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) ∧
  ¬ (∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧
  PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C ∧ D.size + 1 ≤ C.size) := by
  sorry
