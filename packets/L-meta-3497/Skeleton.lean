import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3497 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x4]? = Option.some x5 → ∃ (x7 : ℕ) (x8 : ℕ), x5.inputs = [x7, x8] ∧ x7 < x8 ∧ x8 < x1 + x4) → ∃ (x5 : ℕ → Finset (Finset (Fin x1))), (∀ (x6 : Fin x1), x5 ↑x6 = {{x6}}) ∧ (∀ (x6 : ℕ) (x7 : x6 < x2.size), ∃ (x8 : ℕ) (x9 : ℕ), x2.gates[x6].inputs = [x8, x9] ∧ x8 < x9 ∧ x9 < x1 + x6 ∧ x5 (x1 + x6) = if x2.gates[x6].op.eval [Bool.false, Bool.true] = Bool.true then (x5 x8).biUnion fun (x10 : Finset (Fin x1)) => Finset.image (fun (x11 : Finset (Fin x1)) => x10 ∪ x11) (x5 x9) else x5 x8 ∪ x5 x9) ∧ ∀ (x6 : List Bool), x6.length = x1 → ∀ (x8 : ℕ), (x2.wires x6).getD x8 Bool.false = Bool.true ↔ ∀ x9 ∈ x5 x8, ∃ x11 ∈ x9, x6.getD (↑x11) Bool.false = Bool.true := by
  sorry
