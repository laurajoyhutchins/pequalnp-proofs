import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2636 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool), (∀ x5 ∉ x3, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x3) → (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) → (∀ (x9 : Fin x1 → Bool), x4 x9 = Bool.true ↔ (∃ x10 ∈ x3, x9 x10 = Bool.true) ∨ ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true) → ∀ (x10 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x10 → ∃ x12 ∉ x3, ∃ (x13 : ℕ), x13 + (4 : ℕ) ≤ x10 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x14 : Fin x1 → Bool) => x4 (Function.update x14 x12 Bool.false)) x13 := by
  sorry
