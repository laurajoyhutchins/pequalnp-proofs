import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1545 : ¬ (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 10 (fun x : Fin 10 → Bool => ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 0), (0, 7), (1, 8), (2, 9)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)) s → 14 ≤ s) := by
  sorry
