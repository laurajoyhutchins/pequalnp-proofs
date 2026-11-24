import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1621 : ∀ T : ℕ → Set ((Fin 14 → Bool) → Bool), (∀ i : Fin 14, (fun x : Fin 14 → Bool => x i) ∈ T 0) → (∀ (k : ℕ) (f : (Fin 14 → Bool) → Bool), f ∈ T k → f ∈ T (k + 1)) → (∀ (k : ℕ) (f g : (Fin 14 → Bool) → Bool), f ∈ T k → g ∈ T k → (fun y : Fin 14 → Bool => f y && g y) ∈ T (k + 1) ∧ (fun y : Fin 14 → Bool => f y || g y) ∈ T (k + 1)) → (fun z : Fin 14 → Bool => (z 0 && z 7) || (z 0 && z 8) || (z 0 && z 10) || (z 1 && z 7) || (z 1 && z 9) || (z 1 && z 13) || (z 2 && z 8) || (z 2 && z 12) || (z 2 && z 13) || (z 3 && z 7) || (z 3 && z 11) || (z 3 && z 12) || (z 4 && z 10) || (z 4 && z 11) || (z 4 && z 13) || (z 5 && z 9) || (z 5 && z 10) || (z 5 && z 12) || (z 6 && z 8) || (z 6 && z 9) || (z 6 && z 11)) ∈ T 5 := by
  sorry
