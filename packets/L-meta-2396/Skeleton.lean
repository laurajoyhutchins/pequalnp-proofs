import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2396 : ¬ (let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∈ x2, ∀ x6 ∈ x3, ¬x1 x4 x6) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x2 | x1 x6 x5}.card ≤ (2 : ℕ)) → (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x3 | x1 x6 x7}.card ≤ (2 : ℕ)) → ∃ (x7 : Finset (Fin (13 : ℕ))), x2 ⊆ x7 ∧ (∀ x8 ∈ x3, ∀ x10 ∈ x7, ¬x1 x10 x8) ∧ (∀ x8 ∉ x7, ∃ (x10 : Fin (13 : ℕ)), (∀ x11 ∈ x7, ¬x1 x11 x10) ∧ x1 x8 x10) ∧ (¬∃ (x8 : Fin (13 : ℕ)), ∀ x9 ∈ x7, x1 x9 x8) ∧ ¬∃ (x8 : Fin (13 : ℕ)), ∀ (x9 : Fin (13 : ℕ)), (∀ x10 ∈ x7, ¬x1 x10 x9) → x1 x8 x9) := by
  sorry
