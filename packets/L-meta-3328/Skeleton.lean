import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3328 : have x1 : List ℕ → ℕ → Prop := fun (x1 : List ℕ) (x2 : ℕ) => ∃ x3 ∈ x1, ∃ x4 ∈ x1, x2 = x3 &&& x4 ∨ x2 = x3 ||| x4; have x2 : List ℕ → List ℕ → Prop := fun (x2 x3 : List ℕ) => ∀ (x4 : Fin x3.length), x1 (x2 ++ List.take (↑x4) x3) (x3.get x4); ∀ (x3 : List ℕ) (x4 x5 : ℕ) (x6 : List ℕ), x5 ∉ x3 → x1 x3 x4 → x2 (x4 :: x3) x6 → x1 (x4 :: x3 ++ x6) x5 → ∃ (x11 : List ℕ), x11.length ≤ x6.length + (2 : ℕ) ∧ x11.Nodup ∧ (∀ x12 ∈ x11, x12 ∉ x3) ∧ x5 ∈ x11 ∧ x2 x3 x11 := by
  sorry
