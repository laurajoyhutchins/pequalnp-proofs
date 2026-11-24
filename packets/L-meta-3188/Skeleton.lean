import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3188 : have x1 : Fin (9 : ℕ) → BitVec (24 : ℕ) := fun (x1 : Fin (9 : ℕ)) =>   have x2 : ℕ × ℕ := [((49 : ℕ), (1348 : ℕ)), ((67 : ℕ), (2083 : ℕ)), ((134 : ℕ), (788 : ℕ)), ((268 : ℕ), (105 : ℕ)), ((24 : ℕ), (2706 : ℕ)), ((2592 : ℕ), (27 : ℕ)), ((1088 : ℕ), (220 : ℕ)), ((640 : ℕ), (3296 : ℕ)), ((3328 : ℕ), (3840 : ℕ))].getD ↑x1 ((0 : ℕ), (0 : ℕ));   BitVec.ofNat (24 : ℕ) ((4096 : ℕ) * x2.1 + x2.2); have x2 : List (BitVec (24 : ℕ)) := List.ofFn x1 ++ [x1 (0 : Fin (9 : ℕ)) ||| x1 (2 : Fin (9 : ℕ))]; ∀ (x3 : List (BitVec (24 : ℕ))),   BitVec.ofNat (24 : ℕ) ((4095 : ℕ) * (4096 : ℕ)) ∈ x2 ++ x3 →     (∀ (x5 : Fin x3.length),         have x6 : List (BitVec (24 : ℕ)) := x2 ++ List.take (↑x5) x3;         x3.get x5 ∉ x6 ∧ x3.get x5 ≠ (0 : BitVec (24 : ℕ)) ∧ x3.get x5 ≠ (-1 : BitVec (24 : ℕ)) ∧ ∃ x7 ∈ x6, ∃ x8 ∈ x6, x3.get x5 = x7 &&& x8 ∨ x3.get x5 = x7 ||| x8) →       (15 : ℕ) ≤ x3.length := by
  sorry
