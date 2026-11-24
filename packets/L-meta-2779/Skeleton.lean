import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2779 : ¬ (have x1 : List (BitVec (24 : ℕ)) := [(0 : BitVec (24 : ℕ)), (16777215 : BitVec (24 : ℕ)), (4358697 : BitVec (24 : ℕ)), (8397251 : BitVec (24 : ℕ)), (662022 : BitVec (24 : ℕ)), (304212 : BitVec (24 : ℕ)), (8980632 : BitVec (24 : ℕ)), (1068256 : BitVec (24 : ℕ)), (2199296 : BitVec (24 : ℕ)), (12709888 : BitVec (24 : ℕ)), (16646144 : BitVec (24 : ℕ)), (13339321 : BitVec (24 : ℕ))]; ∀ (x2 : List (BitVec (24 : ℕ))), x2.length ≤ (14 : ℕ) → (∀ (x4 : ℕ) (x5 : x4 < x2.length), x2[x4] ∉ x1 ++ List.take x4 x2 ∧ ∃ x6 ∈ x1 ++ List.take x4 x2, ∃ x7 ∈ x1 ++ List.take x4 x2, x2[x4] = x6 &&& x7 ∨ x2[x4] = x6 ||| x7) → (3428671 : BitVec (24 : ℕ)) ∉ x1 ++ x2) := by
  sorry
