import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1493 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ x : Fin 26 → Bool, (∀ wa : Fin 13, (Finset.univ.filter (fun pa : Fin 13 => (∃ da : ℕ, da ∈ ({0, 1, 3, 9} : Finset ℕ) ∧ (wa.val + da) % 13 = pa.val) ∧ x (Fin.castAdd 13 pa) = true)).card ≤ 2) → PEqualNP.MetaComplexity.circuitFun 26 C x = true → ∃ pb wb : Fin 13, (∃ db : ℕ, db ∈ ({0, 1, 3, 9} : Finset ℕ) ∧ (wb.val + db) % 13 = pb.val) ∧ x (Fin.castAdd 13 pb) = true ∧ x (Fin.natAdd 13 wb) = true) ∧ (∀ pc wc : Fin 13, (∃ dc : ℕ, dc ∈ ({0, 1, 3, 9} : Finset ℕ) ∧ (wc.val + dc) % 13 = pc.val) → PEqualNP.MetaComplexity.circuitFun 26 C (fun k : Fin 26 => decide (k = Fin.castAdd 13 pc ∨ k = Fin.natAdd 13 wc)) = true) := by
  sorry
