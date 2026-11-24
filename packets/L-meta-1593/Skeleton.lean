import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1593 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), (∀ v : Fin n, v ∉ A → (G.neighborSet v).ncard = 3) → (∀ (w : Fin n) (c : G.Walk w w), c.IsCycle → 7 ≤ c.length) → (∀ i j : Fin n, G.Adj i j → i ∉ A) → (∃ i1 j1 : Fin n, G.Adj i1 j1) → ∃ z : Fin n, z ∉ A ∧ ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => @decide ((∃ a ∈ A, x a = true) ∨ ∃ i2 j2 : Fin n, G.Adj i2 j2 ∧ x i2 = true ∧ x j2 = true) (Classical.propDecidable _)) s → ∃ t : ℕ, t + 4 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x' : Fin n → Bool => @decide ((∃ a' ∈ A, x' a' = true) ∨ ∃ i3 j3 : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj i3 j3 ∧ x' i3 = true ∧ x' j3 = true) (Classical.propDecidable _)) t := by
  sorry
