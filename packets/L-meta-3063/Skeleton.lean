import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3063 : ∀ (n m : ℕ) (inc : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (s k T : ℕ)
  (a b : Fin k → ℕ) (A : Fin k → Finset (Fin n)) (B : Fin k → Finset (Fin m)),
  (∀ p p' : Fin n, ∀ l l' : Fin m, p ≠ p' → l ≠ l' → inc p l = true → inc p' l = true →
    inc p l' = true → inc p' l' = true → False) →
  PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  C.size = s + k + T → 1 ≤ k →
  (∀ j < s, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2) →
  (∀ i : Fin k, (A i).Nonempty ∧ (B i).Nonempty ∧ a i < n + m + s ∧ b i < n + m + s ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (s + i.val)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (s + i.val)).inputs = [a i, b i] ∧
    ∀ x : List Bool, x.length = n + m →
      ((C.wires x).getD (a i) false = decide (∃ pa ∈ A i, x.getD pa.val false = true) ∧
       (C.wires x).getD (b i) false = decide (∃ lb ∈ B i, x.getD (n + lb.val) false = true))) →
  (∀ x : List Bool, x.length = n + m →
    C.eval x = decide (∃ i1 j1 : Fin k, i1 < j1 ∧ (C.wires x).getD (n + m + s + i1.val) false = true ∧
      (C.wires x).getD (n + m + s + j1.val) false = true)) →
  (∀ (P : Finset (Fin n)) (L : Finset (Fin m)),
    ((P.card = 1 ∧ L.card ≤ 2) ∨ (P.card ≤ 2 ∧ L.card = 1)) →
    (∀ p ∈ P, ∀ l ∈ L, inc p l = false) →
    C.eval (List.ofFn (fun u : Fin n => decide (u ∈ P)) ++ List.ofFn (fun v : Fin m => decide (v ∈ L))) = false) →
  ((Finset.univ : Finset (Fin n × Fin m)).filter (fun q => inc q.1 q.2 = true ∧
      C.eval (List.ofFn (fun u : Fin n => decide (u = q.1)) ++ List.ofFn (fun v : Fin m => decide (v = q.2))) = true)).card
    ≤ s + k + ((Finset.univ : Finset (Fin k)).filter (fun t =>
        (∃ c : Fin n, 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc c e = true) ∧
        (∃ f ∈ B t, 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g f = true))).card ∧
  (k ≤ T + 1 →
    ((Finset.univ : Finset (Fin n × Fin m)).filter (fun r => inc r.1 r.2 = true ∧
      C.eval (List.ofFn (fun u : Fin n => decide (u = r.1)) ++ List.ofFn (fun v : Fin m => decide (v = r.2))) = true)).card
    ≤ C.size + 1) := by
  sorry
