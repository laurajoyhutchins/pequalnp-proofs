import Mathlib
import PEqualNP.Defs
import PEqualNP.Research.OneNotParentPacking
import PEqualNP.Research.OneNotEvaluatorBridge

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Research.OneNotTruncatedBound : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)),
  (∀ i : Fin m, 2 ≤ (S i).card) →
  (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
  ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ),
  (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
    g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
    g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
  (∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length,
    (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin 1, ι j = i) →
  (∀ (w : Fin m) (x : Fin n → Bool),
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
      decide (∃ v ∈ S w, x v = true)) →
  (∑ i : Fin m, min 2 ((S i).card - 1)) ≤ gates.length := by
  classical
  intro n m S hs hl gates out hg hn he
  obtain ⟨o, a, b, k, hi, ho, hp, hf, hm, ha, hb⟩ :=
    PEqualNP.Research.OneNotEvaluatorBridge n m S gates out hs hg hn he
  let W : ℕ → Finset (Fin n) → Prop := fun w x =>
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩
      (List.ofFn (fun v : Fin n => decide (v ∈ x))) = true
  have hcount := PEqualNP.Research.OneNotParentPacking n m gates.length S W o a b k
    hs hl hi ho hp hf hm ha hb
  have hrow (i : Fin m) : min 2 ((S i).card - 1) =
      1 + (if 3 ≤ (S i).card then 1 else 0) := by
    have hi' := hs i
    by_cases h : 3 ≤ (S i).card
    · simp [h, Nat.min_eq_left (show 2 ≤ (S i).card - 1 by omega)]
    · have htwo : (S i).card = 2 := by omega
      simp [htwo]
  calc
    (∑ i : Fin m, min 2 ((S i).card - 1)) =
        ∑ i : Fin m, (1 + (if 3 ≤ (S i).card then 1 else 0)) :=
      Finset.sum_congr rfl (fun i _ => hrow i)
    _ = m + (Finset.univ.filter (fun i : Fin m => 3 ≤ (S i).card)).card := by
      rw [Finset.sum_add_distrib]
      simp [Finset.sum_ite]
    _ ≤ gates.length := hcount
