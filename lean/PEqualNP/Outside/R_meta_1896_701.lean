import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1896_701
    (hcover : let I : Fin 13 → Fin 13 → Prop := fun p l => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9;
      ∀ (X Y : Finset (Fin 13)), (∀ p ∈ X, ∀ l ∈ Y, ¬ I p l) →
    (∀ l : Fin 13, (X.filter (fun p => I p l)).card ≤ 2) →
    (∀ p : Fin 13, (Y.filter (fun l => I p l)).card ≤ 2) →
      ∃ Z : Finset (Fin 13),
        X ⊆ Z ∧
        (∀ l ∈ Y, ∀ p ∈ Z, ¬ I p l) ∧
        (∀ p ∉ Z, ∃ l : Fin 13, (∀ q ∈ Z, ¬ I q l) ∧ I p l) ∧
        (¬ ∃ l : Fin 13, ∀ p ∈ Z, I p l) ∧
        (¬ ∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ Z, ¬ I q l) → I p l))
    (hmono : ∀ (C : Circuit), Monotone2 C →
      ∀ (a b : Fin (13 + 13) → Bool),
      (∀ k, a k = true → b k = true) →
      circuitFun (13 + 13) C a = true → circuitFun (13 + 13) C b = true)
    (hcount : let I : Fin 13 → Fin 13 → Prop := fun p l => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9;
      ∀ (C : Circuit), Monotone2 C →
      (∀ p l : Fin 13, I p l →
        circuitFun (13 + 13) C (fun k =>
          decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 l)) = true) →
      (∀ (X Y : Finset (Fin 13)), (∀ p ∈ X, ∀ l ∈ Y, ¬ I p l) →
    (∀ l : Fin 13, (X.filter (fun p => I p l)).card ≤ 2) →
    (∀ p : Fin 13, (Y.filter (fun l => I p l)).card ≤ 2) →
        circuitFun (13 + 13) C (fun k => decide
          ((∃ p ∈ X, k = Fin.castAdd 13 p) ∨
           (∃ l ∈ Y, k = Fin.natAdd 13 l))) = false) →
      51 ≤ {i : Fin C.gates.length | (C.gates.get i).op = GateOp.or}.ncard) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) → (∀ (x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∉ x4, ∃ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) ∧ (x5 = x7 ∨ x5 = x7 + (1 : Fin (13 : ℕ)) ∨ x5 = x7 + (3 : Fin (13 : ℕ)) ∨ x5 = x7 + (9 : Fin (13 : ℕ)))) → ((¬∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x4, x7 = x6 ∨ x7 = x6 + (1 : Fin (13 : ℕ)) ∨ x7 = x6 + (3 : Fin (13 : ℕ)) ∨ x7 = x6 + (9 : Fin (13 : ℕ))) ∧ ¬∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) → x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x8 ∈ x4, x7 = Fin.castAdd (13 : ℕ) x8) ∨ ∃ (x8 : Fin (13 : ℕ)), x7 = Fin.natAdd (13 : ℕ) x8 ∧ ∀ x9 ∈ x4, ¬(x9 = x8 ∨ x9 = x8 + (1 : Fin (13 : ℕ)) ∨ x9 = x8 + (3 : Fin (13 : ℕ)) ∨ x9 = x8 + (9 : Fin (13 : ℕ))))) = Bool.false) → (51 : ℕ) ≤ {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard := by
  intro C hC hpos hneg
  apply hcount C hC hpos
  intro X Y hxy hX hY
  obtain ⟨Z, hXZ, hYZ, hclosed, hline, hpencil⟩ := hcover X Y hxy hX hY
  have hz := hneg Z hclosed ⟨hline, hpencil⟩
  let a : Fin (13 + 13) → Bool := fun k => decide
    ((∃ p ∈ X, k = Fin.castAdd 13 p) ∨ (∃ l ∈ Y, k = Fin.natAdd 13 l))
  let b : Fin (13 + 13) → Bool := fun k => decide
    ((∃ p ∈ Z, k = Fin.castAdd 13 p) ∨
     (∃ l : Fin 13, k = Fin.natAdd 13 l ∧
       ∀ q ∈ Z, ¬ (q = l ∨ q = l + 1 ∨ q = l + 3 ∨ q = l + 9)))
  change circuitFun (13 + 13) C a = false
  have hz' : circuitFun (13 + 13) C b = false := hz
  have hab : ∀ k, a k = true → b k = true := by
    intro k hk
    simp only [a, b, decide_eq_true_eq] at hk ⊢
    rcases hk with ⟨p, hp, he⟩ | ⟨l, hl, he⟩
    · exact Or.inl ⟨p, hXZ hp, he⟩
    · exact Or.inr ⟨l, he, hYZ l hl⟩
  cases ha : circuitFun (13 + 13) C a with
  | false => rfl
  | true =>
    have hb := hmono C hC a b hab ha
    rw [hz'] at hb
    contradiction
