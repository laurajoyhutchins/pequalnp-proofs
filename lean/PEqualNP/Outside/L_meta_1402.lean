import Mathlib

namespace PEqualNP.Outside.L_meta_1402_aux

abbrev Fn := (Fin 10 → Bool) → Bool

def input (m : ℕ) : Fin 10 → Bool := fun i => m.testBit i.val

def pMask : Fin 20 → ℕ :=
  ![3, 65, 34, 96, 6, 130, 68, 192, 12, 260, 136, 384, 24, 520, 272, 768, 17, 48, 513, 544]

def nMask : Fin 5 → ℕ := ![165, 297, 330, 594, 660]

def positive (f : Fn) : Finset (Fin 20) :=
  Finset.univ.filter (fun i => f (input (pMask i)) = true)

def negative (f : Fn) : Finset (Fin 5) :=
  Finset.univ.filter (fun i => f (input (nMask i)) = false)

def pc (f : Fn) : ℕ := (positive f).card

def nc (f : Fn) : ℕ := (negative f).card

def gate (b : Bool) (f g : Fn) : Fn :=
  fun x => if b then f x && g x else f x || g x

def var (i : Fin 10) : Fn := fun x => x i

def depthTwo (f : Fn) : Prop :=
  pc f ≤ 16 ∧ (3 ≤ nc f → pc f ≤ 9) ∧ (5 ≤ nc f → pc f ≤ 4)

def depthThree (f : Fn) : Prop :=
  (3 ≤ nc f → pc f ≤ 18) ∧ (5 ≤ nc f → pc f ≤ 9)

def depthFour (f : Fn) : Prop := 5 ≤ nc f → pc f ≤ 18

def rot (s : Fin 10) (f : Fn) : Fn :=
  fun x => f (fun i => x (i + s))

def pShift : Fin 10 → Fin 20 → Fin 20 :=
    ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19],
    ![18, 19, 16, 17, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 12, 15, 14],
    ![15, 14, 13, 12, 18, 19, 16, 17, 0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10],
    ![11, 10, 9, 8, 15, 14, 13, 12, 18, 19, 16, 17, 0, 1, 2, 3, 5, 4, 7, 6],
    ![7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, 18, 19, 16, 17, 1, 0, 3, 2],
    ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16],
    ![17, 16, 19, 18, 3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 14, 15, 12, 13],
    ![12, 13, 14, 15, 17, 16, 19, 18, 3, 2, 1, 0, 7, 6, 5, 4, 10, 11, 8, 9],
    ![8, 9, 10, 11, 12, 13, 14, 15, 17, 16, 19, 18, 3, 2, 1, 0, 6, 7, 4, 5],
    ![4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 16, 19, 18, 2, 3, 0, 1]]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem pShift_bit : ∀ (s : Fin 10) (t : Fin 20) (i : Fin 10),
    input (pMask t) (i + s) = input (pMask (pShift s t)) i := by
  intro s
  fin_cases s <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem pShift_left : ∀ (s : Fin 10) (t : Fin 20),
    pShift (0 - s) (pShift s t) = t := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem pShift_right : ∀ (s : Fin 10) (t : Fin 20),
    pShift s (pShift (0 - s) t) = t := by
  decide

theorem pc_rot (s : Fin 10) (f : Fn) : pc (rot s f) = pc f := by
  unfold pc
  apply Finset.card_bijective (pShift s)
  · constructor
    · intro a b h
      have h' := congrArg (pShift (0 - s)) h
      simpa only [pShift_left] using h'
    · intro b
      exact ⟨pShift (0 - s) b, pShift_right s b⟩
  · intro t
    have h : (fun i => input (pMask t) (i + s)) = input (pMask (pShift s t)) := by
      funext i
      exact pShift_bit s t i
    simp only [positive, Finset.mem_filter, Finset.mem_univ, true_and, rot, h]

def nShift : Fin 10 → Fin 5 → Fin 5 :=
    ![![0, 1, 2, 3, 4],
    ![3, 4, 0, 1, 2],
    ![1, 2, 3, 4, 0],
    ![4, 0, 1, 2, 3],
    ![2, 3, 4, 0, 1],
    ![0, 1, 2, 3, 4],
    ![3, 4, 0, 1, 2],
    ![1, 2, 3, 4, 0],
    ![4, 0, 1, 2, 3],
    ![2, 3, 4, 0, 1]]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem nShift_bit : ∀ (s : Fin 10) (t : Fin 5) (i : Fin 10),
    input (nMask t) (i + s) = input (nMask (nShift s t)) i := by
  intro s
  fin_cases s <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem nShift_left : ∀ (s : Fin 10) (t : Fin 5),
    nShift (0 - s) (nShift s t) = t := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem nShift_right : ∀ (s : Fin 10) (t : Fin 5),
    nShift s (nShift (0 - s) t) = t := by
  decide

theorem nc_rot (s : Fin 10) (f : Fn) : nc (rot s f) = nc f := by
  unfold nc
  apply Finset.card_bijective (nShift s)
  · constructor
    · intro a b h
      have h' := congrArg (nShift (0 - s)) h
      simpa only [nShift_left] using h'
    · intro b
      exact ⟨nShift (0 - s) b, nShift_right s b⟩
  · intro t
    have h : (fun i => input (nMask t) (i + s)) = input (nMask (nShift s t)) := by
      funext i
      exact nShift_bit s t i
    simp only [negative, Finset.mem_filter, Finset.mem_univ, true_and, rot, h]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem shift_cancel : ∀ (s j : Fin 10), (j - s) + s = j := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem certificateZero :
    ∀ (a b c : Bool) (j k l : Fin 10),
      depthTwo (gate c (gate a (var 0) (var j)) (gate b (var k) (var l))) := by
  intro a b c
  cases a <;> cases b <;> cases c <;> simp only [depthTwo] <;> decide

theorem certificate :
    ∀ (a b c : Bool) (i j k l : Fin 10),
      depthTwo (gate c (gate a (var i) (var j)) (gate b (var k) (var l))) := by
  intro a b c i j k l
  have h : depthTwo (rot i
      (gate c (gate a (var 0) (var (j - i))) (gate b (var (k - i)) (var (l - i))))) := by
    simpa only [depthTwo, pc_rot, nc_rot] using certificateZero a b c (j - i) (k - i) (l - i)
  change depthTwo
    (gate c (gate a (var (0 + i)) (var ((j - i) + i)))
      (gate b (var ((k - i) + i)) (var ((l - i) + i)))) at h
  simpa only [zero_add, shift_cancel] using h

theorem and_stats (f g : Fn) :
    pc (fun y => f y && g y) ≤ pc f ∧
    pc (fun y => f y && g y) ≤ pc g ∧
    nc (fun y => f y && g y) ≤ nc f + nc g := by
  have h₁ : positive (fun y => f y && g y) ⊆ positive f := by
    intro i hi
    simp [positive] at hi ⊢
    exact hi.1
  have h₂ : positive (fun y => f y && g y) ⊆ positive g := by
    intro i hi
    simp [positive] at hi ⊢
    exact hi.2
  have h₃ : negative (fun y => f y && g y) ⊆ negative f ∪ negative g := by
    intro i hi
    simpa [negative] using hi
  exact ⟨Finset.card_le_card h₁, Finset.card_le_card h₂,
    le_trans (Finset.card_le_card h₃) (Finset.card_union_le _ _)⟩

theorem or_stats (f g : Fn) :
    pc (fun y => f y || g y) ≤ pc f + pc g ∧
    nc (fun y => f y || g y) ≤ nc f ∧
    nc (fun y => f y || g y) ≤ nc g := by
  have h₁ : positive (fun y => f y || g y) ⊆ positive f ∪ positive g := by
    intro i hi
    simpa [positive] using hi
  have h₂ : negative (fun y => f y || g y) ⊆ negative f := by
    intro i hi
    simp [negative] at hi ⊢
    exact hi.1
  have h₃ : negative (fun y => f y || g y) ⊆ negative g := by
    intro i hi
    simp [negative] at hi ⊢
    exact hi.2
  exact ⟨le_trans (Finset.card_le_card h₁) (Finset.card_union_le _ _),
    Finset.card_le_card h₂, Finset.card_le_card h₃⟩

theorem two_three (f g : Fn) (hf : depthTwo f) (hg : depthTwo g) :
    depthThree (fun y => f y && g y) ∧ depthThree (fun y => f y || g y) := by
  obtain ⟨hf16, hf9, hf4⟩ := hf
  obtain ⟨hg16, hg9, hg4⟩ := hg
  obtain ⟨ha₁, ha₂, ha₃⟩ := and_stats f g
  obtain ⟨ho₁, ho₂, ho₃⟩ := or_stats f g
  constructor
  · constructor
    · intro h
      omega
    · intro h
      by_cases hf' : 3 ≤ nc f
      · have := hf9 hf'
        omega
      · have hg' : 3 ≤ nc g := by omega
        have := hg9 hg'
        omega
  · constructor
    · intro h
      have h₁ := hf9 (by omega)
      have h₂ := hg9 (by omega)
      omega
    · intro h
      have h₁ := hf4 (by omega)
      have h₂ := hg4 (by omega)
      omega

theorem three_four (f g : Fn) (hf : depthThree f) (hg : depthThree g) :
    depthFour (fun y => f y && g y) ∧ depthFour (fun y => f y || g y) := by
  obtain ⟨hf18, hf9⟩ := hf
  obtain ⟨hg18, hg9⟩ := hg
  obtain ⟨ha₁, ha₂, ha₃⟩ := and_stats f g
  obtain ⟨ho₁, ho₂, ho₃⟩ := or_stats f g
  constructor
  · intro h
    by_cases hf' : 3 ≤ nc f
    · have := hf18 hf'
      omega
    · have hg' : 3 ≤ nc g := by omega
      have := hg18 hg'
      omega
  · intro h
    have h₁ := hf9 (by omega)
    have h₂ := hg9 (by omega)
    omega

def levels : ℕ → Set Fn
  | 0 => { f | ∃ i : Fin 10, f = var i }
  | 1 => { f | ∃ (b : Bool) (i j : Fin 10), f = gate b (var i) (var j) }
  | 2 => { f | ∃ (a b c : Bool) (i j k l : Fin 10),
      f = gate c (gate a (var i) (var j)) (gate b (var k) (var l)) }
  | 3 => { f | depthThree f }
  | 4 => { f | depthFour f }
  | _ => Set.univ

theorem step (k : ℕ) (f g : Fn) (hf : f ∈ levels k) (hg : g ∈ levels k) :
    (fun y => f y && g y) ∈ levels (k + 1) ∧
    (fun y => f y || g y) ∈ levels (k + 1) := by
  by_cases h : k ≤ 3
  · interval_cases k
    · change (∃ i : Fin 10, f = var i) at hf
      change (∃ i : Fin 10, g = var i) at hg
      obtain ⟨i, rfl⟩ := hf
      obtain ⟨j, rfl⟩ := hg
      exact ⟨⟨true, i, j, rfl⟩, ⟨false, i, j, rfl⟩⟩
    · change (∃ (b : Bool) (i j : Fin 10), f = gate b (var i) (var j)) at hf
      change (∃ (b : Bool) (i j : Fin 10), g = gate b (var i) (var j)) at hg
      obtain ⟨a, i, j, rfl⟩ := hf
      obtain ⟨b, k, l, rfl⟩ := hg
      exact ⟨⟨a, b, true, i, j, k, l, rfl⟩, ⟨a, b, false, i, j, k, l, rfl⟩⟩
    · change (∃ (a b c : Bool) (i j k l : Fin 10),
        f = gate c (gate a (var i) (var j)) (gate b (var k) (var l))) at hf
      change (∃ (a b c : Bool) (i j k l : Fin 10),
        g = gate c (gate a (var i) (var j)) (gate b (var k) (var l))) at hg
      obtain ⟨a, b, c, i, j, k, l, rfl⟩ := hf
      obtain ⟨a', b', c', i', j', k', l', rfl⟩ := hg
      exact two_three _ _ (certificate a b c i j k l) (certificate a' b' c' i' j' k' l')
    · exact three_four f g hf hg
  · obtain ⟨t, rfl⟩ : ∃ t : ℕ, k = t + 4 := ⟨k - 4, by omega⟩
    change (fun y => f y && g y) ∈ levels (t + 5) ∧
      (fun y => f y || g y) ∈ levels (t + 5)
    simp [levels]

theorem keep (k : ℕ) (f : Fn) (hf : f ∈ levels k) : f ∈ levels (k + 1) := by
  have h := (step k f f hf hf).1
  have he : (fun y => f y && f y) = f := by
    funext y
    cases f y <;> rfl
  rwa [he] at h

def target : Fn := fun z =>
  ((z 0 || z 5) && (z 1 || z 6)) || ((z 1 || z 6) && (z 2 || z 7)) ||
  ((z 2 || z 7) && (z 3 || z 8)) || ((z 3 || z 8) && (z 4 || z 9)) ||
  ((z 4 || z 9) && (z 0 || z 5))

theorem target_counts : pc target = 20 ∧ nc target = 5 := by decide

end PEqualNP.Outside.L_meta_1402_aux

open PEqualNP.Outside.L_meta_1402_aux

theorem PEqualNP.Outside.L_meta_1402 : ¬ (∀ T : ℕ → Set ((Fin 10 → Bool) → Bool), (∀ i : Fin 10, (fun x : Fin 10 → Bool => x i) ∈ T 0) → (∀ (k : ℕ) (f : (Fin 10 → Bool) → Bool), f ∈ T k → f ∈ T (k + 1)) → (∀ (k : ℕ) (f g : (Fin 10 → Bool) → Bool), f ∈ T k → g ∈ T k → (fun y : Fin 10 → Bool => f y && g y) ∈ T (k + 1) ∧ (fun y : Fin 10 → Bool => f y || g y) ∈ T (k + 1)) → (fun z : Fin 10 → Bool => ((z 0 || z 5) && (z 1 || z 6)) || ((z 1 || z 6) && (z 2 || z 7)) || ((z 2 || z 7) && (z 3 || z 8)) || ((z 3 || z 8) && (z 4 || z 9)) || ((z 4 || z 9) && (z 0 || z 5))) ∈ T 4) := by
  intro h
  have hv : ∀ i : Fin 10, (fun x : Fin 10 → Bool => x i) ∈ levels 0 := by
    intro i
    exact ⟨i, rfl⟩
  have hmem : target ∈ levels 4 := h levels hv keep step
  have hb : 5 ≤ nc target → pc target ≤ 18 := hmem
  obtain ⟨hp, hn⟩ := target_counts
  have := hb (by omega)
  omega
