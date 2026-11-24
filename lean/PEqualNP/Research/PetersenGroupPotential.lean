import PEqualNP.Research.PetersenBranchBudget
namespace PEqualNP.Research.BranchBudget

def MaskSub (a b : Nat) : Prop := ∀ i, a.testBit i = true → b.testBit i = true

def addBits (p : Nat → Prop) [DecidablePred p] (l : List Nat) (a : Nat) : Nat :=
  l.foldl (fun m i => if p i then m ||| (1 <<< i) else m) a

theorem bit_one_shift (i j : Nat) : (1 <<< i).testBit j = decide (i = j) := by
  simp [Nat.shiftLeft_eq, Nat.testBit_two_pow]

theorem addBits_bit (p : Nat → Prop) [DecidablePred p] (l : List Nat) (a i : Nat) :
    (addBits p l a).testBit i = true ↔ a.testBit i = true ∨ (i ∈ l ∧ p i) := by
  induction l generalizing a with
  | nil => simp [addBits]
  | cons j l ih =>
    change (addBits p l (if p j then a ||| (1 <<< j) else a)).testBit i = true ↔ _
    rw [ih]
    by_cases h : p j
    · simp only [h, ite_true, Nat.testBit_or, bit_one_shift, Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
      constructor
      · intro h'
        rcases h' with (ha|he)|⟨hm,hp⟩
        · exact Or.inl ha
        · subst j; exact Or.inr ⟨Or.inl rfl,h⟩
        · exact Or.inr ⟨Or.inr hm,hp⟩
      · intro h'
        rcases h' with ha|⟨he|hm,hp⟩
        · exact Or.inl (Or.inl ha)
        · exact Or.inl (Or.inr he.symm)
        · exact Or.inr ⟨hm,hp⟩
    · simp only [h, ite_false, List.mem_cons]
      constructor
      · intro h'
        rcases h' with ha|⟨hm,hp⟩
        · exact Or.inl ha
        · exact Or.inr ⟨Or.inr hm,hp⟩
      · intro h'
        rcases h' with ha|⟨he|hm,hp⟩
        · exact Or.inl ha
        · subst j; exact (h hp).elim
        · exact Or.inr ⟨hm,hp⟩

theorem addBits_bound (p : Nat → Prop) [DecidablePred p] (l : List Nat) (a : Nat) (ha : a < 512)
    (hl : ∀ i ∈ l, i < 9) : addBits p l a < 512 := by
  induction l generalizing a with
  | nil => exact ha
  | cons i l ih =>
    change addBits p l (if p i then a ||| (1 <<< i) else a) < 512
    apply ih
    · split
      · apply Nat.or_lt_two_pow (n:=9) ha
        rw [Nat.shiftLeft_eq, Nat.one_mul]
        exact Nat.pow_lt_pow_right (by decide) (hl i (by simp))
      · exact ha
    · intro j hj; exact hl j (List.mem_cons_of_mem _ hj)

theorem addBits_cost (p : Nat → Prop) [DecidablePred p] (l : List Nat) (a : Nat) (ha : a < 512)
    (hl : ∀ i ∈ l, i < 9) : potential (addBits p l a) ≤ potential a := by
  induction l generalizing a with
  | nil => exact Nat.le_refl _
  | cons i l ih =>
    change potential (addBits p l (if p i then a ||| (1 <<< i) else a)) ≤ potential a
    by_cases h : p i
    · rw [if_pos h]
      have hi := hl i (by simp)
      have hb : a ||| (1 <<< i) < 512 := by
        apply Nat.or_lt_two_pow (n:=9) ha
        rw [Nat.shiftLeft_eq, Nat.one_mul]
        exact Nat.pow_lt_pow_right (by decide) hi
      exact Nat.le_trans (ih _ hb (fun j hj => hl j (List.mem_cons_of_mem _ hj)))
        (monotone_step ⟨a,ha⟩ ⟨i,hi⟩)
    · rw [if_neg h]
      exact ih _ ha (fun j hj => hl j (List.mem_cons_of_mem _ hj))

theorem add_all_bits (a s : Nat) (hs : s < 512) : addBits (fun i => s.testBit i = true) (List.range 9) a = a ||| s := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [addBits_bit, Nat.testBit_or, Bool.or_eq_true, List.mem_range]
  by_cases hi : i < 9
  · simp [hi]
  · have e : s.testBit i = false := Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le hs (Nat.pow_le_pow_right (n:=2) (by decide) (by omega : 9 ≤ i)))
    simp [hi,e]

theorem potential_union (a s : Nat) (ha : a < 512) (hs : s < 512) :
    potential (a ||| s) ≤ potential a := by
  rw [← add_all_bits a s hs]
  exact addBits_cost (fun i => s.testBit i = true) _ _ ha (fun i hi => List.mem_range.mp hi)

theorem or_eq_of_subset {a b : Nat} (h : MaskSub a b) : a ||| b = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  cases ha : a.testBit i <;> simp [ha, h i]

theorem potential_subset {a b : Nat} (ha : a < 512) (hb : b < 512) (h : MaskSub a b) :
    potential b ≤ potential a := by
  rw [← or_eq_of_subset h]
  exact potential_union _ _ ha hb

theorem close_bit (m i : Nat) : (close m).testBit i = true ↔
    m.testBit i = true ∨ (i < 9 ∧ res m i = 0) := by
  unfold close
  rw [Nat.testBit_or, Bool.or_eq_true]
  change _ ∨ (addBits (fun j => res m j = 0) (List.range 9) 0).testBit i = true ↔ _
  rw [addBits_bit]
  simp

theorem twins_bit (m r i : Nat) : (twins m r).testBit i = true ↔
    i < 9 ∧ m.testBit i = false ∧ res m i = res m r := by
  change (addBits (fun j => !m.testBit j && res m j == res m r) (List.range 9) 0).testBit i = true ↔ _
  rw [addBits_bit]
  simp [Bool.and_eq_true]

theorem close_bound (m : Nat) (hm : m < 512) : close m < 512 := by
  unfold close
  apply Nat.or_lt_two_pow (n:=9) hm
  exact addBits_bound (fun j => res m j = 0) _ 0 (by decide) (fun i hi => List.mem_range.mp hi)

theorem residual_zero_union (m s i : Nat) (h : res m i = 0) : res (m ||| s) i = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  have he := congrArg (fun n : Nat => n.testBit j) h
  simp only [res, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_or, Nat.zero_testBit] at he ⊢
  by_cases jlt : j < 9
  · have hf : (511 : Nat).testBit j = true := by
      have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega
      rcases this with h|h|h|h|h|h|h|h|h <;> rw [h] <;> decide
    rw [hf] at he ⊢
    cases ha : (adj[i]?.getD 0).testBit j <;> cases hm : m.testBit j <;> cases hs : s.testBit j <;> simp_all
  · have ha : adj[i]?.getD 0 < 512 := by
      by_cases hi : i < 9
      · have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
        rcases this with h|h|h|h|h|h|h|h|h <;> rw [h] <;> decide
      · have hh : adj[i]? = none := by apply Array.getElem?_eq_none; simp [adj]; omega
        simp [hh]
    have z : (adj[i]?.getD 0).testBit j = false := Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (n:=2) (by decide) (by omega : 9 ≤ j)))
    simp [z]

-- Arbitrary, not necessarily maximal, twin groups. The accepted graph theorem
-- supplies exactly this residual-neighborhood condition.
def GoodGroup (m s : Nat) : Prop := ∀ i j : Fin 9,
  s.testBit i.val = true → s.testBit j.val = true →
  res m i.val ≠ 0 → res m j.val ≠ 0 → res m i.val = res m j.val

theorem group_step (m s : Nat) (hm : m < 512) (hs : s < 512)
    (good : GoodGroup m s) : potential m ≤ 1 + potential (m ||| s) := by
  have hms : m ||| s < 512 := Nat.or_lt_two_pow (n:=9) hm hs
  by_cases act : ∃ i : Fin 9, s.testBit i.val = true ∧ m.testBit i.val = false ∧ res m i.val ≠ 0
  · obtain ⟨r,hrs,hrm,hrr⟩ := act
    have hadv : advance m r.val = close (m ||| twins m r.val) := by simp [advance,hrm,hrr]
    have sub : MaskSub (m ||| s) (advance m r.val) := by
      intro j hj
      rw [hadv,close_bit]
      have e : m.testBit j = true ∨ s.testBit j = true := by simpa only [Nat.testBit_or,Bool.or_eq_true] using hj
      rcases e with hjm|hjs
      · exact Or.inl (by simp [Nat.testBit_or,hjm])
      · have jlt : j < 9 := by
          by_cases h : j < 9
          · exact h
          · have z := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hs (Nat.pow_le_pow_right (n:=2) (by decide) (by omega : 9 ≤ j)))
            simp [z] at hjs
        by_cases hjm : m.testBit j = true
        · exact Or.inl (by simp [Nat.testBit_or,hjm])
        · by_cases hjr : res m j = 0
          · exact Or.inr ⟨jlt,residual_zero_union m _ j hjr⟩
          · have hmj : m.testBit j = false := by cases h : m.testBit j <;> simp_all
            have same := good ⟨j,jlt⟩ r hjs hrs hjr hrr
            exact Or.inl (by rw [Nat.testBit_or, Bool.or_eq_true]; exact Or.inr ((twins_bit _ _ _).mpr ⟨jlt,hmj,same⟩))
    obtain ⟨hadvBound,hadvCost⟩ := step_valid ⟨m,hm⟩ r
    change advance m r.val < 512 at hadvBound
    change potential m ≤ 1 + potential (advance m r.val) at hadvCost
    have hc := potential_subset hms hadvBound sub
    omega
  · have sub : MaskSub (m ||| s) (close m) := by
      intro j hj
      rw [close_bit]
      have e : m.testBit j = true ∨ s.testBit j = true := by simpa only [Nat.testBit_or,Bool.or_eq_true] using hj
      rcases e with hjm|hjs
      · exact Or.inl hjm
      · have jlt : j < 9 := by
          by_cases h : j < 9
          · exact h
          · have z := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hs (Nat.pow_le_pow_right (n:=2) (by decide) (by omega : 9 ≤ j)))
            simp [z] at hjs
        by_cases hjm : m.testBit j = true
        · exact Or.inl hjm
        · have hmj : m.testBit j = false := by cases h : m.testBit j <;> simp_all
          have zero : res m j = 0 := by
            by_cases hz : res m j = 0
            · exact hz
            · exact (act ⟨⟨j,jlt⟩,hjs,hmj,hz⟩).elim
          exact Or.inr ⟨jlt,zero⟩
    have e := potential_subset hms (close_bound m hm) sub
    have hclose := close_valid ⟨m,hm⟩
    change potential m = potential (close m) at hclose
    omega

def GroupSequence : Nat → List Nat → Prop
  | _, [] => True
  | m,s::ss => s < 512 ∧ GoodGroup m s ∧ GroupSequence (m ||| s) ss

def removeGroups (m : Nat) (ss : List Nat) : Nat := ss.foldl (· ||| ·) m

theorem group_sequence_cost (m : Nat) (hm : m < 512) (ss : List Nat)
    (valid : GroupSequence m ss) : potential m ≤ ss.length + potential (removeGroups m ss) := by
  induction ss generalizing m with
  | nil => simp [removeGroups]
  | cons s ss ih =>
    have h1 := group_step m s hm valid.1 valid.2.1
    have h2 := ih (m ||| s) (Nat.or_lt_two_pow (n:=9) hm valid.1) valid.2.2
    change potential m ≤ ss.length + 1 + potential (removeGroups (m ||| s) ss)
    omega

theorem group_sequence_bound (m : Nat) (hm : m < 512) (ss : List Nat)
    (valid : GroupSequence m ss) : removeGroups m ss < 512 := by
  induction ss generalizing m with
  | nil => exact hm
  | cons s ss ih => exact ih _ (Nat.or_lt_two_pow (n:=9) hm valid.1) valid.2.2

def EdgelessMask (m : Nat) : Prop := ∀ i : Fin 9, m.testBit i.val = false → res m i.val = 0

theorem edgeless_close (m : Nat) (hm : m < 512) (h : EdgelessMask m) : close m = 511 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 9
  · have ht : (close m).testBit i = true := (close_bit m i).mpr (by
      cases e : m.testBit i
      · exact Or.inr ⟨hi,h ⟨i,hi⟩ e⟩
      · exact Or.inl rfl)
    rw [ht]
    have e : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
    rcases e with h|h|h|h|h|h|h|h|h <;> rw [h] <;> decide
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (close_bound m hm) (Nat.pow_le_pow_right (n:=2) (by decide) (by omega : 9 ≤ i))),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 511 < 2^9) (Nat.pow_le_pow_right (n:=2) (by decide) (by omega : 9 ≤ i)))]

theorem graph_sequence_lower (m : Nat) (hm : m < 512) (ss : List Nat)
    (valid : GroupSequence m ss) (finish : EdgelessMask (removeGroups m ss)) : potential m ≤ ss.length := by
  have hb := group_sequence_bound m hm ss valid
  have hf := edgeless_close _ hb finish
  have hz := close_valid ⟨removeGroups m ss,hb⟩
  change potential (removeGroups m ss) = potential (close (removeGroups m ss)) at hz
  rw [hf,terminal] at hz
  have hc := group_sequence_cost m hm ss valid
  omega

theorem anchored_group_mask (m : Nat) (hm : m < 512) (ss : List Nat)
    (valid : GroupSequence m ss) (finish : EdgelessMask (removeGroups m ss))
    (h0 : m.testBit 0 = true) (h2 : m.testBit 2 = true) (budget : pop m + ss.length ≤ 5) : allowed m = true := by
  apply allowed_masks ⟨m,hm⟩ h0 h2
  change pop m + potential m ≤ 5
  have h := graph_sequence_lower m hm ss valid finish
  omega

#print axioms group_step
#print axioms graph_sequence_lower
#print axioms anchored_group_mask
end PEqualNP.Research.BranchBudget
namespace PEqualNP.Research.BranchBudget
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem no_mask04 : ∀ m : Fin 512, m.val.testBit 0 = true → m.val.testBit 4 = true → 6 ≤ pop m.val + potential m.val := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem no_mask46 : ∀ m : Fin 512, m.val.testBit 4 = true → m.val.testBit 6 = true → 6 ≤ pop m.val + potential m.val := by decide +kernel
#print axioms no_mask04
#print axioms no_mask46
end PEqualNP.Research.BranchBudget
