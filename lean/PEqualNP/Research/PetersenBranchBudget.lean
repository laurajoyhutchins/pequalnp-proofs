import Lean
namespace PEqualNP.Research.BranchBudget

def adj : Array Nat := #[50,69,138,276,9,385,258,36,104]
def packedPotential : Nat := 589748214790610658905909838019139027806686525983731554724062180551842188556693038363435076607406622588360006084720385011001959057761042583103864457577469780012845074060431493902197647909235875082329760140368740456269860577922480918168913433825448479078305284458368011924242826843905060877001701170414264784173928962111672046249283343387673748774817459067748069964636318672615841207176514839158966177906364267130283764614042368388986284301089001090559784109861
def potential (m : Nat) : Nat := (packedPotential >>> (3*m)) &&& 7
def res (m i : Nat) : Nat := (adj[i]?.getD 0) &&& (511 ^^^ m)
def close (m : Nat) : Nat := m ||| ((List.range 9).foldl (fun a i => if res m i = 0 then a ||| (1 <<< i) else a) 0)
def twins (m i : Nat) : Nat := (List.range 9).foldl (fun a j => if !m.testBit j && res m j == res m i then a ||| (1 <<< j) else a) 0
def advance (m i : Nat) : Nat := if !m.testBit i && res m i != 0 then close (m ||| twins m i) else close m
def pop (m : Nat) : Nat := (List.range 9).countP (fun i => m.testBit i)
def allowed (m : Nat) : Bool := [5,13,37,45,69,77,101,109].contains m

set_option maxHeartbeats 0
set_option maxRecDepth 30000

theorem terminal : potential 511 = 0 := by decide +kernel
-- A local certificate of the lower potential, rather than trusting the DP generator.
def check (m : Nat) : Bool := (potential m == potential (close m)) && (List.range 9).all (fun i => decide (advance m i < 512 ∧ potential m ≤ 1 + potential (advance m i) ∧ potential (m ||| (1 <<< i)) ≤ potential m))
def chunk (j : Nat) : Bool := (List.range 16).all (fun k => check (16*j+k))
theorem check0 : chunk 0 = true := by decide +kernel
theorem check1 : chunk 1 = true := by decide +kernel
theorem check2 : chunk 2 = true := by decide +kernel
theorem check3 : chunk 3 = true := by decide +kernel
theorem check4 : chunk 4 = true := by decide +kernel
theorem check5 : chunk 5 = true := by decide +kernel
theorem check6 : chunk 6 = true := by decide +kernel
theorem check7 : chunk 7 = true := by decide +kernel
theorem check8 : chunk 8 = true := by decide +kernel
theorem check9 : chunk 9 = true := by decide +kernel
theorem check10 : chunk 10 = true := by decide +kernel
theorem check11 : chunk 11 = true := by decide +kernel
theorem check12 : chunk 12 = true := by decide +kernel
theorem check13 : chunk 13 = true := by decide +kernel
theorem check14 : chunk 14 = true := by decide +kernel
theorem check15 : chunk 15 = true := by decide +kernel
theorem check16 : chunk 16 = true := by decide +kernel
theorem check17 : chunk 17 = true := by decide +kernel
theorem check18 : chunk 18 = true := by decide +kernel
theorem check19 : chunk 19 = true := by decide +kernel
theorem check20 : chunk 20 = true := by decide +kernel
theorem check21 : chunk 21 = true := by decide +kernel
theorem check22 : chunk 22 = true := by decide +kernel
theorem check23 : chunk 23 = true := by decide +kernel
theorem check24 : chunk 24 = true := by decide +kernel
theorem check25 : chunk 25 = true := by decide +kernel
theorem check26 : chunk 26 = true := by decide +kernel
theorem check27 : chunk 27 = true := by decide +kernel
theorem check28 : chunk 28 = true := by decide +kernel
theorem check29 : chunk 29 = true := by decide +kernel
theorem check30 : chunk 30 = true := by decide +kernel
theorem check31 : chunk 31 = true := by decide +kernel
theorem chunk_ok (j : Nat) (hj : j < 32) : chunk j = true := by
  have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 ∨ j = 30 ∨ j = 31 := by omega
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · rw [h]; exact check0
  · rw [h]; exact check1
  · rw [h]; exact check2
  · rw [h]; exact check3
  · rw [h]; exact check4
  · rw [h]; exact check5
  · rw [h]; exact check6
  · rw [h]; exact check7
  · rw [h]; exact check8
  · rw [h]; exact check9
  · rw [h]; exact check10
  · rw [h]; exact check11
  · rw [h]; exact check12
  · rw [h]; exact check13
  · rw [h]; exact check14
  · rw [h]; exact check15
  · rw [h]; exact check16
  · rw [h]; exact check17
  · rw [h]; exact check18
  · rw [h]; exact check19
  · rw [h]; exact check20
  · rw [h]; exact check21
  · rw [h]; exact check22
  · rw [h]; exact check23
  · rw [h]; exact check24
  · rw [h]; exact check25
  · rw [h]; exact check26
  · rw [h]; exact check27
  · rw [h]; exact check28
  · rw [h]; exact check29
  · rw [h]; exact check30
  · rw [h]; exact check31
theorem check_ok (m : Fin 512) : check m.val = true := by
  have hb := chunk_ok (m.val / 16) (by omega)
  have hh := List.all_eq_true.mp hb (m.val % 16) (List.mem_range.mpr (by omega))
  have eq : 16 * (m.val / 16) + m.val % 16 = m.val := by omega
  rwa [eq] at hh

theorem close_valid (m : Fin 512) : potential m.val = potential (close m.val) := by
  exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp (check_ok m)).1

theorem step_and_monotone (m : Fin 512) (i : Fin 9) : advance m.val i.val < 512 ∧ potential m.val ≤ 1 + potential (advance m.val i.val) ∧ potential (m.val ||| (1 <<< i.val)) ≤ potential m.val := by
  exact of_decide_eq_true (List.all_eq_true.mp (Bool.and_eq_true_iff.mp (check_ok m)).2 _ (List.mem_range.mpr i.isLt))

theorem step_valid (m : Fin 512) (i : Fin 9) : advance m.val i.val < 512 ∧ potential m.val ≤ 1 + potential (advance m.val i.val) := by
  have h := step_and_monotone m i
  exact ⟨h.1,h.2.1⟩

theorem monotone_step (m : Fin 512) (i : Fin 9) : potential (m.val ||| (1 <<< i.val)) ≤ potential m.val := (step_and_monotone m i).2.2
theorem allowed_masks : ∀ m : Fin 512, m.val.testBit 0 = true → m.val.testBit 2 = true → pop m.val + potential m.val ≤ 5 → allowed m.val = true := by decide +kernel

theorem forbidden_branch : ∀ m : Fin 512, allowed m.val = true → (m.val.testBit 1 = false ∧ m.val.testBit 4 = false ∧ m.val.testBit 7 = false ∧ m.val.testBit 8 = false) := by decide +kernel

theorem seed04 : potential 17 = 4 := by decide +kernel
theorem seed46 : potential 80 = 4 := by decide +kernel

-- Any valid walk reaching the full mask requires at least its initial potential.
inductive Walk : Nat → Fin 512 → Fin 512 → Prop where
  | nil (m : Fin 512) : Walk 0 m m
  | step (m : Fin 512) (i : Fin 9) {n : Nat} {z : Fin 512}
      (tail : Walk n ⟨advance m.val i.val, (step_valid m i).1⟩ z) : Walk (n+1) m z

theorem walk_bound {k : Nat} {m z : Fin 512} (h : Walk k m z) : potential m.val ≤ k + potential z.val := by
  induction h with
  | nil m => simp
  | step m i tail ih =>
    simp only [Fin.val_mk] at ih
    have h := (step_valid m i).2
    omega

theorem anchored_mask {k : Nat} (m : Fin 512) (h : Walk k m 511) (ha : m.val.testBit 0 = true) (hb : m.val.testBit 2 = true) (budget : pop m.val + k ≤ 5) : allowed m.val = true := by
  have e := walk_bound h
  change potential m.val ≤ k + potential 511 at e
  rw [terminal, Nat.add_zero] at e
  exact allowed_masks m ha hb (by omega)

#print axioms anchored_mask
#print axioms step_valid
#print axioms allowed_masks
#print axioms monotone_step
end PEqualNP.Research.BranchBudget
