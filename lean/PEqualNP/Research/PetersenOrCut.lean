import PEqualNP.Research.GateHoist
namespace PEqualNP.Research.Hoist
open PEqualNP.CircuitLowerBounds

def renameIndex {n : Nat} (p : Fin n → Fin n) (i : Nat) : Nat :=
  if h : i < n then (p ⟨i,h⟩).val else i

def renameGate {n : Nat} (p : Fin n → Fin n) (g : Gate) : Gate := ⟨g.op,g.inputs.map (renameIndex p)⟩

def renameCircuit {n : Nat} (p : Fin n → Fin n) (C : Circuit) : Circuit :=
  ⟨C.gates.map (renameGate p),renameIndex p C.output⟩

theorem rename_legal {n : Nat} (p : Fin n → Fin n) (C : Circuit) (h : Legal C) : Legal (renameCircuit p C) := by
  intro g hg
  obtain ⟨g',hm,rfl⟩ := List.mem_map.mp hg
  exact legal_closed _ (h _ hm) _

theorem rename_size {n : Nat} (p : Fin n → Fin n) (C : Circuit) : (renameCircuit p C).size = C.size := by
  simp [renameCircuit,Circuit.size]

def RInv {n : Nat} (p : Fin n → Fin n) (w v : List Bool) : Prop :=
  n ≤ w.length ∧ w.length = v.length ∧ ∀ i, v.getD (renameIndex p i) false = w.getD i false

theorem rename_init {n : Nat} (p : Fin n → Fin n) (x : Fin n → Bool) :
    RInv p (List.ofFn (fun i => x (p i))) (List.ofFn x) := by
  refine ⟨by simp,by simp,?_⟩
  intro i
  by_cases hi : i<n
  · simp [renameIndex,hi,List.getD_eq_getElem?_getD,(p ⟨i,hi⟩).isLt]
  · simp [renameIndex,hi,List.getD_eq_getElem?_getD]

theorem rename_step {n : Nat} (p : Fin n → Fin n) (w v : List Bool) (g : Gate) (h : RInv p w v) :
    RInv p (step w g) (step v (renameGate p g)) := by
  let b := g.op.eval (g.inputs.map fun i => w.getD i false)
  have eq : step v (renameGate p g) = v++[b] := by
    simp only [step,renameGate,List.map_map,Function.comp_def,b]
    congr 3
    exact List.map_congr_left (fun i _ => h.2.2 i)
  rw [eq]
  change RInv p (w++[b]) (v++[b])
  refine ⟨by simp; have := h.1; omega,by simp [h.2.1],?_⟩
  intro i
  by_cases hi : i < w.length
  · have hr : renameIndex p i < v.length := by
      unfold renameIndex
      split
      · have := (p ⟨i,by assumption⟩).isLt
        have := h.1; have := h.2.1; omega
      · have := h.2.1; omega
    rw [get_append_old _ _ _ hr,get_append_old _ _ _ hi]
    exact h.2.2 i
  · have hn : ¬i<n := by have := h.1; omega
    simp only [renameIndex,hn,dite_false]
    by_cases he : i = w.length
    · rw [he,h.2.1,get_append_new,←h.2.1,get_append_new]
    · have h1 : (w++[b]).length ≤ i := by simp; omega
      have h2 : (v++[b]).length ≤ i := by simp [← h.2.1]; omega
      rw [get_missing _ _ h1,get_missing _ _ h2]

theorem rename_fold {n : Nat} (p : Fin n → Fin n) (gs : List Gate) (w v : List Bool) (h : RInv p w v) :
    RInv p (gs.foldl step w) ((gs.map (renameGate p)).foldl step v) := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih => exact ih _ _ (rename_step p w v g h)

theorem rename_read {n : Nat} (p : Fin n → Fin n) (C : Circuit) (x : Fin n → Bool) (i : Nat) :
    ((renameCircuit p C).wires (List.ofFn x)).getD (renameIndex p i) false =
    (C.wires (List.ofFn (fun j => x (p j)))).getD i false :=
  (rename_fold p C.gates _ _ (rename_init p x)).2.2 i

theorem rename_fun {n : Nat} (p : Fin n → Fin n) (C : Circuit) (x : Fin n → Bool) :
    funOf n (renameCircuit p C) x = funOf n C (fun j => x (p j)) := rename_read p C x C.output

def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def autolist : List (List (Fin 9)) := [
 [0,1,2,3,4,5,6,7,8],
 [3,8,5,0,4,2,6,7,1],
 [0,5,8,3,4,1,7,6,2],
 [3,2,1,0,4,8,7,6,5],
 [1,0,5,8,6,2,4,7,3],
 [8,3,2,1,6,5,4,7,0],
 [1,2,3,8,6,0,7,4,5],
 [8,5,0,1,6,3,7,4,2],
 [2,3,8,5,7,1,4,6,0],
 [5,0,1,2,7,8,4,6,3],
 [2,1,0,5,7,3,6,4,8],
 [5,8,3,2,7,0,6,4,1]]

def auto (k : Fin 12) (i : Fin 9) : Fin 9 := (autolist.getD k.val []).getD i.val 0

def reps : List (Fin 9 × Fin 9) := [(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)]

def rep (r : Fin 6) : Fin 9 × Fin 9 := reps.getD r.val (0,0)

-- Finite orbit table; the map sends the given pair to a listed representative.
theorem cover : ∀ i j : Fin 9, i ≠ j → ∃ k : Fin 12, ∃ r : Fin 6,
    (auto k i = (rep r).1 ∧ auto k j = (rep r).2) ∨ (auto k j = (rep r).1 ∧ auto k i = (rep r).2) := by decide

-- Prove invariance symbolically, rather than computing on all 512 inputs.
theorem autoinv (k : Fin 12) (x : Fin 9 → Bool) : edge (fun i => x (auto k i)) = edge x := by
  have hk : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 ∨ k.val = 4 ∨ k.val = 5 ∨ k.val = 6 ∨ k.val = 7 ∨ k.val = 8 ∨ k.val = 9 ∨ k.val = 10 ∨ k.val = 11 := by omega
  rcases hk with h|h|h|h|h|h|h|h|h|h|h|h
  · have e : k = (0 : Fin 12) := Fin.ext h
    rw [e]
    change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) = edge x
    unfold edge
    ac_rfl
  · have e : k = (1 : Fin 12) := Fin.ext h
    rw [e]
    change ((x 3 && x 8) || (x 8 && x 5) || (x 5 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (x 3 && x 2) || (x 8 && x 6) || (x 5 && x 7) || (x 0 && x 1) || (x 2 && x 7) || (x 6 && x 1) || (x 1 && x 2)) = edge x
    unfold edge
    ac_rfl
  · have e : k = (2 : Fin 12) := Fin.ext h
    rw [e]
    change ((x 0 && x 5) || (x 5 && x 8) || (x 8 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 1) || (x 5 && x 7) || (x 8 && x 6) || (x 3 && x 2) || (x 1 && x 6) || (x 7 && x 2) || (x 2 && x 1)) = edge x
    unfold edge
    ac_rfl
  · have e : k = (3 : Fin 12) := Fin.ext h
    rw [e]
    change ((x 3 && x 2) || (x 2 && x 1) || (x 1 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (x 3 && x 8) || (x 2 && x 7) || (x 1 && x 6) || (x 0 && x 5) || (x 8 && x 6) || (x 7 && x 5) || (x 5 && x 8)) = edge x
    unfold edge
    ac_rfl
  · have e : k = (4 : Fin 12) := Fin.ext h
    rw [e]
    change ((x 1 && x 0) || (x 0 && x 5) || (x 5 && x 8) || (x 8 && x 6) || (x 6 && x 1) || (x 1 && x 2) || (x 0 && x 4) || (x 5 && x 7) || (x 8 && x 3) || (x 2 && x 7) || (x 4 && x 3) || (x 3 && x 2)) = edge x
    unfold edge
    ac_rfl
  · have e : k = (5 : Fin 12) := Fin.ext h
    rw [e]
    change ((x 8 && x 3) || (x 3 && x 2) || (x 2 && x 1) || (x 1 && x 6) || (x 6 && x 8) || (x 8 && x 5) || (x 3 && x 4) || (x 2 && x 7) || (x 1 && x 0) || (x 5 && x 7) || (x 4 && x 0) || (x 0 && x 5)) = edge x
    unfold edge
    ac_rfl
  · have e : k = (6 : Fin 12) := Fin.ext h
    rw [e]
    change ((x 1 && x 2) || (x 2 && x 3) || (x 3 && x 8) || (x 8 && x 6) || (x 6 && x 1) || (x 1 && x 0) || (x 2 && x 7) || (x 3 && x 4) || (x 8 && x 5) || (x 0 && x 4) || (x 7 && x 5) || (x 5 && x 0)) = edge x
    unfold edge
    ac_rfl
  · have e : k = (7 : Fin 12) := Fin.ext h
    rw [e]
    change ((x 8 && x 5) || (x 5 && x 0) || (x 0 && x 1) || (x 1 && x 6) || (x 6 && x 8) || (x 8 && x 3) || (x 5 && x 7) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 7 && x 2) || (x 2 && x 3)) = edge x
    unfold edge
    ac_rfl
  · have e : k = (8 : Fin 12) := Fin.ext h
    rw [e]
    change ((x 2 && x 3) || (x 3 && x 8) || (x 8 && x 5) || (x 5 && x 7) || (x 7 && x 2) || (x 2 && x 1) || (x 3 && x 4) || (x 8 && x 6) || (x 5 && x 0) || (x 1 && x 6) || (x 4 && x 0) || (x 0 && x 1)) = edge x
    unfold edge
    ac_rfl
  · have e : k = (9 : Fin 12) := Fin.ext h
    rw [e]
    change ((x 5 && x 0) || (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 7) || (x 7 && x 5) || (x 5 && x 8) || (x 0 && x 4) || (x 1 && x 6) || (x 2 && x 3) || (x 8 && x 6) || (x 4 && x 3) || (x 3 && x 8)) = edge x
    unfold edge
    ac_rfl
  · have e : k = (10 : Fin 12) := Fin.ext h
    rw [e]
    change ((x 2 && x 1) || (x 1 && x 0) || (x 0 && x 5) || (x 5 && x 7) || (x 7 && x 2) || (x 2 && x 3) || (x 1 && x 6) || (x 0 && x 4) || (x 5 && x 8) || (x 3 && x 4) || (x 6 && x 8) || (x 8 && x 3)) = edge x
    unfold edge
    ac_rfl
  · have e : k = (11 : Fin 12) := Fin.ext h
    rw [e]
    change ((x 5 && x 8) || (x 8 && x 3) || (x 3 && x 2) || (x 2 && x 7) || (x 7 && x 5) || (x 5 && x 0) || (x 8 && x 6) || (x 3 && x 4) || (x 2 && x 1) || (x 0 && x 4) || (x 6 && x 1) || (x 1 && x 0)) = edge x
    unfold edge
    ac_rfl

theorem allAndBound
    (bounds : ∀ r : Fin 6, ∀ C : Circuit, Legal C → funOf 9 C = edge →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x (rep r).1 && x (rep r).2)) → 16 ≤ C.size)
    (C : Circuit) (i j : Fin 9) (hne : i ≠ j) (hc : Legal C) (hf : funOf 9 C = edge)
    (first : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x i && x j)) : 16 ≤ C.size := by
  obtain ⟨k,r,hr⟩ := cover i j hne
  let D := renameCircuit (auto k) C
  have leg : Legal D := rename_legal _ _ hc
  have fs : funOf 9 D = edge := by
    funext x
    exact (rename_fun _ _ _).trans ((congrFun hf _).trans (autoinv k x))
  have anchor (x : Fin 9 → Bool) : (D.wires (List.ofFn x)).getD 9 false = (x (rep r).1 && x (rep r).2) := by
    have eq : renameIndex (auto k) 9 = 9 := by simp [renameIndex]
    have hh := rename_read (auto k) C x 9
    rw [eq] at hh
    rw [hh,first]
    rcases hr with h|h
    · simp [h.1,h.2]
    · simp [h.1,h.2,Bool.and_comm]
  have low := bounds r D leg fs anchor
  rwa [rename_size] at low

def SixBounds : Prop := ∀ r : Fin 6, ∀ C : Circuit, Legal C → funOf 9 C = edge →
  (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x (rep r).1 && x (rep r).2)) → 16 ≤ C.size

def NoRawAnd (C : Circuit) : Prop := ∀ i j : Fin 9, i ≠ j → ∀ k : Nat, 9 ≤ k → k < 9+C.size →
    ¬ (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD k false = (x i && x j))

theorem noRawAnd_of_six (h : SixBounds) (C : Circuit) (hc : Legal C) (hf : funOf 9 C = edge)
    (hs : C.size < 16) : NoRawAnd C := by
  intro i j hij k hk hk'
  apply conjunction_exclusion (allAndBound h) C hc hf hs i j hij k hk hk'

-- Exact OR-first reduction, uniform over every pair, conditional only on
-- the six accepted AND-first bounds and the restricted search obligation.
theorem or_first_cut (u v : Fin 9) (h : SixBounds)
    (residual : ∀ C : Circuit, Legal C → funOf 9 C = edge →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x u || x v)) →
      NoRawAnd C → 16 ≤ C.size) :
    ∀ C : Circuit, Legal C → funOf 9 C = edge →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x u || x v)) → 16 ≤ C.size := by
  intro C hc hf first
  by_cases hs : 16 ≤ C.size
  · exact hs
  · exact residual C hc hf first (noRawAnd_of_six h C hc hf (by omega))

#print axioms noRawAnd_of_six
#print axioms or_first_cut
#print axioms cover
#print axioms autoinv
#print axioms allAndBound
end PEqualNP.Research.Hoist
