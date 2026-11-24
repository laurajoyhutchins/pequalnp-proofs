import PEqualNP.Defs
namespace PEqualNP.Research.Hoist
open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def idx (n k i : Nat) : Nat :=
  if i < n then i else if i = k then n else if i < k then i+1 else i

def remap (n k cap pos : Nat) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (fun i => if i < pos then idx n k i else cap)⟩

def replay (n k cap pos : Nat) : List Gate → List Gate
  | [] => []
  | g::gs => if pos = k then replay n k cap (pos+1) gs
      else remap n k cap pos g :: replay n k cap (pos+1) gs

def extra (k pos : Nat) := if pos ≤ k then 1 else 0

def Inv (n k : Nat) (seed : Bool) (w v : List Bool) : Prop :=
  n ≤ w.length ∧ v.length = w.length + extra k w.length ∧
  v.getD n false = seed ∧ ∀ i < w.length, v.getD (idx n k i) false = w.getD i false

theorem idx_lt (n k pos i : Nat) (hn : n ≤ k) (ha : n ≤ pos) (hi : i < pos) :
    idx n k i < pos + extra k pos := by
  unfold idx extra
  repeat' first | split | omega

theorem idx_ne_seed (n k i : Nat) (h : i ≠ k) (hn : n ≤ k) : idx n k i ≠ n := by
  unfold idx
  repeat' first | split | omega

theorem idx_new (n k pos : Nat) (hn : n ≤ pos) (h : pos ≠ k) :
    idx n k pos = pos + extra k pos := by
  unfold idx extra
  repeat' first | split | omega

theorem get_append_old (w : List Bool) (b : Bool) (i : Nat) (h : i < w.length) :
    (w++[b]).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem get_append_new (w : List Bool) (b : Bool) :
    (w++[b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem get_missing (w : List Bool) (i : Nat) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem init (x : List Bool) (k : Nat) (b : Bool) (hk : x.length ≤ k) :
    Inv x.length k b x (x++[b]) := by
  refine ⟨by omega, by simp [extra,hk], get_append_new _ _, ?_⟩
  intro i hi
  rw [show idx x.length k i = i by simp [idx,hi]]
  exact get_append_old _ _ _ hi

theorem val_remap (n k cap : Nat) (b : Bool) (w v : List Bool) (g : Gate)
    (h : Inv n k b w v) (hcap : v.length ≤ cap) :
    (remap n k cap w.length g).op.eval ((remap n k cap w.length g).inputs.map fun i => v.getD i false) =
    g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [remap, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < w.length
  · simp only [hi, ite_true]
    exact h.2.2.2 i hi
  · simp only [hi, ite_false]
    rw [get_missing v cap hcap, get_missing w i (by omega)]

theorem advance (n k cap : Nat) (b : Bool) (w v : List Bool) (g : Gate)
    (hn : n ≤ k) (h : Inv n k b w v) (hcap : v.length ≤ cap) (hk : w.length ≠ k) :
    Inv n k b (step w g) (step v (remap n k cap w.length g)) := by
  have eq := val_remap n k cap b w v g h hcap
  let z := g.op.eval (g.inputs.map fun i => w.getD i false)
  have ev : step v (remap n k cap w.length g) = v++[z] := by simp only [step, eq, z]
  rw [ev]
  change Inv n k b (w++[z]) (v++[z])
  have seedlt : n < v.length := by
    have ha := h.1; have hv := h.2.1
    unfold extra at hv
    split at hv <;> omega
  refine ⟨by simp; have := h.1; omega, ?_, ?_, ?_⟩
  · simp only [List.length_append,List.length_singleton,h.2.1,extra]
    split <;> split <;> omega
  · rw [get_append_old _ _ _ seedlt]; exact h.2.2.1
  · intro i hi
    by_cases old : i < w.length
    · rw [get_append_old _ _ _ old, get_append_old _ _ _ (h.2.1 ▸ idx_lt n k w.length i hn h.1 old)]
      exact h.2.2.2 i old
    · have ei : i = w.length := by simp at hi; omega
      subst i
      rw [idx_new n k w.length h.1 hk, ← h.2.1, get_append_new, get_append_new]

theorem skip (n k : Nat) (b : Bool) (w v : List Bool) (g : Gate)
    (h : Inv n k b w v) (hk : w.length = k)
    (hb : g.op.eval (g.inputs.map fun i => w.getD i false) = b) :
    Inv n k b (step w g) v := by
  have hn := h.1
  change Inv n k b (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) v
  rw [hb]
  refine ⟨by simp; omega, ?_, h.2.2.1, ?_⟩
  · simp [h.2.1, extra, hk]
  · intro i hi
    by_cases old : i < w.length
    · rw [get_append_old _ _ _ old]
      exact h.2.2.2 i old
    · have ei : i = w.length := by simp at hi; omega
      subst i
      rw [show idx n k w.length = n by unfold idx; split <;> simp_all <;> omega, get_append_new]
      exact h.2.2.1

-- The skipped gate's value is supplied by the hoisted first wire.
def good (k : Nat) (b : Bool) (w : List Bool) : List Gate → Prop
  | [] => True
  | g::gs => (w.length = k → g.op.eval (g.inputs.map fun i => w.getD i false) = b) ∧ good k b (step w g) gs

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length+1 := by simp [step]

theorem replay_sound (n k cap : Nat) (b : Bool) (gs : List Gate) (w v : List Bool)
    (hn : n ≤ k) (h : Inv n k b w v) (hg : good k b w gs)
    (hc : w.length + gs.length + extra k (w.length+gs.length) ≤ cap) :
    Inv n k b (gs.foldl step w) ((replay n k cap w.length gs).foldl step v) := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
    have hc' : (step w g).length + gs.length + extra k ((step w g).length+gs.length) ≤ cap := by
      rw [step_len]; simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hc
    simp only [List.foldl_cons,replay]
    by_cases hk : w.length = k
    · rw [ite_eq_left hk]
      have he : w.length+1 = (step w g).length := (step_len _ _).symm
      rw [he]
      exact ih _ _ (skip n k b w v g h hk (hg.1 hk)) hg.2 hc'
    · rw [ite_eq_right hk,List.foldl_cons]
      have he : w.length+1 = (step w g).length := (step_len _ _).symm
      rw [he]
      have hv : v.length ≤ cap := by
        rw [h.2.1]; unfold extra at *
        simp only [List.length_cons] at hc
        split <;> split at hc <;> omega
      exact ih _ _ (advance n k cap b w v g hn h hv hk) hg.2 hc'

theorem fold_len (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih,step_len,List.length_cons]; omega

theorem fold_read (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by rw [step_len]; omega)]
    exact get_append_old _ _ _ hi

theorem good_of_read (gs : List Gate) (w : List Bool) (k : Nat) (b : Bool)
    (h : (gs.foldl step w).getD k false = b) : good k b w gs := by
  induction gs generalizing w with
  | nil => trivial
  | cons g gs ih =>
    refine ⟨?_, ih _ h⟩
    intro hk
    rw [List.foldl_cons, fold_read gs (step w g) k (by rw [step_len]; omega)] at h
    rw [← hk] at h
    exact (get_append_new _ _).symm.trans h

theorem replay_len (gs : List Gate) (n k cap pos : Nat) (h1 : pos ≤ k)
    (h2 : k < pos+gs.length) : (replay n k cap pos gs).length + 1 = gs.length := by
  induction gs generalizing pos with
  | nil => simp at h2; omega
  | cons g gs ih =>
    simp only [replay,List.length_cons]
    by_cases h : pos = k
    · rw [ite_eq_left h]
      have aux : ∀ (ls : List Gate) (p : Nat), k < p → (replay n k cap p ls).length = ls.length := by
        intro ls p hp
        induction ls generalizing p with
        | nil => rfl
        | cons a as ih => simp [replay,show p ≠ k by omega,ih (p+1) (by omega)]
      rw [aux _ _ (by omega)]
    · rw [ite_eq_right h,List.length_cons]
      have e := ih (pos+1) (by omega) (by simp at h2; omega)
      omega

def hoist (C : Circuit) (n k : Nat) (g : Gate) : Circuit :=
  ⟨g :: replay n k (n+C.size) n C.gates,
    if C.output < n+C.size then idx n k C.output else n+C.size⟩

theorem hoist_size (C : Circuit) (n k : Nat) (h1 : n ≤ k) (h2 : k < n+C.size) :
    (hoist C n k g).size = C.size := by
  exact replay_len C.gates n k (n+C.size) n h1 h2

theorem hoist_sound (C : Circuit) (n k : Nat) (g : Gate) (x : List Bool)
    (hx : x.length = n) (h1 : n ≤ k) (h2 : k < n+C.size)
    (hval : (C.wires x).getD k false = g.op.eval (g.inputs.map fun i => x.getD i false)) :
    (hoist C n k g).eval x = C.eval x := by
  let b := g.op.eval (g.inputs.map fun i => x.getD i false)
  have hg : good k b x C.gates := good_of_read _ _ _ _ hval
  have hi : Inv n k b x (step x g) := by
    rw [← hx] at h1 ⊢
    exact init _ _ _ h1
  have cap : x.length + C.gates.length + extra k (x.length+C.gates.length) ≤ n+C.size := by
    rw [hx]; have h : C.size = C.gates.length := rfl
    simp [extra,show ¬ n+C.gates.length ≤ k by omega,h]
  have hr := replay_sound n k (n+C.size) b C.gates x (step x g) h1 hi hg cap
  let w := C.gates.foldl step x
  let v := (replay n k (n+C.size) n C.gates).foldl step (step x g)
  rw [hx] at hr
  change Inv n k b w v at hr
  have wl : w.length = n+C.size := by simp [w,fold_len,hx,Circuit.size]
  have vl : v.length = n+C.size := by rw [hr.2.1,wl]; simp [extra,show ¬ n+C.size ≤ k by omega]
  change v.getD (if C.output < n+C.size then idx n k C.output else n+C.size) false = w.getD C.output false
  by_cases ho : C.output < n+C.size
  · simp only [ho,ite_true]; exact hr.2.2.2 _ (wl.symm ▸ ho)
  · simp only [ho,ite_false]; rw [get_missing v _ (by omega),get_missing w _ (by omega)]

theorem replay_legal (P : Gate → Prop) (closed : ∀ g, P g → ∀ f : Nat → Nat, P ⟨g.op,g.inputs.map f⟩)
    (gs : List Gate) (n k cap pos : Nat) (hg : ∀ g ∈ gs, P g) : ∀ g ∈ replay n k cap pos gs, P g := by
  induction gs generalizing pos with
  | nil => simp [replay]
  | cons a as ih =>
    have ht : ∀ g ∈ as, P g := fun g h => hg g (List.mem_cons_of_mem _ h)
    simp only [replay]
    split
    · exact ih _ ht
    · intro g h
      rcases List.mem_cons.mp h with h | h
      · subst g
        exact closed a (hg a (by simp)) _
      · exact ih _ ht g h

theorem hoist_legal (P : Gate → Prop) (closed : ∀ g, P g → ∀ f : Nat → Nat, P ⟨g.op,g.inputs.map f⟩)
    (C : Circuit) (n k : Nat) (g : Gate) (hg : P g) (hc : ∀ a ∈ C.gates, P a) :
    ∀ a ∈ (hoist C n k g).gates, P a := by
  intro a ha
  rcases List.mem_cons.mp ha with h | h
  · exact h.symm ▸ hg
  · exact replay_legal P closed C.gates n k (n+C.size) n hc a h

theorem hoist_first (C : Circuit) (n k : Nat) (g : Gate) (x : List Bool) (hx : x.length = n) :
    ((hoist C n k g).wires x).getD n false = g.op.eval (g.inputs.map fun i => x.getD i false) := by
  change ((replay n k (n+C.size) n C.gates).foldl step (step x g)).getD n false = _
  rw [fold_read _ _ _ (by rw [step_len,hx]; omega), ← hx]
  exact get_append_new _ _

-- Same gate predicate as the upstream FanInTwo, stated without Mathlib's Set.
def LegalGate (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def Legal (C : Circuit) : Prop := ∀ g ∈ C.gates, LegalGate g

def funOf (n : Nat) (C : Circuit) (x : Fin n → Bool) : Bool := C.eval (List.ofFn x)

def andGate {n : Nat} (i j : Fin n) : Gate := ⟨.and,[i.val,j.val]⟩

theorem andGate_eval {n : Nat} (i j : Fin n) (x : Fin n → Bool) :
    (andGate i j).op.eval ((andGate i j).inputs.map fun a => (List.ofFn x).getD a false) = (x i && x j) := by
  simp [andGate,GateOp.eval,List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,j.isLt]

theorem legal_closed (g : Gate) (h : LegalGate g) (f : Nat → Nat) : LegalGate ⟨g.op,g.inputs.map f⟩ := by
  simpa [LegalGate] using h

-- A verified conditional reduction: an AND-first lower bound lifts to a
-- global exclusion of every semantically equal internal wire.
theorem conjunction_exclusion {n L : Nat} {F : (Fin n → Bool) → Bool}
    (andBound : ∀ (D : Circuit) (i j : Fin n), i ≠ j → Legal D → funOf n D = F →
      (∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD n false = (x i && x j)) → L ≤ D.size)
    (C : Circuit) (hlegal : Legal C) (hf : funOf n C = F) (hs : C.size < L)
    (i j : Fin n) (hne : i ≠ j) (k : Nat) (hk : n ≤ k) (hk' : k < n+C.size) :
    ¬ (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD k false = (x i && x j)) := by
  intro hval
  let g := andGate i j
  let D := hoist C n k g
  have sz : D.size = C.size := hoist_size C n k hk hk'
  have leg : Legal D := hoist_legal LegalGate legal_closed C n k g (by simp [LegalGate,g,andGate]) hlegal
  have func : funOf n D = F := by
    funext x
    have e := hoist_sound C n k g (List.ofFn x) (by simp) hk hk' ((hval x).trans (andGate_eval i j x).symm)
    exact e.trans (congrFun hf x)
  have first (x : Fin n → Bool) : (D.wires (List.ofFn x)).getD n false = (x i && x j) :=
    (hoist_first C n k g (List.ofFn x) (by simp)).trans (andGate_eval i j x)
  have low := andBound D i j hne leg func first
  omega

#print axioms conjunction_exclusion
#print axioms hoist_legal
#print axioms hoist_first
#print axioms replay_sound
#print axioms hoist_sound
#print axioms hoist_size
end PEqualNP.Research.Hoist
