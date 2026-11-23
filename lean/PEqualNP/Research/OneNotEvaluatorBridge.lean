import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Research.OneNotEvaluatorBridge

-- The following evaluator identities are adapted from L-meta-270,
-- originally proved by k-sandhu in upstream PR 149.

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

private lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

private lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

private lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

private def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

private lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

-- At a gate, reads of earlier wires agree with the completed run.
-- All other reads contribute false, even if the wire is produced later.
private lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]


private lemma pre_mono {n : ℕ} (C : Circuit) (q : ℕ)
    (hG : ∀ w, n ≤ w → w < q → ∀ hw : w < n + C.size,
      let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
      g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true)
    (w : ℕ) (hwq : w < q) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
      have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hG w (by omega) hwq hw
      have hstep (v : ℕ) :
          (if v < w then value C x v else false) = true →
          (if v < w then value C y v else false) = true := by
        by_cases hv : v < w
        · simpa only [if_pos hv] using ih v hv (hv.trans hwq)
        · simp [hv]
      have ex := gate_value C x w (by omega) hw
      have ey := gate_value C y w (by omega) hw
      change value C x w = g.op.eval
        (g.inputs.map fun v => if v < w then value C x v else false) at ex
      change value C y w = g.op.eval
        (g.inputs.map fun v => if v < w then value C y v else false) at ey
      rw [ex, ey]
      rcases hg with hg | hg
      · simp only [hg, GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
        intro ha z hz
        obtain ⟨v, hv, rfl⟩ := hz
        exact hstep v (ha _ ⟨v, hv, rfl⟩)
      · simp only [hg, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
        rintro ⟨z, ⟨v, hv, rfl⟩, hz⟩
        exact ⟨_, ⟨v, hv, rfl⟩, hstep v hz⟩
    · simp [missing_value C x w (by omega)]

private lemma not_unique (gs : List Gate)
    (h : ∃ ι : Fin 1 → Fin gs.length, ∀ i : Fin gs.length,
      (gs.get i).op = GateOp.not → ∃ j : Fin 1, ι j = i)
    (i j : Fin gs.length) (hi : (gs.get i).op = GateOp.not)
    (hj : (gs.get j).op = GateOp.not) : i = j := by
  obtain ⟨ι, hι⟩ := h
  obtain ⟨a, ha⟩ := hι i hi
  obtain ⟨b, hb⟩ := hι j hj
  have hab : a = b := Subsingleton.elim _ _
  exact ha.symm.trans ((congrArg ι hab).trans hb)

end PEqualNP.Research.OneNotEvaluatorBridge

open PEqualNP.Research.OneNotEvaluatorBridge in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Research.OneNotEvaluatorBridge : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n))
  (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ),
  (∀ i, 2 ≤ (S i).card) →
  (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
    g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
    g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
  (∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length,
    (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin 1, ι j = i) →
  (∀ (i : Fin m) (x : Fin n → Bool),
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out i⟩ (List.ofFn x) =
      decide (∃ v ∈ S i, x v = true)) →
  let W : ℕ → Finset (Fin n) → Prop := fun w x =>
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩
      (List.ofFn (fun v : Fin n => decide (v ∈ x))) = true
  ∃ (o a b : Fin m → ℕ) (k : Fin m → Bool),
    (∀ v : Fin n, ∀ x, W v.val x ↔ v ∈ x) ∧
    (∀ i, n ≤ o i ∧ o i < n + gates.length) ∧
    (∀ i, a i < o i ∧ b i < o i) ∧
    (∀ i x, W (o i) x ↔ ∃ v ∈ S i, v ∈ x) ∧
    (∀ i w, w < o i → ¬ (∀ x, W w x ↔ ∃ v ∈ S i, v ∈ x)) ∧
    (∀ i, k i = true → ∀ x, W (o i) x ↔ W (a i) x ∧ W (b i) x) ∧
    (∀ i, k i = false → ∀ x, W (o i) x ↔ W (a i) x ∨ W (b i) x) := by
  classical
  intro n m S gates out hsize hG hnot hout
  dsimp only
  let C : Circuit := ⟨gates, 0⟩
  let X (x : Finset (Fin n)) : Fin n → Bool := fun v => decide (v ∈ x)
  let W (w : ℕ) (x : Finset (Fin n)) : Prop := value C (X x) w = true
  let F (i : Fin m) (x : Finset (Fin n)) : Prop := ∃ v ∈ S i, v ∈ x
  have hinput (v : Fin n) (x : Finset (Fin n)) : W v.val x ↔ v ∈ x := by
    simp [W, X, input_value]
  have hsingle (i : Fin m) (v : Fin n) : F i {v} ↔ v ∈ S i := by
    simp [F]
  have hnonempty (i : Fin m) : (S i).Nonempty :=
    Finset.card_pos.mp (by have := hsize i; omega)
  have hF0 (i : Fin m) : ¬ F i ∅ := by simp [F]
  have hF1 (i : Fin m) : F i Finset.univ := by
    obtain ⟨v, hv⟩ := hnonempty i
    exact ⟨v, hv, Finset.mem_univ v⟩
  have hex (i : Fin m) : ∃ w : ℕ, ∀ x, W w x ↔ F i x := by
    refine ⟨out i, fun x => ?_⟩
    change Circuit.eval ⟨gates, out i⟩ (List.ofFn (X x)) = true ↔ F i x
    rw [hout i (X x)]
    simp [F, X]
  let o (i : Fin m) := Nat.find (hex i)
  have ho (i : Fin m) (x : Finset (Fin n)) : W (o i) x ↔ F i x :=
    Nat.find_spec (hex i) x
  have hearly (i : Fin m) (w : ℕ) (hw : w < o i) :
      ¬ (∀ x, W w x ↔ F i x) := by
    intro h
    have hmin := Nat.find_min' (hex i) h
    change o i ≤ w at hmin
    omega
  have hob (i : Fin m) : n ≤ o i ∧ o i < n + C.size := by
    constructor
    · by_contra! h
      let v : Fin n := ⟨o i, h⟩
      have hsub : S i ⊆ {v} := by
        intro u hu
        have hv := (hinput v {u}).mp ((ho i {u}).mpr ((hsingle i u).mpr hu))
        simpa [eq_comm] using hv
      have hc := Finset.card_le_card hsub
      simp at hc
      have hs := hsize i
      omega
    · by_contra! h
      have hv := (ho i Finset.univ).mpr (hF1 i)
      change value C (X Finset.univ) (o i) = true at hv
      rw [missing_value C _ _ h] at hv
      contradiction
  have hshape (i : Fin m) : ∃ (a b : ℕ) (k : Bool),
      a < o i ∧ b < o i ∧
      (k = true → ∀ x, W (o i) x ↔ W a x ∧ W b x) ∧
      (k = false → ∀ x, W (o i) x ↔ W a x ∨ W b x) := by
    let w := o i
    have hn : n ≤ w := (hob i).1
    have hw : w < n + C.size := (hob i).2
    have hj : w - n < gates.length := by
      change w < n + gates.length at hw
      omega
    let g := C.gates[w - n]'(by simpa [C] using hj)
    have hgmem : g ∈ gates := by
      change gates[w-n] ∈ gates
      exact List.getElem_mem _
    obtain ⟨hop, hlen⟩ := hG g hgmem
    have hval (x : Finset (Fin n)) :
        value C (X x) w = g.op.eval
          (g.inputs.map fun t => if t < w then value C (X x) t else false) :=
      gate_value C (X x) w hn hw
    have hv0 : ¬ W w ∅ := fun h => hF0 i ((ho i ∅).mp h)
    have hv1 : W w Finset.univ := (ho i Finset.univ).mpr (hF1 i)
    have hcopy (t : ℕ) (ht : t < w)
        (he : ∀ x, W w x ↔ W t x) : False :=
      hearly i t ht (fun x => (he x).symm.trans (ho i x))
    have hfalse (he : ∀ x, ¬ W w x) : False := he _ hv1
    have htrue (he : ∀ x, W w x) : False := hv0 (he _)
    have hnotop : g.op ≠ GateOp.not := by
      intro hg
      let q : Fin gates.length := ⟨w-n, hj⟩
      have hq : (gates.get q).op = GateOp.not := hg
      have hpre : ∀ u, n ≤ u → u < w → ∀ hu : u < n + C.size,
          let g' := C.gates[u-n]'(by unfold Circuit.size at hu; omega)
          g'.op = GateOp.and ∨ g'.op = GateOp.or := by
        intro u hun huw hu
        have hul : u-n < gates.length := by
          change u < n + gates.length at hu
          omega
        let q' : Fin gates.length := ⟨u-n, hul⟩
        have hm : gates.get q' ∈ gates := List.get_mem _ _
        rcases (hG _ hm).1 with ha | ho' | hn'
        · exact Or.inl ha
        · exact Or.inr ho'
        · have he := congrArg Fin.val (not_unique gates hnot q' q hn' hq)
          change u-n = w-n at he
          omega
      have hread (t : ℕ) :
          (if t < w then value C (X ∅) t else false) = true →
          (if t < w then value C (X Finset.univ) t else false) = true := by
        by_cases ht : t < w
        · simp only [if_pos ht]
          apply pre_mono C w hpre _ _ _ t ht
          intro v _
          simp [X]
        · simp [ht]
      have h0 : value C (X ∅) w = false := by
        cases h : value C (X ∅) w
        · rfl
        · exact False.elim (hv0 h)
      have h1 : value C (X Finset.univ) w = true := hv1
      rw [hval, hg] at h0 h1
      cases hins : g.inputs with
      | nil => simp [hins, GateOp.eval] at h0
      | cons t ts =>
        simp only [hins, GateOp.eval, List.map_cons, List.headD_cons, Bool.not_eq_false] at h0
        simp only [hins, GateOp.eval, List.map_cons, List.headD_cons, Bool.not_eq_true] at h1
        have h := hread t h0
        rw [h1] at h
        contradiction
    have hop' : g.op = GateOp.and ∨ g.op = GateOp.or := by
      rcases hop with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (hnotop h)
    cases hins : g.inputs with
    | nil =>
      rcases hop' with hg | hg
      · exact False.elim (htrue (fun x => by
          change value C (X x) w = true
          rw [hval, hg, hins]
          rfl))
      · exact False.elim (hfalse (fun x => by
          change ¬ value C (X x) w = true
          rw [hval, hg, hins]
          decide))
    | cons t ts =>
      cases ts with
      | nil =>
        have hc (x : Finset (Fin n)) :
            value C (X x) w = if t < w then value C (X x) t else false := by
          rcases hop' with hg | hg <;> simp [hval, hg, hins, GateOp.eval]
        by_cases ht : t < w
        · exact False.elim (hcopy t ht (fun x => by
            change value C (X x) w = true ↔ value C (X x) t = true
            rw [hc, if_pos ht]))
        · exact False.elim (hfalse (fun x => by
            change ¬ value C (X x) w = true
            rw [hc, if_neg ht]
            decide))
      | cons u us =>
        have hus : us = [] := by
          simpa [hins] using hlen
        subst us
        by_cases ht : t < w <;> by_cases hu : u < w
        · rcases hop' with hg | hg
          · refine ⟨t, u, true, ht, hu, ?_, by simp⟩
            intro _ x
            change value C (X x) w = true ↔
              value C (X x) t = true ∧ value C (X x) u = true
            simp [hval, hg, hins, ht, hu, GateOp.eval, Bool.and_eq_true]
          · refine ⟨t, u, false, ht, hu, by simp, ?_⟩
            intro _ x
            change value C (X x) w = true ↔
              value C (X x) t = true ∨ value C (X x) u = true
            simp [hval, hg, hins, ht, hu, GateOp.eval, Bool.or_eq_true]
        · rcases hop' with hg | hg
          · exact False.elim (hfalse (fun x => by
              change ¬ value C (X x) w = true
              simp [hval, hg, hins, ht, hu, GateOp.eval]))
          · exact False.elim (hcopy t ht (fun x => by
              change value C (X x) w = true ↔ value C (X x) t = true
              simp [hval, hg, hins, ht, hu, GateOp.eval]))
        · rcases hop' with hg | hg
          · exact False.elim (hfalse (fun x => by
              change ¬ value C (X x) w = true
              simp [hval, hg, hins, ht, hu, GateOp.eval]))
          · exact False.elim (hcopy u hu (fun x => by
              change value C (X x) w = true ↔ value C (X x) u = true
              simp [hval, hg, hins, ht, hu, GateOp.eval]))
        · exact False.elim (hfalse (fun x => by
            change ¬ value C (X x) w = true
            rcases hop' with hg | hg <;>
              simp [hval, hg, hins, ht, hu, GateOp.eval]))
  choose a b k hab using hshape
  refine ⟨o, a, b, k, hinput, ?_, fun i => ⟨(hab i).1, (hab i).2.1⟩,
    ho, hearly, fun i => (hab i).2.2.1, fun i => (hab i).2.2.2⟩
  intro i
  exact hob i
