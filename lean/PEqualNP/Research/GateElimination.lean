import PEqualNP.Defs.CircuitLowerBounds

namespace PEqualNP.Research.GateElimination
open PEqualNP.CircuitLowerBounds

def readers (g : Gate) : List Nat :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem effective_eval (g : Gate) (w : List Bool) :
    g.op.eval (g.inputs.map fun i => w.getD i false) =
    g.op.eval ((readers g).map fun i => w.getD i false) := by
  rcases g with ⟨op, ins⟩
  cases op <;> try rfl
  cases ins <;> rfl

def AgreeExcept (a b : List Bool) (u : Nat) : Prop :=
  a.length = b.length ∧ ∀ i, i ≠ u → a.getD i false = b.getD i false

theorem agree_append (a b : List Bool) (u : Nat) (h : AgreeExcept a b u)
    (c : Bool) : AgreeExcept (a ++ [c]) (b ++ [c]) u := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  by_cases hl : i < a.length
  · have hr : i < b.length := h.1 ▸ hl
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hl, List.getElem?_append_left hr]
    exact h.2 i hi
  · have ha : a.length ≤ i := by omega
    have hb : b.length ≤ i := by have := h.1; omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right ha, List.getElem?_append_right hb, h.1]

theorem agree_step (a b : List Bool) (u : Nat) (h : AgreeExcept a b u)
    (g : Gate) (hg : u ∉ readers g) : AgreeExcept (step a g) (step b g) u := by
  unfold step
  have heq : g.op.eval (g.inputs.map fun i => a.getD i false) =
      g.op.eval (g.inputs.map fun i => b.getD i false) := by
    rw [effective_eval, effective_eval]
    congr 1
    exact List.map_congr_left (fun i hi => h.2 i (fun e => hg (e ▸ hi)))
  rw [heq]
  exact agree_append a b u h _

theorem agree_fold (gs : List Gate) (a b : List Bool) (u : Nat)
    (h : AgreeExcept a b u) (hn : ∀ g ∈ gs, u ∉ readers g) :
    AgreeExcept (gs.foldl step a) (gs.foldl step b) u := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    apply ih _ _ (agree_step a b u h g (hn g (by simp)))
    intro g' hg'
    exact hn g' (by simp [hg'])

theorem masked_bypass (g : Gate) (gs : List Gate) (a b : List Bool) (u o : Nat)
    (h : AgreeExcept a b u)
    (hm : g.op.eval (g.inputs.map fun i => a.getD i false) =
          g.op.eval (g.inputs.map fun i => b.getD i false))
    (ho : o ≠ u)
    (hd : (Circuit.mk (g :: gs) o).eval a ≠ (Circuit.mk (g :: gs) o).eval b) :
    ∃ q ∈ gs, u ∈ readers q := by
  classical
  apply Classical.byContradiction
  intro hn
  have hstep : AgreeExcept (step a g) (step b g) u := by
    unfold step
    rw [hm]
    exact agree_append a b u h _
  have htail : ∀ q ∈ gs, u ∉ readers q := by
    intro q hq hu
    exact hn ⟨q,hq,hu⟩
  apply hd
  exact (agree_fold gs _ _ u hstep htail).2 o ho

theorem comparable_absorption (a b : Bool) (h : a = true → b = true) :
    GateOp.and.eval [a,b] = a ∧ GateOp.or.eval [a,b] = b := by
  cases a <;> cases b <;> simp_all [GateOp.eval]

theorem complement_absorption (a : Bool) :
    GateOp.and.eval [a,!a] = false ∧ GateOp.or.eval [a,!a] = true := by
  cases a <;> decide

end PEqualNP.Research.GateElimination
